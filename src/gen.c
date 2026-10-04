#include "gen_int.h"


FILE *outf;
FILE *fb, *ab, *db, *xb; /* fn body, allocs, data, extra fns */

int tmpc, lblc, term, strc;
Inl *inl;
Vec defers;
Loop *loops;
Type *fret;
char *fsret;
Vec queue;
FILE *devnull;
int in_typeof;
Loop *typeof_outer;
int dbg_on = -1, dbg_line;
char *dbg_file;
void **pm_k;
char **pm_v;
int pm_cap, pm_n;
int datac;
int discarding;

/* ---------- runtime support emitted once ---------- */
Vec tagfns; /* Type* enums with tagName helper */
Node *collect_node;

/* ---------- dispatcher ---------- */

/* ---------- inline asm: only `syscall` is supported (via libc syscall(), errno -> -errno) ---------- */
int sys_helper_done;

/* general inline asm: each site becomes a stub function in the side file <out>.asm.s.
   The stub gets a buffer pointer (rdi) holding 8-byte slots [inputs..., outputs...]; it saves callee-saved
   registers, loads inputs into their constraint registers, runs the template, and stores outputs back. */
FILE *asm_out;
int asm_n;
const char *areg[16][4] = {
    {"rax", "eax", "ax", "al"},      {"rbx", "ebx", "bx", "bl"},      {"rcx", "ecx", "cx", "cl"},
    {"rdx", "edx", "dx", "dl"},      {"rsi", "esi", "si", "sil"},     {"rdi", "edi", "di", "dil"},
    {"rbp", "ebp", "bp", "bpl"},     {"r8", "r8d", "r8w", "r8b"},     {"r9", "r9d", "r9w", "r9b"},
    {"r10", "r10d", "r10w", "r10b"}, {"r11", "r11d", "r11w", "r11b"}, {"r12", "r12d", "r12w", "r12b"},
    {"r13", "r13d", "r13w", "r13b"}, {"r14", "r14d", "r14w", "r14b"}, {"r15", "r15d", "r15w", "r15b"},
    {"rsp", "esp", "sp", "spl"}};

Node *gen_cur;
Node *gen_cur_pub(void) {
  return gen_cur;
}
Val gen(Node *n, Scope *s, Type *ex) {
  CVal c;
  if (n->tok) gen_cur = n;
  switch (n->k) {
  case N_INT:
  case N_CHAR:
  case N_TRUE:
  case N_FALSE:
  case N_NULL:
  case N_UNDEF:
  case N_ENUMLIT:
  case N_ERRVAL:
  case N_STR:
  case N_TPTR:
  case N_TARRAY:
  case N_TOPT:
  case N_TERRU:
  case N_TFN:
  case N_CONTAINER:
  case N_ERRSET:
    if (!ceval(n, s, &c)) die("%s:%d: bad constant", n->tok->file, n->tok->line);
    return CK(c);
  case N_IDENT: {
    if (!strcmp(n->s, "_")) return VOIDV();
    Type *pt = n->tok && n->tok->k == TK_ID && n->tok->ival ? NULL : prim_type(n->s);
    if (pt) {
      c.k = CV_TYPE;
      c.t = pt;
      return CK(c);
    }
    Sym *y;
    Decl *d;
    if (!lookup(s, n->s, &y, &d)) die("%s:%d: use of undeclared identifier '%s'", n->tok->file, n->tok->line, n->s);
    if (y) {
      if (y->k == S_CVAL) {
        Val r = CK(y->cv);
        if (y->t && r.ck) r.t = y->t;
        return r;
      }
      if (!y->addr && in_typeof && y->t) return V(y->t, "0");
      if (!y->addr) die("%s:%d: '%s' is not available here", n->tok->file, n->tok->line, n->s);
      return LV(y->t, y->addr);
    }
    resolve_decl(d);
    if (d->kind == D_VAR) return LV(d->t, fmt("$%s", d->sym));
    {
      Val r = CK(d->cv);
      if (d->t && r.ck) r.t = d->t;
      return r;
    }
  }
  case N_FIELD: {
    if (ceval(n, s, &c)) return CK(c);
    Val b = gen(n->a, s, NULL);
    Val r = gen_member(b, n->s, n);
    if (!r.ck && r.t && (r.t->k == TY_NULL || r.t->k == TY_VOID))
      return CK(r.t->k == TY_NULL ? cv_null_pub() : (CVal){.k = CV_VOID, .t = t_void});
    return r;
  }
  case N_DEREF: {
    Val v = rv(gen(n->a, s, NULL));
    if (v.t->k == TY_ARRAY) return v; /* `(a ++ b).*`: zb's runtime ++ yields the array value itself */
    if (v.t->k == TY_SLICE) {
      CVal sc;
      if (!ceval(n->a, s, &sc) || sc.k != CV_SLICE)
        die("%s:%d: slice deref needs a comptime-known length", n->tok->file, n->tok->line);
      return LV(array_of(v.t->elem, sc.slen, 0, 0), load(t_u64, addr_of(v)));
    }
    Val r = LV(v.t->elem, opnd(v));
    if (v.t->k == TY_PTR && v.t->len > 0) {
      r.bf = 1;
      r.hbytes = (int)v.t->len;
      r.bitoff = (int)v.t->sent;
    }
    return r;
  }
  case N_UNWRAP: {
    Val v = gen(n->a, s, NULL);
    if (v.ck && v.cv.k == CV_NULL) {
      if (!term) emit("hlt");
      term = 1;
      return NORET();
    }
    if (v.ck && v.t->k != TY_OPT) return v;
    if (v.t->k != TY_OPT) die("%s:%d: .? on non-optional %s", n->tok->file, n->tok->line, tname(v.t));
    return opt_payload(v, NULL);
  }
  case N_INDEX: {
    if (ceval(n, s, &c)) return CK(c);
    Val b = gen(n->a, s, NULL);
    Val i = gen(n->b, s, t_usize);
    return gen_index(b, i);
  }
  case N_SLICE: return gen_slice(n, s);
  case N_CALL: return gen_call(n, s, ex);
  case N_BUILTIN: return gen_builtin(n, s, ex);
  case N_INIT:
    if (ex && is_tuple_type(ex) && (layout(ex->ct), 1)) {
      int any = 0;
      for (int i = 0; i < ex->ct->fields.n; i++)
        if (((Field *)ex->ct->fields.a[i])->t->k == TY_ANYTYPE) any = 1;
      if (any) return gen_init(n, s, ex);
    }
    if (ceval_ex(n, s, ex, &c)) {
      Val r = CK(c);
      if (ex && ck_ok(&c, ex)) r.t = ex;
      return r;
    }
    return gen_init(n, s, ex);
  case N_UN: {
    const char *op = n->s;
    if (!strcmp(op, "&")) {
      Node *a = n->a;
      if (a->k == N_INIT && !a->a && ex &&
          (ex->k == TY_SLICE || ex->k == TY_MPTR || (ex->k == TY_PTR && ex->elem->k == TY_ARRAY))) {
        Type *et = ex->k == TY_PTR ? ex->elem->elem : ex->elem;
        Type *at = array_of(et, a->list.n, 0, 0);
        Val v = gen_init(a, s, at);
        return V(ptr_to(at, 1), addr_of(v));
      }
      Val v;
      if (a->k == N_ENUMLIT && ex && ex->k == TY_PTR && ex->elem->ct &&
          (ex->elem->k == TY_STRUCT || ex->elem->k == TY_UNION) && find_decl(ex->elem->ct, a->s)) {
        CVal tv = {0};
        tv.k = CV_TYPE;
        tv.t = ex->elem;
        v = gen_member(CK(tv), a->s, a); /* &.decl_literal */
      } else
        v = gen(a, s, ex && ex->k == TY_PTR ? ex->elem : NULL);
      if (v.ck && v.cv.k == CV_FN) {
        FnInst *fi = plain_inst(v.cv.fn);
        return V(ptr_to(fn_type(&fi->ptypes, fi->ret, 0), 1), fmt("$%s", fi->sym));
      }
      if (v.lv && v.bf) return V(bitptr_to(v.t, 0, v.hbytes, v.bitoff), v.op);
      if (v.lv) return V(ptr_to(v.t, 0), v.op);
      if (v.ck && v.cv.k == CV_STR) return V(v.t, mat(v));
      if (v.ck && v.cv.k == CV_AGG && is_tuple_type(v.t) && ex &&
          (ex->k == TY_SLICE || ex->k == TY_MPTR || (ex->k == TY_PTR && ex->elem->k == TY_ARRAY))) {
        layout(v.t->ct);
        Type *at = ex->k == TY_PTR ? ex->elem : array_of(ex->elem, v.t->ct->fields.n, ex->hassent, ex->sent);
        if (at->elem->k != TY_ANYTYPE) v = coerce(v, at);
      }
      if (is_aggr(v.t)) return V(ptr_to(v.t, 1), addr_of(v));
      if (v.t->k == TY_CINT)
        v = coerce(v, t_i64);
      else if (v.t->k == TY_CFLOAT)
        v = coerce(v, t_f64);
      char *sl = slot(v.t);
      put(v, v.t, sl);
      return V(ptr_to(v.t, 1), sl);
    }
    Val v = rv(gen(n->a, s, ex));
    if (is_vec(v.t)) return vec_un(op, v);
    if (!strcmp(op, "!")) {
      v = coerce(v, t_bool);
      if (v.ck) {
        v.cv.i = !v.cv.i;
        return v;
      }
      char *r = tmp();
      emit("%s =w ceqw %s, 0", r, opnd(v));
      return V(t_bool, r);
    }
    if (v.ck && v.cv.k == CV_FLOAT) {
      v.cv.f = -v.cv.f;
      return v;
    }
    if (v.ck && v.cv.k == CV_INT) {
      if (op[0] == '~') {
        if (ex && v.t->k == TY_CINT) v = coerce(v, ex);
        v.cv.i = wrap_int(~v.cv.i, v.t);
      } else
        v.cv.i = wrap_int(-v.cv.i, v.t);
      return v;
    }
    if (is_wide(v.t)) {
      if (op[0] == '~') {
        char *a = tmp(), *b2 = tmp();
        emit("%s =l xor %s, -1", a, wlo(v));
        emit("%s =l xor %s, -1", b2, whi(v));
        return w_from_parts(v.t, a, b2);
      }
      CVal z = {0};
      z.k = CV_INT;
      z.t = v.t;
      return w_arith("-", v.t, CK(z), v);
    }
    if (is_bigf(v.t)) return V(v.t, bigf_op(8, v.t, opnd(v), NULL));
    char *r = tmp();
    if (op[0] == '~') {
      emit("%s =%c xor %s, -1", r, qc(v.t), opnd(v));
      return V(v.t, norm(r, v.t));
    }
    emit("%s =%c neg %s", r, qc(v.t), opnd(v));
    return V(v.t, norm(r, v.t));
  }
  case N_BIN: {
    const char *op = n->s;
    if (!strcmp(op, "and") || !strcmp(op, "or")) return gen_logic(n, s);
    if (ceval(n, s, &c)) return CK(c);
    if (!strcmp(op, "||")) {
      die("%s:%d: runtime ||", n->tok->file, n->tok->line);
    }
    if (!strcmp(op, "**")) { /* runtime repetition of a tuple / array */
      CVal cn;
      if (!ceval(n->b, s, &cn) || cn.k != CV_INT)
        die("%s:%d: ** count must be comptime-known", n->tok->file, n->tok->line);
      int64_t cnt = (int64_t)cn.i;
      Val a = rv(gen(n->a, s, NULL));
      Type *t = a.t;
      if (is_tuple_type(t)) {
        layout(t->ct);
        int m = t->ct->fields.n;
        Vec names = {0}, types = {0};
        int nct = 0;
        CVal **cts = xalloc(sizeof(CVal *) * (m * cnt + 1));
        for (int64_t r = 0; r < cnt; r++)
          for (int i = 0; i < m; i++) {
            Field *f = t->ct->fields.a[i];
            int j = names.n;
            if (f->is_ct) {
              cts[j] = f->defcv;
              nct++;
            }
            vpush(&types, f->t);
            vpush(&names, fmt("%d", j));
          }
        Type *rt = nct ? mk_anon_struct_cv(&names, &types, 1, cts) : mk_anon_struct(&names, &types, 1);
        char *sl = slot(rt);
        for (int64_t r = 0; r < cnt; r++)
          for (int i = 0; i < m; i++) {
            Field *f = t->ct->fields.a[i], *g = rt->ct->fields.a[r * m + i];
            if (g->is_ct) continue;
            blit(addp(addr_of(a), f->off), addp(sl, g->off), (int)tsize(f->t));
          }
        return V(rt, sl);
      }
      Type *at = t->k == TY_PTR ? t->elem : t;
      if (at->k != TY_ARRAY) die("%s:%d: runtime ** needs an array or tuple operand", n->tok->file, n->tok->line);
      char *src = t->k == TY_PTR ? opnd(a) : addr_of(a);
      int64_t bytes = tsize(at);
      Type *rt = array_of(at->elem, at->len * cnt, 0, 0);
      char *sl = slot(rt);
      for (int64_t r = 0; r < cnt; r++) blit(src, addp(sl, r * bytes), (int)bytes);
      return V(rt, sl);
    }
    if (!strcmp(op, "++")) {
      Val a = rv(gen(n->a, s, NULL)), b = rv(gen(n->b, s, NULL));
      Type *et = NULL;
      Val *vs[2] = {&a, &b};
      int64_t ln[2];
      for (int k = 0; k < 2; k++) {
        Type *t = vs[k]->t;
        if (t->k == TY_ARRAY)
          et = t->elem;
        else if (t->k == TY_PTR && t->elem->k == TY_ARRAY)
          et = t->elem->elem;
      }
      if (!et && is_tuple_type(a.t) && is_tuple_type(b.t)) { /* runtime tuple concatenation */
        Vec names = {0}, types = {0}, vals = {0};
        layout(a.t->ct);
        layout(b.t->ct);
        int tot = a.t->ct->fields.n + b.t->ct->fields.n, nct = 0;
        CVal **cts = xalloc(sizeof(CVal *) * (tot + 1));
        for (int k = 0; k < 2; k++) {
          Container *c = vs[k]->t->ct;
          for (int i = 0; i < c->fields.n; i++) {
            Field *f = c->fields.a[i];
            Val fv = rv(gen_member(*vs[k], f->name, n));
            int j = names.n;
            if (fv.ck && (fv.cv.k == CV_ENUMLIT || fv.cv.k == CV_TYPE)) {
              cts[j] = xalloc(sizeof(CVal));
              *cts[j] = fv.cv;
              nct++;
            }
            Val *pv = xalloc(sizeof *pv);
            *pv = fv;
            vpush(&vals, pv);
            vpush(&types, f->t);
            vpush(&names, fmt("%d", j));
          }
        }
        Type *t = nct ? mk_anon_struct_cv(&names, &types, 1, cts) : mk_anon_struct(&names, &types, 1);
        char *sl = slot(t);
        for (int i = 0; i < vals.n; i++) {
          Field *f = t->ct->fields.a[i];
          if (f->is_ct) continue;
          put(*(Val *)vals.a[i], f->t, addp(sl, f->off));
        }
        return V(t, sl);
      }
      if (!et) die("%s:%d: runtime ++ needs array operands", n->tok->file, n->tok->line);
      char *src[2];
      for (int k = 0; k < 2; k++) {
        Type *t = vs[k]->t;
        if (t->k == TY_PTR && t->elem->k == TY_ARRAY) {
          ln[k] = t->elem->len;
          src[k] = opnd(*vs[k]);
        } else if (t->k == TY_ARRAY) {
          ln[k] = t->len;
          src[k] = addr_of(*vs[k]);
        } else {
          int64_t m = t->ct ? (layout(t->ct), t->ct->fields.n) : 0;
          Val c2 = coerce(*vs[k], array_of(et, m, 0, 0));
          ln[k] = m;
          src[k] = addr_of(c2);
        }
      }
      Type *rt = array_of(et, ln[0] + ln[1], 0, 0);
      char *sl = slot(rt);
      blit(src[0], sl, (int)(ln[0] * tsize(et)));
      blit(src[1], addp(sl, ln[0] * tsize(et)), (int)(ln[1] * tsize(et)));
      return V(rt, sl);
    }
    int cmp = !strcmp(op, "==") || !strcmp(op, "!=") || !strcmp(op, "<") || !strcmp(op, ">") || !strcmp(op, "<=") ||
              !strcmp(op, ">=");
    if (ex && (ex->k == TY_OPT || ex->k == TY_ERRU) && !cmp) ex = ex->elem;
    Val a = rv(gen(n->a, s, cmp ? NULL : ex));
    Type *bh = cmp ? (a.t->k == TY_CINT || a.t->k == TY_ENUMLIT ? NULL : a.t)
                   : (a.t->k == TY_CINT ? ex : (a.t->k == TY_MPTR ? t_usize : a.t));
    if (bh && !cmp && (n->b->k == N_SWITCH || n->b->k == N_IF) && !in_typeof) {
      Type *bt = typeof_impl(n->b, s);
      if (bt && (bt->k == TY_INT || bt->k == TY_FLOAT) && bt != bh) bh = NULL;
    }
    if (bh && bh->k == TY_ARRAY && bh->isconst != 2)
      bh = NULL; /* array operand: the other side may be a vector (peer) */
    Val b = rv(gen(n->b, s, bh));
    if (a.t->k == TY_ARRAY && b.t->k == TY_ARRAY && a.t->len == b.t->len &&
        (a.t->isconst == 2) != (b.t->isconst == 2)) { /* array op vector: peer type is the vector */
      if (a.t->isconst == 2)
        b = coerce(b, a.t);
      else
        a = coerce(a, b.t);
    }
    if (a.ck && a.t->k == TY_CINT && b.t->k == TY_CINT && !b.ck) a = coerce(a, t_i64);
    if (cmp && !a.ck && a.t->k == TY_INT && b.ck && b.cv.k == CV_INT) {
      CVal raw;
      if (ceval(n->b, s, &raw) && raw.k == CV_INT && cv_typeof(&raw)->k == TY_CINT) b = CK(raw);
    }
    if (cmp) return gen_cmp(op, a, b);
    if (a.t->k == TY_CINT && b.t->k == TY_CINT && ex && ex->k == TY_INT) {
      a = coerce(a, ex);
      b = coerce(b, ex);
    }
    return gen_arith(op, a, b);
  }
  case N_ASSIGN: gen_assign(n, s); return VOIDV();
  case N_DESTRUCT: gen_destruct(n, s); return VOIDV();
  case N_UNREACHABLE:
    emit("hlt");
    term = 1;
    return NORET();
  case N_TRY: return gen_try(n, s, ex);
  case N_CATCH: return gen_catch(n, s, ex);
  case N_ORELSE: return gen_orelse(n, s, ex);
  case N_IF: {
    CVal cc;
    if (!n->cap && ceval(n->a, s, &cc) && cc.k == CV_BOOL) return gen_if(n, s, ex);
    if (n->cap && !n->capref && ceval(n->a, s, &cc) && cc.k != CV_UNDEF) {
      Scope *bs = new_scope(s, NULL);
      if (cc.k == CV_NULL) return n->c ? gen(n->c, s, ex) : VOIDV();
      if (cc.k == CV_ERR) {
        if (n->cap2) bind_cval(bs, n->cap2, cc);
        return n->c ? gen(n->c, bs, ex) : VOIDV();
      }
      bind_cval(bs, n->cap, cc);
      return gen(n->b, bs, ex);
    }
    if (!n->cap && n->cap2) {
      Val cv = gen(n->a, s, NULL);
      if (cv.t->k == TY_ERRU) return gen_if_erru(n, s, ex, cv);
    }
    if (n->cap) {
      Val cv = gen(n->a, s, NULL);
      if (cv.t->k == TY_ERRU) return gen_if_erru(n, s, ex, cv);
      /* optional: re-dispatch with the already evaluated condition */
      Res R;
      memset(&R, 0, sizeof R);
      R.ex = ex;
      char *lt = newl(), *lf = newl(), *lx = newl();
      if_peer(&R, n, s, ex);
      Scope *ts = new_scope(s, NULL);
      char *pv = opt_is_ptr(cv.t) ? opnd(cv) : NULL;
      if (cv.t->k != TY_OPT) die("%s:%d: if capture needs optional or error union", n->tok->file, n->tok->line);
      if (cv.t->elem->k == TY_NORET) {
        if (n->c) return gen(n->c, s, ex);
        return VOIDV();
      } /* ?noreturn is always null */
      if (pv) {
        char *h = tmp();
        emit("%s =w cnel %s, 0", h, pv);
        br(h, lt, lf);
      } else
        br(opt_has(cv), lt, lf);
      label(lt);
      cap_bind(ts, n->cap, n->capref, opt_payload(cv, pv));
      {
        Val tv = gen(n->b, ts, n->c ? ex : NULL);
        res_put(&R, n->c || tv.t->k == TY_NORET ? tv : VOIDV());
      }
      jmp(lx);
      label(lf);
      if (n->c)
        res_put(&R, gen(n->c, s, ex ? ex : R.collect ? NULL : R.t));
      else
        res_put(&R, VOIDV());
      jmp(lx);
      label(lx);
      return res_get(&R);
    }
    return gen_if(n, s, ex);
  }
  case N_WHILE:
    if (n->flags & F_INLINE) return gen_inline_while(n, s, ex);
    return gen_while(n, s, ex);
  case N_FOR:
    if (n->flags & F_INLINE) return gen_inline_for(n, s, ex);
    return gen_for(n, s, ex);
  case N_SWITCH: return gen_switch(n, s, ex);
  case N_BLOCK: return gen_block(n, s, ex);
  case N_BREAK: {
    Loop *L = find_loop(n->label, 0);
    if (in_typeof) {
      int outer = 0;
      for (Loop *p = typeof_outer; p; p = p->up)
        if (p == L) outer = 1;
      if (outer) {
        if (n->a) {
          Val v = gen(n->a, s, L->res->ex ? L->res->ex : L->res->t);
          if (v.t->k == TY_NORET) return v;
        }
        jmp(L->brk);
        return NORET();
      }
    }
    if (n->a) {
      Type *bx = L->res->ex ? L->res->ex : (L->res->collect || type_incomplete(L->res->t)) ? NULL : L->res->t;
      Val v = gen(n->a, s, bx);
      if (v.t->k == TY_NORET) return v;
      res_put(L->res, v);
    } else if (L->res)
      res_put(L->res, VOIDV());
    L->brk_used = 1;
    run_defers(L->dbase, NULL);
    jmp(L->brk);
    return NORET();
  }
  case N_CONTINUE: {
    Loop *L = n->label ? find_loop(n->label, 1) : find_loop(NULL, 1);
    if (L->kind == 2) {
      Val v = coerce(gen(n->a, s, L->swt), L->swt);
      put(v, L->swt, L->swslot);
      run_defers(L->dbase, NULL);
      jmp(L->swdisp);
      return NORET();
    }
    L->cont_used = 1;
    run_defers(L->dbase, NULL);
    jmp(L->cont);
    return NORET();
  }
  case N_RETURN: return gen_return(n, s);
  case N_VAR: gen_vardecl(n, s); return VOIDV();
  case N_DEFER:
  case N_ERRDEFER: {
    Defer *d = xalloc(sizeof *d);
    d->n = n->a;
    d->err = n->k == N_ERRDEFER;
    d->s = s;
    d->cap = n->cap;
    vpush(&defers, d);
    return VOIDV();
  }
  case N_COMPTIME:
    if (n->a->k == N_UNREACHABLE) {
      if (!term) emit("hlt");
      term = 1;
      return NORET();
    }
    {
      int returned = 0;
      if (!ceval_ret(n->a, s, ex, fret, &c, &returned)) {
        /* lenient: valid Zig guarantees this is comptime-known; zb may lose comptime-ness (e.g. destructured
           comptime tuple fields), so evaluate plain calls/asserts at runtime instead */
        if (n->a->k == N_CALL || n->a->k == N_BUILTIN) {
          if (getenv("ZB_DBG"))
            fprintf(stderr, "zb: note: %s:%d: comptime expression evaluated at runtime\n", n->tok->file, n->tok->line);
          return gen(n->a, s, ex);
        }
        die("%s:%d: unable to evaluate comptime expression (at %s)", n->tok->file, n->tok->line, ct_fail_loc());
      }
      if (returned) return ret_val(CK(c), c.k == CV_VOID);
    }
    {
      Val r = CK(c);
      if (ex && ck_ok(&c, ex)) r.t = ex;
      return r;
    }
  case N_FLOAT: {
    CVal fc = cv_float(n->fval, t_cfloat);
    Val fv = CK(fc);
    return ex && (is_float(ex) || (ex->k == TY_OPT && is_float(ex->elem))) ? coerce(fv, ex) : fv;
  }
  case N_ASM: return gen_asm(n, s);
  case N_FN: return VOIDV();
  default: die("%s:%d: cannot generate node kind %d", n->tok->file, n->tok->line, n->k);
  }
}

/* ---------- typeof via dry run ---------- */
Type *typeof_ex(Node *n, Scope *s, Type *ex) {
  FILE *sfb = fb, *sab = ab;
  int st = term;
  Loop *sl = loops;
  int sdn = defers.n;
  if (!devnull) devnull = fopen("/dev/null", "w");
  Loop *sto = typeof_outer;
  typeof_outer = loops;
  in_typeof++;
  fb = ab = devnull;
  Val v = gen(n, s, ex);
  fb = sfb;
  ab = sab;
  term = st;
  loops = sl;
  defers.n = sdn;
  in_typeof--;
  typeof_outer = sto;
  return v.t;
}
Type *typeof_impl(Node *n, Scope *s) {
  FILE *sfb = fb, *sab = ab;
  int st = term;
  Loop *sl = loops;
  int sdn = defers.n;
  if (!devnull) devnull = fopen("/dev/null", "w");
  Loop *sto = typeof_outer;
  typeof_outer = loops;
  in_typeof++;
  fb = ab = devnull;
  Val v = gen(n, s, NULL);
  fb = sfb;
  ab = sab;
  term = st;
  loops = sl;
  defers.n = sdn;
  in_typeof--;
  typeof_outer = sto;
  return v.t;
}

/* ---------- globals ---------- */
void gen_global(Decl *d) {
  Node *n = d->node;
  if (n->flags & F_EXTERN) return;
  CVal v = d->has_init ? d->cv : (CVal){.k = CV_UNDEF};
  char *buf;
  size_t bsz;
  FILE *f = open_memstream(&buf, &bsz);
  int first = 1;
  ser(f, &first, &v, d->t);
  if (first) fputs("z 1", f);
  fclose(f);
  int al = talign(d->t);
  if (al < 1) al = 1;
  if (al > 16) al = 16;
  fprintf(db, "%sdata $%s = align %d { %s }\n", (n->flags & F_EXPORT) ? "export " : "", d->sym, al, buf);
  free(buf);
}

/* ---------- functions ---------- */
void queue_fn(FnInst *fi) {
  if (fi->queued || (fi->node->flags & F_EXTERN) || !fi->node->b) return;
  fi->queued = 1;
  vpush(&queue, fi);
}
FnInst *gen_cur_fi;
void gen_fn(FnInst *fi) {
  {
    static int tr = -1;
    if (tr < 0) tr = getenv("ZB_TRACE_FN") != NULL;
    if (tr) {
      static int cnt;
      fprintf(stderr, "genfn %s\n", fi->sym);
#ifdef ZB_GC
      if (++cnt % 2000 == 0) {
        extern size_t GC_get_heap_size(void), GC_get_memory_use(void);
        struct mallinfo2 mi = mallinfo2();
        fprintf(stderr, "mem fns=%d gcheap=%zuM gcuse=%zuM malloc=%zuM queue=%d\n", cnt, GC_get_heap_size() >> 20,
                GC_get_memory_use() >> 20, (mi.uordblks + mi.hblkhd) >> 20, queue.n);
      }
#endif
    }
  }
  gen_cur_fi = fi;
  if (dbg_on < 0) dbg_on = getenv("ZB_DBG") != NULL;
  dbg_line = 0;
  dbg_file = fi->node->tok ? fi->node->tok->file : NULL;
  char *fbuf, *abuf;
  size_t fsz, asz;
  fb = open_memstream(&fbuf, &fsz);
  ab = open_memstream(&abuf, &asz);
  term = 0;
  defers.n = 0;
  loops = NULL;
  fret = fi->ret;
  fsret = NULL;
  Node *f = fi->node;
  Scope *fs = new_scope(fi->scope, NULL);
  char params[4096];
  int m = 0;
  params[0] = 0;
  if (is_aggr(fret)) {
    fsret = "%sret";
    m += snprintf(params + m, sizeof params - m, "l %%sret");
  }
  for (int i = 0; i < f->list.n; i++) {
    Node *p = f->list.a[i];
    Type *t = fi->ptypes.a[i];
    if (p->flags & F_VARARGS) {
      m += snprintf(params + m, sizeof params - m, "%s...", m ? ", " : "");
      continue;
    }
    if (!t) continue;
    char *pn = fmt("%%p%d", i);
    if (tsize(t) == 0) {
      if (p->s) bind_local(fs, p->s, t, "0");
      continue;
    }
    m += snprintf(params + m, sizeof params - m, "%s%c %s", m ? ", " : "", qc(t), pn);
    if (!p->s) continue;
    if (is_aggr(t))
      bind_local(fs, p->s, t, pn);
    else {
      char *sl = slot(t);
      store(t, pn, sl);
      bind_local(fs, p->s, t, sl);
    }
  }
  gen_block(f->b, fs, NULL);
  if (!term) {
    if (fret->k == TY_ERRU) {
      store(t_u16, "0", fsret);
      emit("ret");
    } else if (fret->k == TY_VOID || is_aggr(fret) || tsize(fret) == 0)
      emit("ret");
    else
      emit("hlt");
  }
  fclose(fb);
  fclose(ab);
  char rc = (fret->k == TY_VOID || fret->k == TY_NORET || is_aggr(fret) || tsize(fret) == 0) ? 0 : qc(fret);
  if (dbg_on && dbg_file) {
    char *rp = realpath(dbg_file, NULL);
    fprintf(outf, "dbgfile \"%s\"\n", rp ? rp : dbg_file);
    free(rp);
  }
  fprintf(outf, "%sfunction %s%c $%s(%s) {\n@start\n%s%s}\n\n",
          ((f->flags & F_EXPORT) || fi->exported) ? "export " : "", rc ? "" : "", rc ? rc : ' ', fi->sym, params, abuf,
          fbuf);
  free(fbuf);
  free(abuf);
}
void gen_init_buffers(void) {
  fprintf(outf, "type :zbw = { l, l }\n");
  db = tmpfile();
  xb = tmpfile();
  if (!db || !xb) die("cannot create temp files");
  typeof_hook = typeof_impl;
}
void gen_all(void) {
  for (int i = 0; i < queue.n; i++) {
    FnInst *fi = queue.a[i];
    if (!fi->done) {
      fi->done = 1;
      gen_fn(fi);
    }
  }
}
void gen_main_wrapper(FnInst *mi, int glue) {
  Type *r = mi->ret;
  if (glue) {
    fprintf(outf,
            "export function w $main(w %%argc, l %%argv, l %%envp) {\n@start\n\tstorew %%argc, $zb.argc\n\tstorel "
            "%%argv, $zb.argv\n\t%%a =l extsw %%argc\n\t%%r =w call $%s(l %%a, l %%argv, l %%envp)\n\tret %%r\n}\n",
            mi->sym);
    return;
  }
  fprintf(
      outf,
      "export function w $main(w %%argc, l %%argv) {\n@start\n\tstorew %%argc, $zb.argc\n\tstorel %%argv, $zb.argv\n");
  if (r->k == TY_VOID || r->k == TY_NORET)
    fprintf(outf, "\tcall $%s()\n\tret 0\n}\n", mi->sym);
  else if (r->k == TY_INT)
    fprintf(outf, "\t%%r =w call $%s()\n\tret %%r\n}\n", mi->sym);
  else if (r->k == TY_ERRU) {
    fprintf(outf,
            "\t%%e =l alloc8 %d\n\tcall $%s(l %%e)\n\t%%c =w loaduh %%e\n\tjnz %%c, @err, @ok\n@err\n\tcall "
            "$zb.errexit(w %%c)\n\tret 1\n@ok\n",
            tsize(r) < 8 ? 8 : tsize(r), mi->sym);
    if (r->elem->k == TY_INT)
      fprintf(outf, "\t%%p =l add %%e, %d\n\t%%v =w loadub %%p\n\tret %%v\n}\n", erru_off(r));
    else
      fprintf(outf, "\tret 0\n}\n");
  } else
    die("unsupported main return type %s", tname(r));
}
void gen_finish(void) {
  fprintf(db, "export data $zb.argc = align 4 { w 0 }\nexport data $zb.argv = align 8 { l 0 }\n");
  char **syms = xalloc(sizeof(char *) * (errnames.n + 1));
  for (int i = 0; i < errnames.n; i++) {
    char *s = errnames.a[i];
    syms[i] = strdata(s, strlen(s));
  }
  fprintf(db, "data $zb.errnames = align 8 { l 0, l 0");
  for (int i = 0; i < errnames.n; i++) fprintf(db, ", l %s, l %d", syms[i], (int)strlen((char *)errnames.a[i]));
  fprintf(db, " }\n");
  fprintf(db, "data $zb.pm = { b \"panic: \" }\ndata $zb.em = { b \"error: \" }\ndata $zb.nl = { b 10 }\n");
  fprintf(xb, "function $zb.panic(l %%p, l %%n) {\n@start\n\tcall $write(w 2, l $zb.pm, l 7)\n\tcall $write(w 2, l "
              "%%p, l %%n)\n\tcall $write(w 2, l $zb.nl, l 1)\n\tcall $abort()\n\thlt\n}\n");
  fprintf(xb, "function $zb.errexit(w %%c) {\n@start\n\t%%w =l extuw %%c\n\t%%o =l mul %%w, 16\n\t%%a =l add "
              "$zb.errnames, %%o\n\t%%p =l loadl %%a\n\t%%a2 =l add %%a, 8\n\t%%n =l loadl %%a2\n\tcall $write(w 2, l "
              "$zb.em, l 7)\n\tcall $write(w 2, l %%p, l %%n)\n\tcall $write(w 2, l $zb.nl, l 1)\n\tret\n}\n");
  {
    FILE *fs[2] = {xb, db};
    char buf[65536];
    size_t k;
    for (int i = 0; i < 2; i++) {
      rewind(fs[i]);
      while ((k = fread(buf, 1, sizeof buf, fs[i])) > 0) fwrite(buf, 1, k, outf);
      fclose(fs[i]);
    }
  }
}

void gen_exports(void) {
  for (int i = 0; i < zb_exports.n; i++) {
    ExportReq *er = zb_exports.a[i];
    Decl *d = NULL;
    Node *x = er->node;
    if (x && x->k == N_UN && x->s && !strcmp(x->s, "&")) x = x->a;
    if (x && x->k == N_IDENT)
      for (Scope *sc = er->scope; sc && !d; sc = sc->up)
        if (sc->ct) d = find_decl(sc->ct, x->s);
    if (er->v.k == CV_FN) d = er->v.fn;
    if (!d) die("@export: cannot resolve %s", er->name);
    resolve_decl(d);
    if (d->node->k == N_FN) {
      FnInst *fi = plain_inst(d);
      fi->sym = er->name;
      fi->exported = 1;
    }
  }
}
void eset_resolve(Type *S) {
  Container *c = S->ct;
  if (c->iresolved || c->iresolving) return;
  FnInst *fi = c->infer_fi ? c->infer_fi : plain_inst(c->infer_d);
  if (fi == gen_cur_fi) return; /* still generating: incomplete */
  c->iresolving = 1;
  if (!fi->done) {
    fi->done = 1;
    FILE *sfb = fb, *sab = ab;
    int sterm = term;
    Inl *sinl = inl;
    Vec sdef = defers;
    Loop *sloops = loops;
    Type *sfret = fret;
    char *sfsret = fsret;
    int sit = in_typeof;
    Loop *sto = typeof_outer;
    int sdl = dbg_line;
    char *sdf = dbg_file;
    int sdisc = discarding;
    Node *scn = collect_node, *sgc = gen_cur;
    FnInst *sfi = gen_cur_fi;
    defers = (Vec){0};
    inl = NULL;
    in_typeof = 0;
    typeof_outer = NULL;
    discarding = 0;
    collect_node = NULL;
    gen_fn(fi);
    fb = sfb;
    ab = sab;
    term = sterm;
    inl = sinl;
    defers = sdef;
    loops = sloops;
    fret = sfret;
    fsret = sfsret;
    in_typeof = sit;
    typeof_outer = sto;
    dbg_line = sdl;
    dbg_file = sdf;
    discarding = sdisc;
    collect_node = scn;
    gen_cur = sgc;
    gen_cur_fi = sfi;
  }
  eset_flatten(S);
  c->iresolving = 0;
  c->iresolved = 1;
}
