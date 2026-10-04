#include "gen_int.h"

Val gen_builtin(Node *n, Scope *s, Type *ex) {
  const char *b = n->s;
  Node *x = n->list.n ? n->list.a[0] : NULL, *y = n->list.n > 1 ? n->list.a[1] : NULL;
  CVal c;
  Type *ex0 = ex;
  if (ex && ex->k == TY_ERRU) ex = ex->elem;
  if (ex && ex->k == TY_OPT) {
    static const char *ar[] = {"divTrunc", "divExact", "divFloor", "divCeil", "rem",  "mod", "min",
                               "max",      "shlExact", "shrExact", "abs",     "sqrt", NULL};
    for (int i = 0; ar[i]; i++)
      if (!strcmp(b, ar[i])) {
        ex = ex->elem;
        break;
      }
  } /* numeric result: operands don't get the optional */
  if (!strcmp(b, "backingInt")) {
    Type *at = typeof_impl(x, s);
    if (at->k == TY_ENUM || (at->k == TY_UNION && at->ct->tagged) || at->k == TY_INT || at->k == TY_CINT)
      b = "intFromEnum";
    else {
      b = "bitCast";
      ex = ex0 = int_type(bits_of(at), 0);
    }
  } else if (!strcmp(b, "fromBackingInt")) {
    Type *u = ex && ex->k == TY_OPT ? ex->elem : ex;
    if (!u) die("%s:%d: @fromBackingInt needs a result type", n->tok->file, n->tok->line);
    if (u->ct) layout(u->ct);
    Type *bt = u->k == TY_ENUM ? u->ct->tag : int_type(bits_of(u), 0);
    Val v = coerce(rv(gen(x, s, bt)), bt);
    if (v.ck && u->k == TY_ENUM) {
      CVal r = v.cv;
      r.t = u;
      return CK(r);
    }
    if (u->k == TY_ENUM) return V(u, opnd(v));
    if (!is_aggr(u)) return V(u, opnd(v));
    char *sl = slot(u);
    store(bt, opnd(v), sl);
    return V(u, sl);
  }
  if (!strcmp(b, "divCeil")) {
    Val a = rv(gen(x, s, ex)), d = rv(gen(y, s, ex));
    Type *t = peer(a, d);
    if (t->k == TY_CINT) t = ex ? ex : t_i64;
    a = coerce(a, t);
    d = coerce(d, t);
    if (is_wide(t)) die("%s:%d: @divCeil on wide ints unsupported", n->tok->file, n->tok->line);
    if (is_bigf(t)) return V(t, bigf_op(12, t, bigf_op(3, t, opnd(a), opnd(d)), NULL));
    if (is_float(t)) {
      char c = qc(t), *q = tmp(), *r = tmp();
      emit("%s =%c div %s, %s", q, c, opnd(a), opnd(d));
      emit("%s =%c call $%s(%c %s)", r, c, c == 's' ? "ceilf" : "ceil", c, q);
      return V(t, r);
    }
    char cl = qc(t), *A = opnd(a), *D = opnd(d), *q = tmp(), *r = tmp(), *nz = tmp(), *adj = tmp(), *ext = tmp(),
         *res = tmp();
    emit("%s =%c %s %s, %s", q, cl, t->sign ? "div" : "udiv", A, D);
    emit("%s =%c %s %s, %s", r, cl, t->sign ? "rem" : "urem", A, D);
    emit("%s =w cne%c %s, 0", nz, cl, r);
    if (t->sign) {
      char *x1 = tmp(), *pos = tmp();
      emit("%s =%c xor %s, %s", x1, cl, r, D);
      emit("%s =w csge%c %s, 0", pos, cl, x1);
      emit("%s =w and %s, %s", adj, nz, pos);
    } else
      emit("%s =w copy %s", adj, nz);
    if (cl == 'l')
      emit("%s =l extuw %s", ext, adj);
    else
      emit("%s =w copy %s", ext, adj);
    emit("%s =%c add %s, %s", res, cl, q, ext);
    return V(t, norm(res, t));
  }
  if (!strcmp(b, "call")) {
    Node *fnn = y, *an = n->list.a[2];
    Node *cn = xalloc(sizeof *cn);
    cn->k = N_CALL;
    cn->tok = n->tok;
    cn->a = fnn;
    if (an->k == N_INIT && !an->a && !(an->flags & F_FIELDS)) {
      for (int i = 0; i < an->list.n; i++) vpush(&cn->list, an->list.a[i]);
    } else {
      Type *tt = typeof_impl(an, s);
      if (tt->k == TY_PTR) tt = tt->elem;
      if (!tt->ct) die("%s:%d: @call args must be a tuple", n->tok->file, n->tok->line);
      layout(tt->ct);
      for (int i = 0; i < tt->ct->fields.n; i++) {
        Node *f = xalloc(sizeof *f);
        f->k = N_FIELD;
        f->tok = an->tok;
        f->a = an;
        f->s = fmt("%d", i);
        vpush(&cn->list, f);
      }
    }
    return gen(cn, s, ex0);
  }
  if (!strcmp(b, "errorCast")) {
    Val v = rv(gen(x, s, NULL));
    if (ex0 && (ex0->k == TY_ERRU || ex0->k == TY_ERRSET) && v.t->k == ex0->k) {
      if (v.ck) {
        v.cv.t = ex0;
      }
      v.t = ex0;
    }
    return v;
  }
  if (strcmp(b, "memcpy") && strcmp(b, "memmove") && strncmp(b, "atomic", 6) && strcmp(b, "memset") &&
      strcmp(b, "panic") && strcmp(b, "trap") && ceval_ex(n, s, ex, &c)) {
    Val v = CK(c);
    return ex && v.t->k == TY_CINT && ex->k == TY_INT ? coerce(v, ex) : v;
  }
  if (!strcmp(b, "as")) {
    Type *t = eval_type(x, s);
    return coerce(gen(y, s, t), t);
  }
  if (!strcmp(b, "splat")) {
    if (!ex || !is_vec(ex)) {
      if (ex && ex->k == TY_ARRAY) return vec_splat(gen(x, s, ex->elem), ex);
      die("%s:%d: @splat needs a vector result type", n->tok->file, n->tok->line);
    }
    return vec_splat(gen(x, s, ex->elem), ex);
  }
  if (!strcmp(b, "reduce")) {
    CVal op;
    if (!ceval_ex(x, s, NULL, &op)) die("@reduce op must be comptime");
    const char *on = op.k == CV_ENUMLIT ? op.s : NULL;
    if (!on) {
      Container *rc = ((Type *)op.t)->ct;
      layout(rc);
      for (int i = 0; i < rc->fields.n; i++) {
        Field *f = rc->fields.a[i];
        if (f->val == (int64_t)op.i) on = f->name;
      }
    }
    return vec_reduce(on, rv(gen(y, s, NULL)));
  }
  if (!strcmp(b, "select")) {
    Type *et = eval_type(x, s);
    Val m = rv(gen(y, s, NULL));
    Type *vt = vec_of(et, m.t->len);
    Val a = coerce(rv(gen(n->list.a[2], s, vt)), vt), bb = coerce(rv(gen(n->list.a[3], s, vt)), vt);
    m = V(m.t, addr_of(m));
    a = V(vt, addr_of(a));
    bb = V(vt, addr_of(bb));
    char *sl = slot(vt);
    for (int64_t i = 0; i < vt->len; i++) {
      Val r = sel2(vel(m, i), vel(a, i), vel(bb, i), et);
      put(r, et, addp(sl, i * tsize(et)));
    }
    return V(vt, sl);
  }
  if (!strcmp(b, "shuffle")) {
    Type *et = eval_type(x, s);
    Val a = rv(gen(y, s, NULL)), bb = rv(gen(n->list.a[2], s, NULL));
    CVal mk;
    if (!ceval_force(n->list.a[3], s, &mk)) die("@shuffle mask must be comptime");
    int64_t ml = mk.k == CV_AGG ? mk.n : 0;
    Type *vt = vec_of(et, ml);
    char *sl = slot(vt);
    a = V(a.t, addr_of(a));
    bb = V(bb.t, addr_of(bb));
    for (int64_t i = 0; i < ml; i++) {
      int64_t k = (int64_t)mk.el[i]->i;
      if (mk.el[i]->k == CV_UNDEF) k = 0;
      Val e = k >= 0 ? vel(a, k) : vel(bb, ~k);
      put(e, et, addp(sl, i * tsize(et)));
    }
    return V(vt, sl);
  }
  if (!strcmp(b, "floatFromInt") || !strcmp(b, "intFromFloat") || !strcmp(b, "floatCast")) {
    if (!ex) die("%s:%d: @%s needs a result type", n->tok->file, n->tok->line, b);
    Type *to = ex;
    if (to->k == TY_OPT) to = to->elem;
    if (is_vec(to)) {
      Val v = rv(gen(x, s, NULL));
      Type *vt = v.t;
      char *sl = slot(to);
      v = V(vt, addr_of(v));
      for (int64_t i = 0; i < to->len; i++)
        put(float_conv(vel(v, i), to->elem), to->elem, addp(sl, i * tsize(to->elem)));
      return V(to, sl);
    }
    return float_conv(gen(x, s, NULL), to);
  }
  if (!strcmp(b, "sqrt") || !strcmp(b, "sin") || !strcmp(b, "cos") || !strcmp(b, "tan") || !strcmp(b, "exp") ||
      !strcmp(b, "exp2") || !strcmp(b, "exp10") || !strcmp(b, "log") || !strcmp(b, "log2") || !strcmp(b, "log10") ||
      !strcmp(b, "floor") || !strcmp(b, "ceil") || !strcmp(b, "trunc") || !strcmp(b, "round") ||
      (!strcmp(b, "abs") && 0)) {
    Val v = rv(gen(x, s, ex));
    if (v.t->k == TY_CFLOAT) v = coerce(v, ex && ex->k == TY_FLOAT ? ex : t_f64);
    Type *t = v.t;
    if (is_vec(t)) {
      char *sl = slot(t);
      Val av = V(t, addr_of(v));
      for (int64_t i = 0; i < t->len; i++) {
        char c = qc(t->elem), *r = tmp();
        emit("%s =%c call $%s%s(%c %s)", r, c, b, c == 's' ? "f" : "", c, opnd(vel(av, i)));
        store(t->elem, r, addp(sl, i * tsize(t->elem)));
      }
      return V(t, sl);
    }
    if (is_bigf(t)) {
      static const char *nm[] = {"sqrt", "floor", "ceil", "trunc", "round", "sin",  "cos",
                                 "tan",  "exp",   "exp2", "exp10", "log",   "log2", "log10"};
      for (int k = 0; k < 14; k++)
        if (!strcmp(b, nm[k])) return V(t, bigf_op(10 + k, t, opnd(v), NULL));
    }
    char c = qc(t), *r = tmp();
    emit("%s =%c call $%s%s(%c %s)", r, c, b, c == 's' ? "f" : "", c, opnd(v));
    return V(t, r);
  }
  if (!strcmp(b, "mulAdd")) {
    Type *t = eval_type(x, s);
    Val a1 = coerce(gen(y, s, t), t), a2 = coerce(gen(n->list.a[2], s, t), t), a3 = coerce(gen(n->list.a[3], s, t), t);
    if (is_bigf(t)) {
      char *sl = slot(t);
      emit("call $zb_fma(w %d, l %s, l %s, l %s, l %s)", t->bits, sl, opnd(a1), opnd(a2), opnd(a3));
      return V(t, sl);
    }
    char c = qc(t), *r = tmp();
    emit("%s =%c call $fma%s(%c %s, %c %s, %c %s)", r, c, c == 's' ? "f" : "", c, opnd(a1), c, opnd(a2), c, opnd(a3));
    return V(t, r);
  }
  if (!strcmp(b, "intCast") || !strcmp(b, "truncate")) {
    if (!ex) die("%s:%d: @%s needs a result type", n->tok->file, n->tok->line, b);
    if (ex->k == TY_OPT) ex = ex->elem;
    return int_conv(gen(x, s, NULL), ex, b[0] == 't');
  }
  if (!strcmp(b, "bitCast")) {
    Val v = rv(gen(x, s, NULL));
    if (!ex) die("@bitCast needs a result type");
    if (v.ck) {
      CVal r;
      if (ceval_rt(n, s, ex, &r)) {
        Val c = CK(r);
        c.t = ex;
        return c;
      }
      if (is_aggr(ex) || is_aggr(v.t))
        v = V(v.t, mat(v)), v.ck = 0, v = is_aggr(v.t) ? V(v.t, addr_of(coerce(CK(v.cv), v.t))) : v;
      else
        return coerce(v, ex);
    }
    if ((lpadded(v.t) || lpadded(ex)) && (v.t->k == TY_ARRAY || ex->k == TY_ARRAY)) return lbitcast(v, ex);
    if (is_aggr(v.t) || is_aggr(ex)) {
      if (is_aggr(v.t)) {
        if (is_aggr(ex)) {
          if (is_wide(ex) && ex->bits < 128 && ex->bits > 64) {
            char *sl = slot(ex);
            blit(addr_of(v), sl, 16);
            wnorm(ex, sl);
            return V(ex, sl);
          }
          return V(ex, addr_of(v));
        }
        return V(ex, load(ex, addr_of(v)));
      }
      char *sl = slot(ex);
      store(v.t, opnd(v), sl);
      return V(ex, sl);
    }
    if (v.t->k == TY_FLOAT && v.t->bits == 16 && ex->k != TY_FLOAT) {
      char *r = tmp();
      emit("%s =w call $zb_f2h(s %s)", r, opnd(v));
      return V(ex, norm(r, ex));
    }
    if (ex->k == TY_FLOAT && ex->bits == 16 && v.t->k != TY_FLOAT) {
      char *r = tmp();
      emit("%s =s call $zb_h2f(w %s)", r, opnd(v));
      return V(ex, r);
    }
    if ((v.t->k == TY_FLOAT) != (ex->k == TY_FLOAT)) {
      char *r = tmp();
      emit("%s =%c cast %s", r, qc(ex), opnd(v));
      return V(ex, r);
    }
    return V(ex, norm(opnd(v), ex));
  }
  if (!strcmp(b, "ptrCast") || !strcmp(b, "alignCast") || !strcmp(b, "constCast") || !strcmp(b, "volatileCast")) {
    Val v = rv(gen(x, s, (b[0] == 'a' || b[0] == 'v') ? ex : NULL));
    Type *to = ex ? ex : v.t;
    if (!strcmp(b, "constCast") && !ex) {
      if (v.t->k == TY_PTR)
        to = ptr_to(v.t->elem, 0);
      else if (v.t->k == TY_SLICE)
        to = slice_of(v.t->elem, 0);
      else if (v.t->k == TY_MPTR)
        to = mptr_to(v.t->elem, 0, v.t->hassent, v.t->sent);
    }
    if (to->k == TY_OPT && to->elem->k == TY_SLICE && v.t->k != TY_OPT) { /* cast to the slice, then wrap */
      Type *st = to->elem;
      Val r;
      if (v.t->k == TY_SLICE && tsize(v.t->elem) != tsize(st->elem) && tsize(st->elem) > 0) {
        char *a = addr_of(v), *l = load(t_u64, addp(a, 8)), *m = tmp(), *q = tmp(), *sl = slot(st);
        emit("%s =l mul %s, %d", m, l, tsize(v.t->elem));
        emit("%s =l udiv %s, %d", q, m, tsize(st->elem));
        store(t_u64, load(t_u64, a), sl);
        store(t_u64, q, addp(sl, 8));
        r = V(st, sl);
      } else {
        r = v;
        r.t = st;
      }
      return coerce(r, to);
    }
    if (v.t->k == TY_SLICE && to->k != TY_SLICE && !(to->k == TY_OPT && to->elem->k == TY_SLICE))
      return V(to, load(t_u64, addr_of(v)));
    if (v.t->k == TY_SLICE && to->k == TY_SLICE && tsize(v.t->elem) != tsize(to->elem) && tsize(to->elem) > 0) {
      char *a = addr_of(v), *l = load(t_u64, addp(a, 8)), *m = tmp(), *q = tmp(), *sl = slot(to);
      emit("%s =l mul %s, %d", m, l, tsize(v.t->elem));
      emit("%s =l udiv %s, %d", q, m, tsize(to->elem));
      store(t_u64, load(t_u64, a), sl);
      store(t_u64, q, addp(sl, 8));
      return V(to, sl);
    }
    if (to->k == TY_SLICE && (v.t->k == TY_PTR || v.t->k == TY_MPTR)) {
      int64_t bytes = v.t->k == TY_PTR ? tsize(v.t->elem) : 0;
      int es = tsize(to->elem);
      char *sl = slot(to);
      store(t_u64, opnd(v), sl);
      store(t_u64, fmt("%lld", (long long)(es ? bytes / es : 0)), addp(sl, 8));
      return V(to, sl);
    }
    if (is_aggr(to) || is_aggr(v.t)) {
      v.t = to;
      return v;
    }
    return V(to, opnd(v));
  }
  if (!strcmp(b, "intFromPtr")) {
    Val v = rv(gen(x, s, NULL));
    if (v.t->k == TY_SLICE) return V(t_usize, load(t_u64, addr_of(v)));
    return V(t_usize, opnd(v));
  }
  if (!strcmp(b, "ptrFromInt")) {
    Val v = coerce(gen(x, s, t_usize), t_usize);
    return V(ex, opnd(v));
  }
  if (!strcmp(b, "intFromBool")) {
    Val v = gen(x, s, NULL);
    if (is_vec(v.t)) {
      v = rv(v);
      Type *rt = vec_of(t_u1, v.t->len);
      char *sl = slot(rt), *pa = addr_of(v);
      for (int64_t i = 0; i < v.t->len; i++) {
        char *e = load(t_bool, addp(pa, i * tsize(t_bool)));
        store(t_u1, e, addp(sl, i * tsize(t_u1)));
      }
      return V(rt, sl);
    }
    v = coerce(v, t_bool);
    return V(t_u1, opnd(v));
  }
  if (!strcmp(b, "intFromEnum")) {
    Val v = rv(gen(x, s, NULL));
    Type *t = v.t;
    if (t->ct) layout(t->ct);
    if (t->k == TY_UNION && t->ct->tag && t->ct->tag->ct) layout(t->ct->tag->ct);
    if (t->k == TY_UNION) {
      return V(t->ct->tag->ct->tag, load(t->ct->tag, addp(addr_of(v), union_tag_off(t))));
    }
    return V(t->ct->tag, opnd(v));
  }
  if (!strcmp(b, "enumFromInt")) {
    if (ex && ex->k == TY_OPT) ex = ex->elem;
    if (!ex || ex->k != TY_ENUM) die("%s:%d: @enumFromInt needs an enum result type", n->tok->file, n->tok->line);
  }
  if (!strcmp(b, "enumFromInt")) {
    layout(ex->ct);
    Val v = rv(gen(x, s, NULL));
    if (v.ck) {
      CVal r = v.cv;
      r.t = ex;
      return CK(r);
    }
    return V(ex, opnd(int_conv(v, ex->ct->tag, 0)));
  }
  if (!strcmp(b, "intFromError")) {
    Val v = rv(gen(x, s, NULL));
    return V(t_u16, opnd(v));
  }
  if (!strcmp(b, "errorFromInt")) {
    Val v = coerce(gen(x, s, t_u16), t_u16);
    return V(t_errset, opnd(v));
  }
  if (!strcmp(b, "errorName")) {
    Val v = rv(gen(x, s, NULL));
    char *e = opnd(v), *w = tmp(), *o = tmp(), *a = tmp();
    emit("%s =l extuw %s", w, e);
    emit("%s =l mul %s, 16", o, w);
    emit("%s =l add $zb.errnames, %s", a, o);
    return V(slice_of(t_u8, 1), a);
  }
  if (!strcmp(b, "tagName")) {
    Val v = rv(gen(x, s, NULL));
    Type *t = v.t;
    char *tv;
    if (t->k == TY_UNION) {
      tv = load(t->ct->tag, addp(addr_of(v), union_tag_off(t)));
      t = t->ct->tag;
    } else
      tv = opnd(v);
    if (qc(t) == 'l') {
      char *w = tmp();
      emit("%s =w copy %s", w, tv);
      tv = w;
    }
    char *fnm = tagname_fn(t), *r = tmp();
    emit("%s =l call $%s(w %s)", r, fnm, tv);
    return V(slice_of(t_u8, 1), r);
  }

  if (strstr(b, "WithOverflow")) {
    Val a = rv(gen(x, s, NULL)), c2 = rv(gen(y, s, NULL));
    int shl = b[0] == 's' && b[1] == 'h';
    Type *t = shl ? a.t : peer(a, c2);
    if (t->k == TY_CINT) t = t_i64;
    a = coerce(a, t);
    if (!shl) c2 = coerce(c2, t);
    int sg = t->sign, bits = t->bits;
    char *A = opnd(a), *B2 = opnd(c2), *res, *ov = tmp();
    if (bits <= 32) {
      char *xa = tmp(), *xb = tmp(), *r = tmp();
      emit("%s =l %s %s", xa, sg ? "extsw" : "extuw", A);
      emit("%s =l %s %s", xb, (sg && !shl) ? "extsw" : "extuw", B2);
      emit("%s =l %s %s, %s", r, b[0] == 'a' ? "add" : shl ? "shl" : b[0] == 's' ? "sub" : "mul", xa, xb);
      char *tw = tmp();
      emit("%s =w copy %s", tw, r);
      res = norm(tw, t);
      char *e = tmp();
      emit("%s =l %s %s", e, sg ? "extsw" : "extuw", res);
      emit("%s =w cnel %s, %s", ov, e, r);
    } else {
      char *r = tmp();
      if (b[0] == 'a') {
        emit("%s =l add %s, %s", r, A, B2);
        if (sg) {
          char *p1 = tmp(), *p2 = tmp(), *p3 = tmp();
          emit("%s =l xor %s, %s", p1, A, r);
          emit("%s =l xor %s, %s", p2, B2, r);
          emit("%s =l and %s, %s", p3, p1, p2);
          emit("%s =w csltl %s, 0", ov, p3);
        } else
          emit("%s =w cultl %s, %s", ov, r, A);
      } else if (shl) {
        emit("%s =l shl %s, %s", r, A, B2);
        char *bk = tmp();
        emit("%s =l %s %s, %s", bk, sg ? "sar" : "shr", r, B2);
        emit("%s =w cnel %s, %s", ov, bk, A);
      } else if (b[0] == 's') {
        emit("%s =l sub %s, %s", r, A, B2);
        if (sg) {
          char *p1 = tmp(), *p2 = tmp(), *p3 = tmp();
          emit("%s =l xor %s, %s", p1, A, B2);
          emit("%s =l xor %s, %s", p2, A, r);
          emit("%s =l and %s, %s", p3, p1, p2);
          emit("%s =w csltl %s, 0", ov, p3);
        } else
          emit("%s =w cultl %s, %s", ov, A, B2);
      } else {
        emit("%s =l mul %s, %s", r, A, B2);
        char *sl = slot(t_u8), *lz = newl(), *lnz = newl(), *le = newl(), *z = tmp();
        store(t_u8, "0", sl);
        emit("%s =w ceql %s, 0", z, A);
        br(z, lz, lnz);
        label(lnz);
        char *q = tmp(), *d = tmp();
        emit("%s =l %s %s, %s", q, sg ? "div" : "udiv", r, A);
        emit("%s =w cnel %s, %s", d, q, B2);
        if (sg) {
          char *m1 = tmp(), *m2 = tmp(), *m3 = tmp(), *m4 = tmp();
          emit("%s =w ceql %s, -1", m1, A);
          emit("%s =w ceql %s, -9223372036854775808", m2, B2);
          emit("%s =w and %s, %s", m3, m1, m2);
          emit("%s =w or %s, %s", m4, d, m3);
          d = m4;
        }
        store(t_u8, d, sl);
        jmp(le);
        label(lz);
        jmp(le);
        label(le);
        ov = load(t_u8, sl);
      }
      res = r;
    }
    Vec names = {0}, types = {0};
    vpush(&names, "0");
    vpush(&names, "1");
    vpush(&types, t);
    vpush(&types, t_u1);
    Type *tt = mk_anon_struct(&names, &types, 1);
    char *sl = slot(tt);
    store(t, res, sl);
    store(t_u8, ov, addp(sl, ((Field *)tt->ct->fields.a[1])->off));
    return V(tt, sl);
  }
  if (!strcmp(b, "byteSwap") || !strcmp(b, "bitReverse")) {
    Val a = rv(gen(x, s, ex));
    Type *t = a.t;
    if (t->k == TY_CINT) t = ex ? ex : t_i64;
    a = coerce(a, t);
    char c = qc(t);
    int bits = t->bits;
    char *A = opnd(a), *acc = "0";
    int step = b[1] == 'y' ? 8 : 1;
    unsigned long long mk = step == 8 ? 0xff : 1;
    for (int i = 0; i < bits / step; i++) {
      char *p = tmp(), *q = tmp(), *r = tmp(), *o = tmp();
      emit("%s =%c shr %s, %d", p, c, A, i * step);
      emit("%s =%c and %s, %llu", q, c, p, mk);
      emit("%s =%c shl %s, %d", r, c, q, bits - step - i * step);
      emit("%s =%c or %s, %s", o, c, acc, r);
      acc = o;
    }
    return V(t, norm(acc, t));
  }
  if (!strcmp(b, "fieldParentPtr")) {
    CVal nm;
    if (!ceval(x, s, &nm) || nm.k != CV_STR) die("@fieldParentPtr field name must be comptime");
    if (ex && ex->k == TY_OPT) ex = ex->elem;
    if (!ex || ex->k != TY_PTR) die("%s:%d: @fieldParentPtr needs a pointer result type", n->tok->file, n->tok->line);
    char nb[256];
    snprintf(nb, sizeof nb, "%.*s", nm.slen, nm.s);
    layout(ex->elem->ct);
    Field *f = find_field(ex->elem->ct, nb);
    if (!f) die("no field %s", nb);
    Val p = rv(gen(y, s, NULL));
    char *r = tmp();
    emit("%s =l sub %s, %d", r, opnd(p), f->off);
    return V(ex, r);
  }
  if (!strncmp(b, "atomic", 6) || !strncmp(b, "cmpxchg", 7)) {
    Type *t0 = eval_type(x, s);
    Val p = rv(gen(y, s, ptr_to(t0, 0)));
    char *P = opnd(p);
    Type *t = is_packed(t0) ? int_type(tsize(t0) * 8, 0) : t0;
#define PKIN(v_) (t != t0 ? V(t, load(t, addr_of(coerce(v_, t0)))) : coerce(v_, t))
#define PKOUT(v_)                                                                                                      \
  (t != t0 ? ({                                                                                                        \
    Val o_ = (v_);                                                                                                     \
    char *sl_ = slot(t0);                                                                                              \
    store(t, opnd(o_), sl_);                                                                                           \
    V(t0, sl_);                                                                                                        \
  })                                                                                                                   \
           : (v_))
    if (!strcmp(b, "atomicLoad")) return PKOUT(V(t, load(t, P)));
    if (!strcmp(b, "atomicStore")) {
      Val v = PKIN(gen(n->list.a[2], s, t0));
      store(t, opnd(v), P);
      return VOIDV();
    }
    if (!strcmp(b, "atomicRmw")) {
      CVal op;
      if (!ceval_ex(n->list.a[2], s, bt_type_pub("AtomicRmwOp"), &op)) die("@atomicRmw op must be comptime");
      const char *on = NULL;
      Container *rc = bt_type_pub("AtomicRmwOp")->ct;
      layout(rc);
      if (op.k == CV_ENUMLIT)
        on = op.s;
      else
        for (int i = 0; i < rc->fields.n; i++) {
          Field *f = rc->fields.a[i];
          if (f->val == (int64_t)op.i) on = f->name;
        }
      Val v = PKIN(gen(n->list.a[3], s, t0));
      Val old = V(t, load(t, P));
      Val nv;
      if (!strcmp(on, "Xchg"))
        nv = v;
      else if (!strcmp(on, "Max") || !strcmp(on, "Min"))
        nv = sel2(gen_cmp(on[1] == 'a' ? ">" : "<", v, old), v, old, t);
      else if (!strcmp(on, "Nand")) {
        Val a2 = gen_arith("&", old, v);
        char *r = tmp();
        emit("%s =%c xor %s, -1", r, qc(t), opnd(a2));
        nv = V(t, norm(r, t));
      } else
        nv = coerce(gen_arith(!strcmp(on, "Add")   ? "+%"
                              : !strcmp(on, "Sub") ? "-%"
                              : !strcmp(on, "And") ? "&"
                              : !strcmp(on, "Or")  ? "|"
                                                   : "^",
                              old, v),
                    t);
      store(t, opnd(nv), P);
      return PKOUT(old);
    }
    if (!strncmp(b, "cmpxchg", 7)) {
      Val e = PKIN(gen(n->list.a[2], s, t0)), nv = PKIN(gen(n->list.a[3], s, t0));
      Type *ot = opt_of(t0);
      Val cur = V(t, load(t, P));
      Val eq = gen_cmp("==", cur, e);
      char *sl = slot(ot), *l1 = newl(), *l2 = newl(), *le = newl();
      br(opnd(eq), l1, l2);
      label(l1);
      store(t, opnd(nv), P);
      put(coerce(CK(cv_null_pub()), ot), ot, sl);
      jmp(le);
      label(l2);
      put(coerce(PKOUT(cur), ot), ot, sl);
      jmp(le);
      label(le);
      return is_aggr(ot) ? V(ot, sl) : V(ot, load(ot, sl));
    }
  }
  if ((!strcmp(b, "memcpy") || !strcmp(b, "memmove") || !strcmp(b, "memset")) && ct_try_store(x, n, s)) return VOIDV();
  if (!strcmp(b, "memcpy") || !strcmp(b, "memmove")) {
    Val d = rv(gen(x, s, NULL)), sv = rv(gen(y, s, NULL));
    char *dp, *sp, *len = NULL;
    Type *et;
    if (d.t->k == TY_SLICE) {
      dp = load(t_u64, addr_of(d));
      len = load(t_u64, addp(addr_of(d), 8));
      et = d.t->elem;
    } else if (d.t->k == TY_PTR && d.t->elem->k == TY_ARRAY) {
      dp = opnd(d);
      len = fmt("%lld", (long long)d.t->elem->len);
      et = d.t->elem->elem;
    } else {
      dp = opnd(d);
      et = d.t->elem;
    }
    if (sv.t->k == TY_SLICE) {
      sp = load(t_u64, addr_of(sv));
      if (!len) len = load(t_u64, addp(addr_of(sv), 8));
    } else if (sv.ck && sv.cv.k == CV_STR) {
      sp = mat(sv);
      if (!len) len = fmt("%d", sv.cv.slen);
    } else if (sv.t->k == TY_ARRAY) {
      sp = addr_of(sv);
      if (!len) len = fmt("%lld", (long long)sv.t->len);
    } else if (sv.t->k == TY_PTR && sv.t->elem->k == TY_ARRAY) {
      sp = opnd(sv);
      if (!len) len = fmt("%lld", (long long)sv.t->elem->len);
    } else
      sp = opnd(sv);
    char *nb = tmp();
    emit("%s =l mul %s, %d", nb, len, tsize(et));
    emit("call $memmove(l %s, l %s, l %s)", dp, sp, nb);
    return VOIDV();
  }
  if (!strcmp(b, "memset")) {
    Val d = rv(gen(x, s, NULL));
    char *dp, *len;
    Type *et;
    if (d.t->k == TY_SLICE) {
      dp = load(t_u64, addr_of(d));
      len = load(t_u64, addp(addr_of(d), 8));
      et = d.t->elem;
    } else {
      dp = opnd(d);
      len = fmt("%lld", (long long)d.t->elem->len);
      et = d.t->elem->elem;
    }
    Val v = coerce(gen(y, s, et), et);
    if (v.ck && v.cv.k == CV_UNDEF) return VOIDV();
    if (tsize(et) == 1) {
      char *w = opnd(v);
      emit("call $memset(l %s, w %s, l %s)", dp, w, len);
      return VOIDV();
    }
    char *is = slot(t_usize), *lc = newl(), *lb = newl(), *le = newl();
    store(t_u64, "0", is);
    jmp(lc);
    label(lc);
    char *i = load(t_u64, is), *c2 = tmp();
    emit("%s =w cultl %s, %s", c2, i, len);
    br(c2, lb, le);
    label(lb);
    char *o = tmp(), *a = tmp();
    emit("%s =l mul %s, %d", o, i, tsize(et));
    emit("%s =l add %s, %s", a, dp, o);
    put(v, et, a);
    char *i2 = tmp();
    emit("%s =l add %s, 1", i2, i);
    store(t_u64, i2, is);
    jmp(lc);
    label(le);
    return VOIDV();
  }
  if (!strcmp(b, "min") || !strcmp(b, "max")) return gen_minmax(n, s, ex, b[1] == 'i');
  if (!strcmp(b, "divTrunc") || !strcmp(b, "divExact") || !strcmp(b, "rem"))
    return gen_arith(b[0] == 'r' ? "%" : "/", gen(x, s, ex), gen(y, s, ex));
  if (!strcmp(b, "divFloor") || !strcmp(b, "mod")) {
    Val a = rv(gen(x, s, ex)), d = rv(gen(y, s, ex));
    Type *t = peer(a, d);
    if (t->k == TY_CINT) t = ex ? ex : t_i64;
    a = coerce(a, t);
    d = coerce(d, t);
    if (is_bigf(t)) return V(t, bigf_op(b[0] == 'd' ? 24 : 5, t, opnd(a), opnd(d)));
    if (is_float(t)) {
      char c = qc(t), *q = tmp(), *f = tmp();
      emit("%s =%c div %s, %s", q, c, opnd(a), opnd(d));
      emit("%s =%c call $%s(%c %s)", f, c, c == 's' ? "floorf" : "floor", c, q);
      if (b[0] == 'd') return V(t, f);
      char *m = tmp(), *r = tmp();
      emit("%s =%c mul %s, %s", m, c, f, opnd(d));
      emit("%s =%c sub %s, %s", r, c, opnd(a), m);
      return V(t, r);
    }
    if (!t->sign) return gen_arith(b[0] == 'm' ? "%" : "/", a, d);
    char cl = qc(t), *A = opnd(a), *D = opnd(d), *q = tmp(), *r = tmp(), *nz = tmp(), *x1 = tmp(), *neg = tmp(),
         *adj = tmp(), *res = tmp(), *ext = tmp();
    emit("%s =%c div %s, %s", q, cl, A, D);
    emit("%s =%c rem %s, %s", r, cl, A, D);
    emit("%s =w cne%c %s, 0", nz, cl, r);
    emit("%s =%c xor %s, %s", x1, cl, r, D);
    emit("%s =w cslt%c %s, 0", neg, cl, x1);
    emit("%s =w and %s, %s", adj, nz, neg);
    if (cl == 'l')
      emit("%s =l extuw %s", ext, adj);
    else
      emit("%s =w copy %s", ext, adj);
    if (b[0] == 'm') {
      char *m = tmp();
      emit("%s =%c mul %s, %s", m, cl, ext, D);
      emit("%s =%c add %s, %s", res, cl, r, m);
    } else
      emit("%s =%c sub %s, %s", res, cl, q, ext);
    return V(t, res);
  }
  if (!strcmp(b, "shlExact") || !strcmp(b, "shrExact")) {
    Val a = gen(x, s, ex);
    Type *st = NULL;
    if (a.t->k == TY_INT) {
      int bb = bits_of(a.t), l = 0;
      while ((1 << l) < bb) l++;
      st = int_type(l, 0);
    } /* rhs result type: Log2Int(T) */
    return gen_arith(b[1] == 'h' && b[2] == 'l' ? "<<" : ">>", a, gen(y, s, st));
  }
  if (!strcmp(b, "abs")) {
    Val a = rv(gen(x, s, NULL));
    Type *t = a.t;
    if (is_bigf(t)) return V(t, bigf_op(9, t, opnd(a), NULL));
    if (t->k == TY_FLOAT) {
      char c = qc(t), *r = tmp();
      emit("%s =%c call $fabs%s(%c %s)", r, c, c == 's' ? "f" : "", c, opnd(a));
      return V(t, r);
    }
    if (t->k == TY_INT && !t->sign) return a;
    if (is_vec(t)) {
      char *sl = slot(t);
      Val av = V(t, addr_of(a));
      Type *et = t->elem;
      Type *ut = et->k == TY_INT ? int_type(et->bits, 0) : et;
      for (int64_t i = 0; i < t->len; i++) {
        Val e = vel(av, i);
        char *r;
        if (et->k == TY_FLOAT) {
          char c = qc(et);
          r = tmp();
          emit("%s =%c call $fabs%s(%c %s)", r, c, c == 's' ? "f" : "", c, opnd(e));
        } else if (!et->sign)
          r = opnd(e);
        else {
          char c = qc(et), *o = opnd(e), *ng = tmp(), *sg = tmp(), *x1 = tmp();
          r = tmp();
          emit("%s =%c sar %s, %d", sg, c, o, c == 'w' ? 31 : 63);
          emit("%s =%c xor %s, %s", x1, c, o, sg);
          emit("%s =%c sub %s, %s", ng, c, x1, sg);
          r = ng;
        }
        store(et, r, addp(sl, i * tsize(et)));
      }
      return V(vec_of(ut, t->len), sl);
    }
    if (is_wide(t)) {
      Type *ut = int_type(t->bits, 0);
      if (!t->sign) return V(ut, a.op);
      char *lo = wlo(a), *hi = whi(a), *sg = tmp(), *xl = tmp(), *xh = tmp();
      emit("%s =l sar %s, 63", sg, hi);
      emit("%s =l xor %s, %s", xl, lo, sg);
      emit("%s =l xor %s, %s", xh, hi, sg);
      Val xv = w_from_parts(ut, xl, xh), sv = w_from_parts(ut, sg, sg);
      return w_arith("-", ut, xv, sv);
    }
    char cl = qc(t), *o = opnd(a), *ng = tmp(), *c2 = tmp(), *sl = slot(t), *l1 = newl(), *l2 = newl();
    store(t, o, sl);
    emit("%s =w cslt%c %s, 0", c2, cl, o);
    br(c2, l1, l2);
    label(l1);
    emit("%s =%c neg %s", ng, cl, o);
    store(t, ng, sl);
    jmp(l2);
    label(l2);
    return V(int_type(t->bits, 0), load(t, sl));
  }
  if (!strcmp(b, "panic")) {
    Val m = coerce(gen(x, s, slice_of(t_u8, 1)), slice_of(t_u8, 1));
    char *a = addr_of(m);
    char *p = load(t_u64, a), *l = load(t_u64, addp(a, 8));
    emit("call $zb.panic(l %s, l %s)", p, l);
    emit("hlt");
    term = 1;
    return NORET();
  }
  if (!strcmp(b, "prefetch")) {
    gen(x, s, NULL);
    return VOIDV();
  }
  if (!strcmp(b, "extern")) {
    Type *t = eval_type(x, s);
    CVal o;
    if (!ceval_force(y, s, &o)) die("@extern options not comptime");
    int fi = field_index(cv_typeof(&o), "name");
    return V(t, fmt("$%s", cv_cstr(o.el[fi], NULL)));
  }
  if (!strcmp(b, "cVaStart")) {
    Type *t = ex ? ex : bt_type_pub("VaList");
    char *sl = slot(t);
    emit("vastart %s", sl);
    return V(t, sl);
  }
  if (!strcmp(b, "cVaEnd")) {
    gen(x, s, NULL);
    return VOIDV();
  }
  if (!strcmp(b, "cVaCopy")) {
    Val p = rv(gen(x, s, NULL));
    Type *t = p.t->elem;
    char *sl = slot(t);
    blit(opnd(p), sl, tsize(t));
    return V(t, sl);
  }
  if (!strcmp(b, "cVaArg")) {
    Val p = rv(gen(x, s, NULL));
    Type *t = eval_type(y, s);
    char *r = tmp();
    char q = t->k == TY_FLOAT                                                         ? (t->bits == 32 ? 's' : 'd')
             : (tsize(t) == 8 || t->k == TY_PTR || t->k == TY_MPTR || t->k == TY_OPT) ? 'l'
                                                                                      : 'w';
    emit("%s =%c vaarg %s", r, q, opnd(p));
    return V(t, t->k == TY_FLOAT || q == 'l' ? r : norm(r, t));
  }
  if (!strcmp(b, "trap") || !strcmp(b, "breakpoint")) {
    emit("hlt");
    term = 1;
    return NORET();
  }
  if (!strcmp(b, "field")) {
    Val base = gen(x, s, NULL);
    CVal nm;
    char *nms = ceval_force(y, s, &nm) ? cv_cstr(&nm, NULL) : NULL;
    if (!nms)
      die("%s:%d: @field name must be comptime-known string (at %s)", n->tok->file, n->tok->line, ct_fail_loc());
    return gen_member(base, nms, n);
  }
  if (!strcmp(b, "unionInit")) {
    Type *t = eval_type(x, s);
    CVal nm;
    char *nms = ceval_force(y, s, &nm) ? cv_cstr(&nm, NULL) : NULL;
    if (!nms)
      die("%s:%d: @unionInit field name must be comptime-known (at %s)", n->tok->file, n->tok->line, ct_fail_loc());
    Field *f = find_field(t->ct, nms);
    if (!f) die("%s:%d: no field '%s' in union %s", n->tok->file, n->tok->line, nms, tname(t));
    char *sl = slot(t);
    Val v = coerce(gen(n->list.a[2], s, f->t), f->t);
    put(v, f->t, sl);
    if (t->ct->tagged) store(t->ct->tag, fmt("%lld", (long long)f->val), addp(sl, union_tag_off(t)));
    return V(t, sl);
  }
  if (!strcmp(b, "setEvalBranchQuota") || !strcmp(b, "setRuntimeSafety") || !strcmp(b, "branchHint") ||
      !strcmp(b, "setFloatMode") || !strcmp(b, "disableInstrumentation"))
    return VOIDV();
  if (!strcmp(b, "errorReturnTrace")) {
    CVal z = {0};
    z.k = CV_NULL;
    return CK(z);
  }
  if (!strcmp(b, "returnAddress") || !strcmp(b, "frameAddress")) return V(t_usize, "0");
  if (!strcmp(b, "clz") || !strcmp(b, "ctz") || !strcmp(b, "popCount")) {
    Val a = rv(gen(x, s, NULL));
    Type *t = a.t;
    if (is_wide(t)) {
      char *ad = addr_of(a), *lo = load(t_u64, ad), *hi = load(t_u64, addp(ad, 8)), *res = slot(t_u64);
      if (b[0] == 'p') {
        char *p1 = tmp(), *p2 = tmp(), *r = tmp(), *rl = tmp();
        emit("%s =w call $__popcountdi2(l %s)", p1, lo);
        emit("%s =w call $__popcountdi2(l %s)", p2, hi);
        emit("%s =w add %s, %s", r, p1, p2);
        emit("%s =l extuw %s", rl, r);
        return int_conv(V(t_u64, rl), int_type(8, 0), 1);
      }
      int clz = b[1] == 'l';
      char *first = clz ? hi : lo, *second = clz ? lo : hi;
      char *z1 = tmp(), *z2 = tmp(), *l1 = newl(), *l2 = newl(), *l3 = newl(), *l4 = newl(), *le = newl();
      int adj = clz ? 128 - t->bits : 0;
      const char *fn = clz ? "__clzdi2" : "__ctzdi2";
      emit("%s =w cnel %s, 0", z1, first);
      br(z1, l1, l2);
      label(l1);
      {
        char *r = tmp(), *r2 = tmp(), *rl = tmp();
        emit("%s =w call $%s(l %s)", r, fn, first);
        emit("%s =w sub %s, %d", r2, r, adj);
        emit("%s =l extuw %s", rl, r2);
        store(t_u64, rl, res);
        jmp(le);
      }
      label(l2);
      emit("%s =w cnel %s, 0", z2, second);
      br(z2, l3, l4);
      label(l3);
      {
        char *r = tmp(), *r2 = tmp(), *rl = tmp();
        emit("%s =w call $%s(l %s)", r, fn, second);
        emit("%s =w add %s, %d", r2, r, 64 - adj);
        emit("%s =l extuw %s", rl, r2);
        store(t_u64, rl, res);
        jmp(le);
      }
      label(l4);
      store(t_u64, fmt("%d", t->bits), res);
      jmp(le);
      label(le);
      return int_conv(V(t_u64, load(t_u64, res)), int_type(8, 0), 1);
    }
    char *o = opnd(a), *w = o;
    if (qc(t) == 'w') {
      w = tmp();
      emit("%s =l extuw %s", w, o);
    }
    char *r = tmp(), *res = slot(t_u64);
    if (b[0] == 'p') {
      emit("%s =w call $__popcountdi2(l %s)", r, w);
      return V(int_type(7, 0), r);
    }
    char *z = tmp(), *lz = newl(), *lnz = newl(), *le = newl();
    emit("%s =w ceql %s, 0", z, w);
    br(z, lz, lnz);
    label(lz);
    store(t_u64, fmt("%d", t->bits), res);
    jmp(le);
    label(lnz);
    emit("%s =w call $%s(l %s)", r, b[1] == 'l' ? "__clzdi2" : "__ctzdi2", w);
    if (b[1] == 'l' && t->bits < 64) {
      char *r2 = tmp();
      emit("%s =w sub %s, %d", r2, r, 64 - t->bits);
      r = r2;
    }
    char *rl = tmp();
    emit("%s =l extuw %s", rl, r);
    store(t_u64, rl, res);
    jmp(le);
    label(le);
    return int_conv(V(t_u64, load(t_u64, res)), int_type(8, 0), 1);
  }
  {
    static const char *tyb[] = {"Int",  "Vector", "Struct", "Union",    "Enum",       "Pointer",  "Fn",     "Tuple",
                                "Type", "Float",  "Array",  "Optional", "ErrorUnion", "ErrorSet", "Opaque", NULL};
    for (int i = 0; tyb[i]; i++)
      if (!strcmp(b, tyb[i]) && ceval_force(n, s, &c)) return CK(c);
  } /* type constructors: args are comptime */
  die("%s:%d: builtin @%s not supported", n->tok->file, n->tok->line, b);
}
