#include "gen_int.h"

/* ---------- control flow ---------- */
Loop *find_loop(char *label, int forcont) {
  for (Loop *l = loops; l; l = l->up) {
    if (label) {
      if (l->label && !strcmp(l->label, label)) return l;
    } else if (l->kind == 0)
      return l;
  }
  die("break/continue target not found");
  (void)forcont;
}
int ex_partial(Type *t) { /* tuple hint with untyped (anytype) fields: peer-resolve instead */
  if (!t || !is_tuple_type(t)) return 0;
  layout(t->ct);
  for (int i = 0; i < t->ct->fields.n; i++)
    if (((Field *)t->ct->fields.a[i])->t->k == TY_ANYTYPE) return 1;
  return 0;
}
int type_incomplete(Type *t) {
  if (!t) return 1;
  if (t->k == TY_NULL || t->k == TY_UNDEF || t->k == TY_ENUMLIT || t->k == TY_NORET || t->k == TY_CINT ||
      t->k == TY_CFLOAT)
    return 1;
  if (t->k == TY_TUPLE || (t->k == TY_STRUCT && is_anon(t))) {
    layout(t->ct);
    for (int i = 0; i < t->ct->fields.n; i++)
      if (type_incomplete(((Field *)t->ct->fields.a[i])->t)) return 1;
  }
  return 0;
}
Val gen_block(Node *n, Scope *s, Type *ex) {
  Scope *bs = new_scope(s, NULL);
  int base = defers.n;
  if (n->label && !ex && !in_typeof) { /* peer-resolve the types of all breaks first */
    Node *sc = collect_node;
    collect_node = n;
    Type *pt = typeof_impl(n, s);
    collect_node = sc;
    if (pt && !type_incomplete(pt) && !type_is_ctonly(pt) && pt->k != TY_VOID) ex = pt;
  }
  Loop L;
  memset(&L, 0, sizeof L);
  Res R;
  memset(&R, 0, sizeof R);
  R.ex = ex;
  if (n == collect_node && in_typeof) {
    R.collect = 1;
    collect_node = NULL;
  } else if (in_typeof && ex_partial(ex))
    R.collect = 1;
  else if (n->label && !ex && in_typeof)
    R.collect = 1;
  if (n->label) {
    L.label = n->label;
    L.brk = newl();
    L.res = &R;
    L.dbase = base;
    L.kind = 1;
    L.up = loops;
    loops = &L;
  }
  for (int i = 0; i < n->list.n; i++) {
    Node *st = n->list.a[i];
    gen(st, bs, NULL);
    if (term) break; /* rest of the block is unreachable (e.g. after a comptime-pruned branch) */
  }
  int fell = !term;
  if (!term) run_defers(base, NULL);
  defers.n = base;
  if (n->label) {
    loops = L.up;
    if (fell && !term) {
      if (R.ex && R.ex->k == TY_ERRU && R.ex->elem == t_void && !R.collect)
        res_put(&R, coerce(VOIDV(), R.ex)); /* fallthrough = success */
      else if (R.t && R.t->k == TY_ERRSET) {
        R.t = erru_of2(t_void, R.t);
        R.has = 1;
      } else {
        if (!R.t) {
          R.t = t_void;
        }
        R.has = 1;
      }
      jmp(L.brk);
    }
    label(L.brk);
    return res_get(&R);
  }
  if (!fell) return NORET();
  return VOIDV();
}
void cap_bind(Scope *s, char *name, int ref, Val payload) {
  if (!name || !strcmp(name, "_")) return;
  if (ref) {
    bind_val(s, name, V(ptr_to(payload.t, 0), payload.op));
    return;
  }
  bind_val(s, name, rv(payload));
}
Val gen_if(Node *n, Scope *s, Type *ex) {
  CVal c;
  if (!n->cap && ceval(n->a, s, &c) && c.k == CV_BOOL) {
    if (c.i) return gen(n->b, s, ex);
    return n->c ? gen(n->c, s, ex) : VOIDV();
  }
  Res R;
  memset(&R, 0, sizeof R);
  R.ex = ex;
  Val cv0 = n->cap ? (Val){0} : gen(n->a, s, t_bool);
  if (!n->cap && cv0.ck && cv0.cv.k == CV_BOOL) {
    if (cv0.cv.i) return gen(n->b, s, ex);
    return n->c ? gen(n->c, s, ex) : VOIDV();
  }
  if (!ex && n->c && !in_typeof) {
    Type *t1 = typeof_impl(n->b, s), *t2 = typeof_impl(n->c, s), *p = peer_t(t1, t2);
    if (p && p != t1 && p->k != TY_CINT) R.ex = p;
  }
  if (!ex && n->c && in_typeof) R.collect = 1;
  char *lt = newl(), *lf = newl(), *lx = newl();
  Scope *ts = new_scope(s, NULL), *es = new_scope(s, NULL);
  Val cv = coerce(cv0, t_bool);
  br(opnd(cv), lt, lf);
  label(lt);
  Val tv = gen(n->b, ts, n->c ? R.ex : NULL);
  res_put(&R, n->c || tv.t->k == TY_NORET ? tv : VOIDV());
  jmp(lx);
  label(lf);
  if (n->c) {
    Val ev = gen(n->c, es, R.ex ? R.ex : R.collect ? NULL : R.t);
    res_put(&R, ev);
  } else
    res_put(&R, VOIDV());
  jmp(lx);
  label(lx);
  return res_get(&R);
}
void if_peer(Res *R, Node *n, Scope *s, Type *ex) {
  if (ex || !n->c) return;
  if (in_typeof) {
    R->collect = 1;
    return;
  }
  Type *p = typeof_impl(n, s);
  if (p && p->k != TY_CINT && p->k != TY_NORET && p->k != TY_NULL && p->k != TY_ENUMLIT && p->k != TY_UNDEF &&
      p->k != TY_VOID)
    R->ex = p;
}
Val gen_if_erru(Node *n, Scope *s, Type *ex, Val cv) {
  Res R;
  memset(&R, 0, sizeof R);
  R.ex = ex;
  if_peer(&R, n, s, ex);
  char *lt = newl(), *lf = newl(), *lx = newl();
  Scope *ts = new_scope(s, NULL), *es = new_scope(s, NULL);
  char *a = addr_of(cv);
  char *e = load(t_u16, a);
  br(e, lf, lt);
  label(lt);
  if (n->cap && cv.t->elem != t_void)
    cap_bind(ts, n->cap, n->capref, LV(cv.t->elem, addp(a, erru_off(cv.t))));
  else if (n->cap && strcmp(n->cap, "_"))
    bind_cval(ts, n->cap, cv_void());
  Val tv = gen(n->b, ts, n->c ? ex : NULL);
  res_put(&R, n->c || tv.t->k == TY_NORET ? tv : VOIDV());
  jmp(lx);
  label(lf);
  if (n->cap2) bind_val(es, n->cap2, V(eset_of(cv.t), e));
  if (n->c) {
    Val ev = gen(n->c, es, ex ? ex : R.collect ? NULL : R.t);
    res_put(&R, ev);
  } else
    res_put(&R, VOIDV());
  jmp(lx);
  label(lx);
  return res_get(&R);
}
Val gen_while(Node *n, Scope *s, Type *ex) {
  int always = 0, skip = 0;
  if (!ex && n->c && !in_typeof) ex = loop_peer(n, s);
  Loop L;
  memset(&L, 0, sizeof L);
  Res R;
  memset(&R, 0, sizeof R);
  R.ex = ex;
  if (n == collect_node && in_typeof) {
    R.collect = 1;
    collect_node = NULL;
  } else if (in_typeof && ex_partial(ex))
    R.collect = 1;
  char *lc = newl(), *lb = newl(), *lk = newl(), *le = newl(), *lx = newl();
  L.label = n->label;
  L.brk = lx;
  L.cont = lk;
  L.res = &R;
  L.dbase = defers.n;
  L.kind = 0;
  jmp(lc);
  label(lc);
  Scope *bs = new_scope(s, NULL), *es = new_scope(s, NULL);
  if (n->cap || n->cap2) {
    Val cv = gen(n->a, s, NULL);
    if (cv.t->k == TY_OPT && cv.t->elem->k == TY_NORET) {
      jmp(le);
      label(lb);
      skip = 1;
    } /* ?noreturn: always null, body unanalyzed */
    else if (cv.t->k == TY_OPT) {
      char *pv = opt_is_ptr(cv.t) ? opnd(cv) : NULL;
      if (pv) {
        char *h = tmp();
        emit("%s =w cnel %s, 0", h, pv);
        br(h, lb, le);
      } else
        br(opt_has(cv), lb, le);
      label(lb);
      cap_bind(bs, n->cap, n->capref, opt_payload(cv, pv));
    } else {
      char *a = addr_of(cv), *e = load(t_u16, a);
      br(e, le, lb);
      label(lb);
      if (!n->cap)
        ;
      else if (cv.t->elem != t_void)
        cap_bind(bs, n->cap, n->capref, LV(cv.t->elem, addp(a, erru_off(cv.t))));
      else if (strcmp(n->cap, "_"))
        bind_cval(bs, n->cap, cv_void());
      if (n->cap2) bind_val(es, n->cap2, V(eset_of(cv.t), e));
    }
  } else {
    Val cv = coerce(gen(n->a, s, t_bool), t_bool);
    if (cv.ck) {
      jmp(cv.cv.i ? lb : le);
      if (cv.cv.i) always = 1;
    } else
      br(opnd(cv), lb, le);
    label(lb);
  }
  L.up = loops;
  loops = &L;
  if (!skip) gen(n->b, bs, NULL);
  jmp(lk);
  label(lk);
  if (n->d && !skip) gen(n->d, bs, NULL);
  jmp(lc); /* continue expr may `break` out of this loop */
  loops = L.up;
  label(le);
  if (n->c) {
    Val ev = gen(n->c, es, ex);
    res_put(&R, ev);
  } else if ((R.has || ex) && !always)
    res_put(&R, VOIDV());
  else if (always) {
    emit("hlt");
    term = 1;
  }
  jmp(lx);
  label(lx);
  if (always && !L.brk_used) {
    emit("hlt");
    term = 1;
    return NORET();
  }
  if (!n->c && !R.has) return VOIDV();
  return res_get(&R);
}
Val gen_inline_while(Node *n, Scope *s, Type *ex) {
  Loop L;
  memset(&L, 0, sizeof L);
  Res R;
  memset(&R, 0, sizeof R);
  R.ex = ex;
  char *lx = newl();
  int stopped = 0, iters = 0;
  L.label = n->label;
  L.brk = lx;
  L.res = &R;
  L.dbase = defers.n;
  L.kind = 0;
  for (;;) {
    if (term) {
      stopped = 1;
      break;
    }
    Scope *bs = new_scope(s, NULL);
    CVal c;
    if (!ceval_force(n->a, s, &c))
      die("%s:%d: inline while condition is not comptime-known (at %s)", n->tok->file, n->tok->line, ct_fail_loc());
    if (n->cap) {
      if (c.k == CV_NULL || c.k == CV_ERR) break;
      bind_cval(bs, n->cap, c);
    } else {
      if (c.k != CV_BOOL) die("%s:%d: inline while condition is not a bool", n->tok->file, n->tok->line);
      if (!c.i) break;
    }
    char *lk = newl();
    L.cont = lk;
    L.cont_used = 0;
    L.up = loops;
    loops = &L;
    gen(n->b, bs, NULL);
    loops = L.up;
    if (term && !L.cont_used) {
      stopped = 1;
      break;
    }
    jmp(lk);
    label(lk);
    if (n->d) gen(n->d, bs, NULL);
    if (++iters > 1000000) die("%s:%d: inline while: too many iterations", n->tok->file, n->tok->line);
  }
  if (!stopped && n->c) res_put(&R, gen(n->c, s, ex));
  int dead = term && !L.brk_used; /* the unrolled code ends in return/noreturn */
  jmp(lx);
  label(lx);
  if (dead) {
    emit("hlt");
    term = 1;
    return NORET();
  }
  if (!R.has) return VOIDV();
  return res_get(&R);
}
Val gen_inline_for(Node *n, Scope *s, Type *ex) {
  int ni = n->list.n;
  CVal *cvs = xalloc(sizeof(CVal) * ni);
  Val *rvs = xalloc(sizeof(Val) * ni);
  char *kind = xalloc(ni);
  int64_t *start = xalloc(sizeof(int64_t) * ni);
  int64_t len = -1;
  for (int i = 0; i < ni; i++) {
    Node *e = n->list.a[i];
    int64_t l = -1;
    if (e->k == N_RANGE) {
      CVal lo, hi;
      if (!e->b && !ceval(e->a, s, &lo)) {
        kind[i] = 3;
        rvs[i] = coerce(rv(gen(e->a, s, t_usize)), t_usize);
        char *sl = slot(t_usize);
        store(t_u64, opnd(rvs[i]), sl);
        rvs[i] = V(t_usize, sl);
        continue;
      } /* runtime open range start */
      if (!ceval_force(e->a, s, &lo)) die("%s:%d: inline for range must be comptime-known", e->tok->file, e->tok->line);
      kind[i] = 2;
      start[i] = (int64_t)lo.i;
      if (e->b) {
        if (!ceval_force(e->b, s, &hi))
          die("%s:%d: inline for range must be comptime-known", e->tok->file, e->tok->line);
        l = (int64_t)(hi.i - lo.i);
      }
    } else {
      CVal c;
      if (ceval(e, s, &c) && c.k != CV_UNDEF) {
        kind[i] = 1;
        cvs[i] = c;
        if (!cv_len(&c, &l)) {
          Type *t = cv_typeof(&c);
          if (t->k == TY_PTR && t->elem->k == TY_ARRAY)
            l = t->elem->len;
          else
            die("%s:%d: cannot iterate over %s", e->tok->file, e->tok->line, tname(t));
        }
      } else {
        Val v = gen(e, s, NULL);
        rvs[i] = v;
        Type *t = v.t;
        if (v.ck && v.cv.k != CV_UNDEF && cv_len(&v.cv, &l)) {
          kind[i] = 1;
          cvs[i] = v.cv;
          if (len < 0 && l >= 0) len = l;
          continue;
        }
        if (t->k == TY_ARRAY)
          l = t->len;
        else if (t->k == TY_PTR && t->elem->k == TY_ARRAY)
          l = t->elem->len;
        else if ((t->k == TY_STRUCT || t->k == TY_TUPLE) && t->ct) {
          layout(t->ct);
          l = t->ct->fields.n;
        } else if (t->k == TY_PTR && (t->elem->k == TY_STRUCT || t->elem->k == TY_TUPLE) && t->elem->ct) {
          layout(t->elem->ct);
          l = t->elem->ct->fields.n;
          v = rv(v);
          rvs[i] = LV(t->elem, opnd(v));
        } else
          die("%s:%d: inline for needs a comptime-known length (%s)", e->tok->file, e->tok->line, tname(t));
      }
    }
    if (len < 0 && l >= 0) len = l;
  }
  if (len < 0) die("%s:%d: inline for needs a bounded iterable", n->tok->file, n->tok->line);
  Loop L;
  memset(&L, 0, sizeof L);
  Res R;
  memset(&R, 0, sizeof R);
  R.ex = ex;
  char *lx = newl();
  int stopped = 0;
  L.label = n->label;
  L.brk = lx;
  L.res = &R;
  L.dbase = defers.n;
  L.kind = 0;
  for (int64_t k = 0; k < len; k++) {
    if (term) {
      stopped = 1;
      break;
    }
    Scope *bs = new_scope(s, NULL);
    for (int i = 0; i < ni && i < n->list2.n; i++) {
      Node *cp = n->list2.a[i];
      if (!strcmp(cp->s, "_")) continue;
      if (kind[i] == 2) {
        bind_cval(bs, cp->s, cv_int(start[i] + k, t_usize));
        continue;
      }
      if (kind[i] == 3) {
        char *r = tmp();
        emit("%s =l add %s, %lld", r, load(t_u64, rvs[i].op), (long long)k);
        char *sl = slot(t_usize);
        store(t_u64, r, sl);
        bind_local(bs, cp->s, t_usize, sl);
        continue;
      }
      if (kind[i] == 1) {
        bind_cval(bs, cp->s, cv_elem(&cvs[i], k));
        continue;
      }
      Val v = rvs[i];
      Type *t = v.t;
      Val e;
      if ((t->k == TY_STRUCT || t->k == TY_TUPLE) && t->ct) {
        Field *f = t->ct->fields.a[k];
        e = f->is_ct ? CK(*(CVal *)f->defcv) : LV(f->t, addp(addr_of(v), f->off));
      } else
        e = gen_index(v, CK(cv_int(k, t_usize)));
      cap_bind(bs, cp->s, cp->flags & F_REF, e);
    }
    char *lk = newl();
    L.cont = lk;
    L.cont_used = 0;
    L.up = loops;
    loops = &L;
    gen(n->b, bs, NULL);
    loops = L.up;
    if (term && !L.cont_used) {
      stopped = 1;
      break;
    }
    jmp(lk);
    label(lk);
  }
  if (!stopped && n->c) res_put(&R, gen(n->c, s, ex));
  int dead = term && !L.brk_used;
  jmp(lx);
  label(lx);
  if (dead) {
    emit("hlt");
    term = 1;
    return NORET();
  }
  if (!R.has) return VOIDV();
  return res_get(&R);
}
Type *loop_peer(Node *n, Scope *s) { /* peer-resolve break/else types of a loop expression */
  Node *sc = collect_node;
  collect_node = n;
  Type *pt = typeof_impl(n, s);
  collect_node = sc;
  if (pt && !type_incomplete(pt) && !type_is_ctonly(pt) && pt->k != TY_VOID && pt->k != TY_NORET) return pt;
  return NULL;
}
Val gen_for(Node *n, Scope *s, Type *ex) {
  if (!ex && n->c && !in_typeof) ex = loop_peer(n, s);
  int ni = n->list.n;
  Iter *it = xalloc(sizeof(Iter) * ni);
  char *len = NULL;
  for (int i = 0; i < ni; i++) {
    Node *e = n->list.a[i];
    if (e->k == N_RANGE) {
      it[i].range = 1;
      it[i].start = opnd(coerce(gen(e->a, s, t_usize), t_usize));
      CVal clo, chi;
      if (e->b && ceval(e->a, s, &clo) && clo.k == CV_INT && ceval(e->b, s, &chi) && chi.k == CV_INT)
        it[i].len = fmt("%lld", (long long)(chi.i - clo.i));
      else if (e->b) {
        char *hi = opnd(coerce(gen(e->b, s, t_usize), t_usize)), *l = tmp();
        emit("%s =l sub %s, %s", l, hi, it[i].start);
        it[i].len = l;
      }
    } else {
      Val v = gen(e, s, NULL);
      Type *t = v.t;
      if (v.ck && v.cv.k == CV_STR) {
        it[i].base = mat(v);
        it[i].et = t_u8;
        it[i].len = fmt("%d", v.cv.slen);
      } else if (t->k == TY_ARRAY) {
        it[i].base = addr_of(v);
        it[i].et = t->elem;
        it[i].len = fmt("%lld", (long long)t->len);
      } else if (t->k == TY_PTR && t->elem->k == TY_ARRAY) {
        it[i].base = opnd(v);
        it[i].et = t->elem->elem;
        it[i].len = fmt("%lld", (long long)t->elem->len);
      } else if (t->k == TY_SLICE) {
        char *a = addr_of(v);
        it[i].base = load(t_u64, a);
        it[i].len = load(t_u64, addp(a, 8));
        it[i].et = t->elem;
      } else if (t->k == TY_MPTR) {
        it[i].base = opnd(v);
        it[i].et = t->elem;
      } else
        die("%s:%d: cannot iterate over %s", e->tok->file, e->tok->line, tname(t));
    }
    if (!len && it[i].len) len = it[i].len;
  }
  if (!len) die("for loop needs a bounded iterable");
  if (!strcmp(len, "0")) return n->c ? gen(n->c, s, ex) : VOIDV(); /* comptime-known empty: body not analyzed */
  Loop L;
  memset(&L, 0, sizeof L);
  Res R;
  memset(&R, 0, sizeof R);
  R.ex = ex;
  if (n == collect_node && in_typeof) {
    R.collect = 1;
    collect_node = NULL;
  } else if (in_typeof && ex_partial(ex))
    R.collect = 1;
  char *lc = newl(), *lb = newl(), *lk = newl(), *le = newl(), *lx = newl();
  L.label = n->label;
  L.brk = lx;
  L.cont = lk;
  L.res = &R;
  L.dbase = defers.n;
  L.kind = 0;
  char *is = slot(t_usize);
  store(t_u64, "0", is);
  jmp(lc);
  label(lc);
  char *i = load(t_u64, is), *c = tmp();
  emit("%s =w cultl %s, %s", c, i, len);
  br(c, lb, le);
  label(lb);
  Scope *bs = new_scope(s, NULL);
  for (int k = 0; k < ni && k < n->list2.n; k++) {
    Node *cp = n->list2.a[k];
    if (!strcmp(cp->s, "_")) continue;
    if (it[k].range) {
      char *v = tmp();
      emit("%s =l add %s, %s", v, it[k].start, i);
      bind_val(bs, cp->s, V(t_usize, v));
      continue;
    }
    char *o = tmp(), *a = tmp();
    emit("%s =l mul %s, %d", o, i, tsize(it[k].et));
    emit("%s =l add %s, %s", a, it[k].base, o);
    cap_bind(bs, cp->s, cp->flags & F_REF, LV(it[k].et, a));
  }
  L.up = loops;
  loops = &L;
  gen(n->b, bs, NULL);
  loops = L.up;
  jmp(lk);
  label(lk);
  {
    char *i2 = load(t_u64, is), *i3 = tmp();
    emit("%s =l add %s, 1", i3, i2);
    store(t_u64, i3, is);
  }
  jmp(lc);
  label(le);
  if (n->c) {
    Val ev = gen(n->c, s, ex);
    res_put(&R, ev);
  }
  jmp(lx);
  label(lx);
  if (!n->c && !R.has) return VOIDV();
  return res_get(&R);
}
int item_match_ct(Node *it, Scope *s, CVal *cond, Type *ct) {
  CVal v;
  if (it->k == N_RANGE) {
    CVal lo, hi;
    ceval_force(it->a, s, &lo);
    ceval_force(it->b, s, &hi);
    return cond->i >= lo.i && cond->i <= hi.i;
  }
  Type *rt = cond->k == CV_INT ? cv_typeof(cond) : NULL;
  (void)ct;
  if (!ceval_rt(it, s, rt, &v)) die("%s:%d: switch item not comptime-known", it->tok->file, it->tok->line);
  return cv_match(cond, &v);
}
void ct_prong_bind(Node *pr, Scope *ps, CVal *cc) {
  int isu = cc->k == CV_AGG && cc->t->k == TY_UNION;
  if (pr->cap) bind_cval(ps, pr->cap, isu ? *cc->el[0] : *cc);
  if (pr->cap2) {
    if (isu) {
      Field *f = cc->t->ct->fields.a[cc->i];
      CVal tv = {0};
      tv.k = CV_INT;
      tv.i = f->val;
      tv.t = cc->t->ct->tag;
      bind_cval(ps, pr->cap2, tv);
    } else
      bind_cval(ps, pr->cap2, *cc);
  }
}
int has_cont_to(Node *n, const char *l, int depth) { /* does `continue :l` occur inside n? */
  if (!n || depth > 200) return 0;
  if (n->k == N_CONTINUE && n->label && !strcmp(n->label, l)) return 1;
  if (has_cont_to(n->a, l, depth + 1) || has_cont_to(n->b, l, depth + 1) || has_cont_to(n->c, l, depth + 1) ||
      has_cont_to(n->d, l, depth + 1))
    return 1;
  for (int i = 0; i < n->list.n; i++)
    if (has_cont_to(n->list.a[i], l, depth + 1)) return 1;
  for (int i = 0; i < n->list2.n; i++)
    if (has_cont_to(n->list2.a[i], l, depth + 1)) return 1;
  return 0;
}
Val gen_switch(Node *n, Scope *s, Type *ex) {
  CVal cc;
  Val pre = {0};
  int has_pre = 0, known = ceval(n->a, s, &cc);
  if (!known && n->a->k == N_CALL) { /* inline calls can yield comptime-known results */
    pre = rv(gen(n->a, s, NULL));
    has_pre = 1;
    if (pre.ck && pre.cv.k != CV_UNDEF) {
      cc = pre.cv;
      known = 1;
    }
  }
  if (known && (!n->label || type_is_ctonly(cv_typeof(&cc)) || !has_cont_to(n, n->label, 0))) {
    Type *ct = cc.t;
    Node *sel = NULL, *els = NULL;
    for (int i = 0; i < n->list.n && !sel; i++) {
      Node *pr = n->list.a[i];
      if (pr->flags & F_ELSE) {
        els = pr;
        continue;
      }
      for (int j = 0; j < pr->list.n; j++)
        if (item_match_ct(pr->list.a[j], s, &cc, ct)) {
          sel = pr;
          break;
        }
    }
    if (!sel) sel = els;
    if (!sel) die("comptime switch: no prong matched");
    Scope *ps = new_scope(s, NULL);
    ct_prong_bind(sel, ps, &cc);
    if (!n->label) return gen(sel->b, ps, ex);
    /* labeled switch on a comptime-only operand: behaves like a labeled block around the chosen prong */
    Loop L;
    memset(&L, 0, sizeof L);
    Res R;
    memset(&R, 0, sizeof R);
    R.ex = ex;
    L.label = n->label;
    L.brk = newl();
    L.res = &R;
    L.dbase = defers.n;
    L.kind = 1;
    L.up = loops;
    loops = &L;
    Val v = gen(sel->b, ps, ex);
    loops = L.up;
    if (!term && v.t->k != TY_NORET) res_put(&R, v);
    jmp(L.brk);
    label(L.brk);
    return res_get(&R);
  }
  int anyref = 0;
  for (int i = 0; i < n->list.n; i++)
    if (((Node *)n->list.a[i])->capref) anyref = 1;
  Val lvv = {0};
  int uselv = 0;
  if (has_pre)
    lvv = pre;
  else {
    lvv = gen(n->a, s, NULL);
    if (anyref && !n->label && lvv.lv && !lvv.bf && !lvv.ck) uselv = 1;
  }
  Val cv = uselv ? lvv : rv(lvv);
  Type *ct = cv.t;
  if (ct->k == TY_CINT) {
    cv = coerce(cv, t_i64);
    ct = t_i64;
  }
  Res R;
  memset(&R, 0, sizeof R);
  R.ex = ex;
  if ((!ex || ex_partial(ex)) && in_typeof)
    R.collect = 1;
  else if (!ex) {
    Type *pt = typeof_impl(n, s);
    if (pt && !type_incomplete(pt) && !type_is_ctonly(pt) && pt->k != TY_VOID) R.ex = ex = pt;
  }
  Loop L;
  memset(&L, 0, sizeof L);
  char *sw = uselv ? cv.op : slot(ct), *ld = newl(), *lx = newl();
  if (!uselv) put(cv, ct, sw);
  jmp(ld);
  label(ld);
  L.label = n->label;
  L.kind = 2;
  L.swslot = sw;
  L.swdisp = ld;
  L.swt = ct;
  L.brk = lx;
  L.res = &R;
  L.dbase = defers.n;
  int isu = ct->k == TY_UNION;
  Type *tagt = isu ? ct->ct->tag : ct;
  int pk = !isu && is_packed(ct);
  Type *pkt = pk ? int_type(bits_of(ct), 0) : NULL; /* packed struct operand: compare backing ints */
  char *x = isu ? load(tagt, addp(sw, union_tag_off(ct))) : pk ? load(pkt, sw) : load(ct, sw);
  /* expand prongs into cases; inline prongs get one case per (comptime-known) value */
  typedef struct {
    Node *pr;
    int isct;
    CVal v;
    char *lab;
  } Case;
  Vec cases = {0};
  int elsei = -1;
  for (int i = 0; i < n->list.n; i++) {
    Node *pr = n->list.a[i];
    if (pr->flags & F_INLINE) {
      if (pr->flags & F_ELSE) {
        int nvals;
        if (tagt->k == TY_ENUM) {
          layout(tagt->ct);
          nvals = tagt->ct->fields.n;
        } else if (tagt->k == TY_BOOL)
          nvals = 2;
        else if (tagt->k == TY_INT && tagt->bits <= 10)
          nvals = 1 << tagt->bits;
        else
          die("%s:%d: inline else needs an enum, bool, small int or tagged union operand", pr->tok->file,
              pr->tok->line);
        for (int k = 0; k < nvals; k++) {
          Field fb = {0};
          Field *f = &fb;
          if (tagt->k == TY_ENUM)
            f = tagt->ct->fields.a[k];
          else
            fb.val = (tagt->k == TY_INT && tagt->sign) ? k - (1 << (tagt->bits - 1)) : k;
          int covered = 0;
          for (int j = 0; j < n->list.n && !covered; j++) {
            Node *op = n->list.a[j];
            if (op->flags & F_ELSE) continue;
            for (int m = 0; m < op->list.n; m++) {
              Node *it = op->list.a[m];
              CVal iv;
              if (it->k == N_RANGE) continue;
              if (ceval_rt(it, s, tagt, &iv) && iv.k == CV_INT && iv.i == f->val) {
                covered = 1;
                break;
              }
            }
          }
          if (covered) continue;
          Case *c = xalloc(sizeof *c);
          c->pr = pr;
          c->isct = 1;
          c->v = tagt->k == TY_BOOL ? cv_bool((int)f->val) : cv_int(f->val, tagt);
          vpush(&cases, c);
        }
      } else
        for (int m = 0; m < pr->list.n; m++) {
          Node *it = pr->list.a[m];
          if (it->k == N_RANGE) {
            CVal lo, hi;
            if (!ceval_rt(it->a, s, NULL, &lo) || !ceval_rt(it->b, s, NULL, &hi) || lo.k != CV_INT || hi.k != CV_INT)
              die("%s:%d: inline prong range must be comptime-known", it->tok->file, it->tok->line);
            if (hi.i - lo.i > 100000) die("%s:%d: inline prong range too large", it->tok->file, it->tok->line);
            for (i128 q = lo.i; q <= hi.i; q++) {
              Case *c = xalloc(sizeof *c);
              c->pr = pr;
              c->isct = 1;
              c->v = cv_int(q, tagt);
              vpush(&cases, c);
            }
            continue;
          }
          Case *c = xalloc(sizeof *c);
          c->pr = pr;
          c->isct = 1;
          if (!ceval_rt(it, s, tagt, &c->v))
            die("%s:%d: inline prong items must be comptime-known values", it->tok->file, it->tok->line);
          c->v = ccoerce(c->v, tagt);
          vpush(&cases, c);
        }
      continue;
    }
    Case *c = xalloc(sizeof *c);
    c->pr = pr;
    if (pr->flags & F_ELSE) elsei = cases.n;
    vpush(&cases, c);
  }
  for (int i = 0; i < cases.n; i++) {
    Case *c = cases.a[i];
    Node *pr = c->pr;
    c->lab = newl();
    if (i == elsei) continue;
    if (c->isct) {
      char *nx = newl(), *cmp = tmp();
      emit("%s =w ceq%c %s, %lld", cmp, qc(tagt), x, (long long)c->v.i);
      br(cmp, c->lab, nx);
      label(nx);
      continue;
    }
    for (int j = 0; j < pr->list.n; j++) {
      Node *it = pr->list.a[j];
      char *nx = newl(), *cmp = tmp();
      if (it->k == N_RANGE) {
        Val lo = coerce(gen(it->a, s, tagt), tagt), hi = coerce(gen(it->b, s, tagt), tagt);
        char *c1 = tmp(), *c2 = tmp();
        int sg = tagt->k == TY_INT && tagt->sign;
        emit("%s =w c%s%c %s, %s", c1, sg ? "sge" : "uge", qc(tagt), x, opnd(lo));
        emit("%s =w c%s%c %s, %s", c2, sg ? "sle" : "ule", qc(tagt), x, opnd(hi));
        emit("%s =w and %s, %s", cmp, c1, c2);
      } else {
        Val iv = coerce(gen(it, s, tagt), tagt);
        if (pk) {
          char *sl = slot(ct);
          put(iv, ct, sl);
          emit("%s =w ceq%c %s, %s", cmp, qc(pkt), x, load(pkt, sl));
        } else
          emit("%s =w ceq%c %s, %s", cmp, qc(tagt), x, opnd(iv));
      }
      br(cmp, c->lab, nx);
      label(nx);
    }
  }
  if (elsei >= 0)
    jmp(((Case *)cases.a[elsei])->lab);
  else {
    emit("hlt");
    term = 1;
  }
  L.up = loops;
  loops = &L;
  for (int i = 0; i < cases.n; i++) {
    Case *c = cases.a[i];
    Node *pr = c->pr;
    label(c->lab);
    Scope *ps = new_scope(s, NULL);
    if (isu && !pr->cap && !c->isct &&
        !(pr->flags & F_ELSE)) { /* prong whose fields all have noreturn payloads is unreachable (not analyzed) */
      int allnr = pr->list.n > 0;
      for (int j = 0; j < pr->list.n && allnr; j++) {
        CVal iv;
        Field *f = NULL;
        Node *it = pr->list.a[j];
        if (it->k != N_RANGE && ceval(it, s, &iv)) {
          if (iv.k == CV_ENUMLIT)
            f = find_field(ct->ct, iv.s);
          else if (iv.k == CV_INT)
            for (int k = 0; k < ct->ct->fields.n; k++) {
              Field *ff = ct->ct->fields.a[k];
              if (ff->val == (int64_t)iv.i) f = ff;
            }
        }
        if (!f || f->t->k != TY_NORET) allnr = 0;
      }
      if (allnr) {
        emit("hlt");
        term = 1;
        continue;
      }
    }
    if (pr->cap) {
      if (isu) {
        Field *f = NULL;
        if (c->isct) {
          for (int k = 0; k < ct->ct->fields.n; k++) {
            Field *ff = ct->ct->fields.a[k];
            if (ff->val == (int64_t)c->v.i) f = ff;
          }
        } else if (!(pr->flags & F_ELSE)) {
          Node *it = pr->list.a[0];
          CVal iv;
          ceval(it, s, &iv);
          f = iv.k == CV_ENUMLIT ? find_field(ct->ct, iv.s) : NULL;
          if (!f && iv.k == CV_INT)
            for (int k = 0; k < ct->ct->fields.n; k++) {
              Field *ff = ct->ct->fields.a[k];
              if (ff->val == (int64_t)iv.i) f = ff;
            }
        }
        if (f && f->t->k == TY_NORET) {
          emit("hlt");
          term = 1;
          continue;
        } /* payload of type noreturn: prong unreachable */
        if (f)
          cap_bind(ps, pr->cap, pr->capref, LV(f->t, sw));
        else
          cap_bind(ps, pr->cap, pr->capref, LV(ct, sw));
      } else if (c->isct && !pr->capref)
        bind_cval(ps, pr->cap, c->v);
      else
        cap_bind(ps, pr->cap, pr->capref, LV(ct, sw));
    }
    if (pr->cap2) {
      if (c->isct)
        bind_cval(ps, pr->cap2, c->v);
      else
        bind_val(ps, pr->cap2, V(tagt, x));
    }
    Val v = gen(pr->b, ps, ex);
    res_put(&R, v);
    jmp(lx);
  }
  loops = L.up;
  label(lx);
  return res_get(&R);
}
Val gen_return(Node *n, Scope *s) {
  Val v;
  if (n->a)
    v = gen(n->a, s, fret);
  else
    v = VOIDV();
  return ret_val(v, !n->a);
}
Val ret_val(Val v, int noval) {
  if (v.t->k == TY_NORET) return v;
  if (inl && in_typeof > inl->level) {
    term = 1;
    return NORET();
  } /* dry run inside an inline body: don't touch the frame */
  if (inl) {
    if (noval && fret->k == TY_ERRU) {
      char *sl = slot(fret);
      store(t_u16, "0", sl);
      v = V(fret, sl);
    } else
      v = coerce(v, fret);
    if (v.ck && v.cv.k != CV_UNDEF) {
      if (inl->nret && !cval_eq(&inl->ckv, &v.cv)) inl->allck = 0;
      inl->ckv = v.cv;
    } else
      inl->allck = 0;
    inl->nret++;
    run_defers(inl->dbase, NULL);
    if (!term) {
      res_put(inl->res, v);
      jmp(inl->lx);
    }
    term = 1;
    return NORET();
  }
  if (noval && fret->k == TY_ERRU) {
    char *sl = slot(fret);
    store(t_u16, "0", sl);
    v = V(fret, sl);
  } else
    v = coerce(v, fret);
  if (is_aggr(fret)) {
    put(v, fret, fsret);
    if (fret->k == TY_ERRU && have_errdefer(0)) {
      char *e = load(t_u16, fsret), *le = newl(), *lo = newl();
      br(e, le, lo);
      label(le);
      run_defers(0, e);
      if (!term) emit("ret");
      term = 1;
      label(lo);
      run_defers(0, NULL);
      if (!term) emit("ret");
      term = 1;
    } else {
      run_defers(0, NULL);
      if (!term) emit("ret");
    }
  } else if (fret->k == TY_VOID || tsize(fret) == 0) {
    run_defers(0, NULL);
    if (!term) emit("ret");
  } else {
    char *o = opnd(v);
    run_defers(0, NULL);
    if (!term) emit("ret %s", o);
  }
  term = 1;
  return NORET();
}
Val gen_try(Node *n, Scope *s, Type *ex) {
  Type *pe = ex && ex->k == TY_ERRU && n->a->k == N_CALL && n->a->a->k == N_ENUMLIT ? ex->elem
                                                                                    : ex; /* `return try .init(..)` */
  Val v = gen(n->a, s, pe && pe->k != TY_ERRU && pe->k != TY_ANYTYPE ? erru_of(pe) : NULL);
  if (v.t->k == TY_ERRSET) {
    if (fret->k == TY_ERRU && is_inferred_eset(fret->ret)) eset_add_set(fret->ret, v.t);
    char *e = opnd(v);
    store(t_u16, e, fsret);
    run_defers(0, e);
    emit("ret");
    term = 1;
    return NORET();
  }
  if (fret->k == TY_ERRU && is_inferred_eset(fret->ret) && v.t->k == TY_ERRU) eset_add_set(fret->ret, eset_of(v.t));
  if (v.t->k != TY_ERRU)
    return v; /* lenient: only reachable in code real Zig would not analyze (e.g. catch of an empty inferred error set) */
  char *a = addr_of(v), *e = load(t_u16, a), *le = newl(), *lo = newl();
  br(e, le, lo);
  label(le);
  if (fret->k == TY_ERRU) {
    store(t_u16, e, fsret);
    run_defers(0, e);
    if (!term) emit("ret");
  } else if (fret->k == TY_ERRSET) {
    run_defers(0, e);
    if (!term) emit("ret %s", e);
  } else
    emit("hlt"); /* error set must be empty (inferred) */
  term = 1;
  label(lo);
  if (v.t->elem == t_void) return VOIDV();
  return LV(v.t->elem, addp(a, erru_off(v.t)));
}
Val gen_catch(Node *n, Scope *s, Type *ex) {
  Val v = gen(n->a, s, ex && ex->k != TY_ERRU && ex->k != TY_ANYTYPE ? erru_of(ex) : NULL);
  if (v.t->k != TY_ERRU && v.ck) { /* comptime-known error union value */
    if (v.cv.k == CV_ERR) {
      Scope *cs = new_scope(s, NULL);
      if (n->cap) bind_cval(cs, n->cap, v.cv);
      return gen(n->b, cs, ex);
    }
    return ex ? coerce(v, ex) : v;
  }
  if (v.t->k == TY_ERRSET) {
    Scope *cs = new_scope(s, NULL);
    if (n->cap) bind_val(cs, n->cap, V(v.t, opnd(v)));
    return gen(n->b, cs, ex);
  } /* operand is a bare error set: always the error path */
  if (v.t->k != TY_ERRU)
    die("%s:%d: catch on non error union %s (ck=%d)", n->tok->file, n->tok->line, tname(v.t), v.ck);
  Res R;
  memset(&R, 0, sizeof R);
  R.ex = ex ? ex : v.t->elem;
  int discard = !ex && n->b->k == N_BLOCK && n->b->list.n == 0 && !n->b->label; /* `x catch {}`: result is void */
  if (discard)
    R.ex = t_void;
  else if (!ex && in_typeof) {
    R.ex = NULL;
    R.collect = 1;
  } else if (!ex) {
    Scope *cs0 = new_scope(s, NULL);
    if (n->cap) bind_val(cs0, n->cap, V(eset_of(v.t), "0"));
    Type *bt = typeof_impl(n->b, cs0), *p = bt && bt->k != TY_NORET ? peer_t(v.t->elem, bt) : NULL;
    if (p && p->k != TY_CINT && p->k != TY_VOID) R.ex = p;
  }
  char *a = addr_of(v), *e = load(t_u16, a), *le = newl(), *lo = newl(), *lx = newl();
  br(e, le, lo);
  label(lo);
  res_put(&R, v.t->elem == t_void || discard ? VOIDV() : rv(LV(v.t->elem, addp(a, erru_off(v.t)))));
  jmp(lx);
  label(le);
  Scope *cs = new_scope(s, NULL);
  if (n->cap) bind_val(cs, n->cap, V(eset_of(v.t), e));
  res_put(&R, gen(n->b, cs, R.collect ? NULL : R.t ? R.t : R.ex));
  jmp(lx);
  label(lx);
  return res_get(&R);
}
Val gen_orelse(Node *n, Scope *s, Type *ex) {
  if (n->a->k == N_CALL && n->b->k == N_BUILTIN &&
      !strcmp(n->b->s, "compileError")) { /* `f() orelse @compileError(..)`: fold comptime-known lhs */
    CVal c;
    if (ceval_force(n->a, s, &c) && c.k != CV_UNDEF) {
      if (c.k == CV_NULL) return gen(n->b, s, ex);
      Val r = CK(c);
      return ex ? coerce(r, ex) : r;
    }
  }
  Val v = gen(n->a, s, ex ? opt_of(ex) : NULL);
  if (v.ck && v.cv.k == CV_NULL && v.cv.slen <= 0) return gen(n->b, s, ex);
  if (v.ck && v.t->k != TY_OPT) return v; /* comptime-known non-null payload */
  if (v.t->k != TY_OPT) die("%s:%d: orelse on non optional", n->tok->file, n->tok->line);
  Res R;
  memset(&R, 0, sizeof R);
  R.ex = ex ? ex : v.t->elem;
  if (!ex && in_typeof) {
    R.ex = NULL;
    R.collect = 1;
  } else if (!ex) {
    Type *bt = typeof_impl(n->b, s), *p = bt && bt->k != TY_NORET ? peer_t(v.t->elem, bt) : NULL;
    if (p && p->k != TY_CINT) R.ex = p;
  }
  char *pv = opt_is_ptr(v.t) ? opnd(v) : NULL, *lh = newl(), *ln = newl(), *lx = newl();
  if (pv) {
    char *h = tmp();
    emit("%s =w cnel %s, 0", h, pv);
    br(h, lh, ln);
  } else
    br(opt_has(v), lh, ln);
  label(lh);
  res_put(&R, rv(opt_payload(v, pv)));
  jmp(lx);
  label(ln);
  res_put(&R, gen(n->b, s, R.collect ? NULL : R.t ? R.t : R.ex));
  jmp(lx);
  label(lx);
  return res_get(&R);
}
