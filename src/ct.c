#include "ct_int.h"

int xs;
char *xlabel;
CVal xval;    /* pending control flow (R_CF) */
int ct_force; /* >0: comptime context (calls/loops/side effects allowed) */
long ct_steps;
Type *cur_rt; /* return type of the function being interpreted */
Type *brt;    /* result type for the builtin being evaluated */
int ct_trace = -1;
Type *t_splat; /* marker type for @splat values without a result type */
char *lrt_l[64];
Type *lrt_t[64];
int lrt_n; /* labeled-block result types */
Node *ev_cur;
const char *ct_cur_loc(void) {
  return ev_cur && ev_cur->tok ? fmt("%s:%d", ev_cur->tok->file, ev_cur->tok->line) : "?";
}
CVal unwrap_some_null(CVal v) {
  v.slen--;
  if (v.t && v.t->k == TY_OPT) v.t = v.t->elem;
  return v;
}
AnonE *anon_tab[ANON_HB];
AnonE *anon_ct_tab[ANON_CT_HB];

/* ---------- member access ---------- */
int ceval_member(CVal base, const char *name, CVal *out) {
  if (base.k == CV_TYPE) {
    Type *t = base.t;
    if (t->ct) {
      Decl *d = find_decl(t->ct, name);
      if (d) {
        resolve_decl(d);
        if (d->kind == D_CONST || d->kind == D_FN) {
          *out = d->cv;
          return 1;
        }
        return 0;
      }
      if (t->k == TY_ENUM) {
        int64_t v;
        if (enum_val(t, name, &v)) {
          *out = cv_int(v, t);
          return 1;
        }
      }
      if (t->k == TY_UNION && t->ct->tagged) {
        int64_t v;
        layout(t->ct);
        if (enum_val(t, name, &v)) {
          *out = cv_int(v, t->ct->tag);
          return 1;
        }
      }
    }
    if (t->k == TY_ERRSET) {
      CVal v = {0};
      v.k = CV_ERR;
      v.i = err_id(name);
      v.t = t;
      *out = v;
      return 1;
    }
    return 0;
  }
  if (base.k == CV_STR) {
    if (!strcmp(name, "len")) {
      *out = cv_int(base.slen, t_usize);
      return 1;
    }
    if (!strcmp(name, "ptr")) {
      CVal p = {0};
      p.k = CV_PTR;
      p.base = box(base);
      p.idx = 0;
      p.t = mptr_to(t_u8, 1, 1, 0);
      *out = p;
      return 1;
    }
    return 0;
  }
  if (base.k == CV_SLICE) {
    if (!strcmp(name, "len")) {
      *out = cv_int(base.slen, t_usize);
      return 1;
    }
    if (!strcmp(name, "ptr")) {
      CVal p = base;
      p.k = CV_PTR;
      p.t = mptr_to(base.t ? base.t->elem : t_u8, base.t ? base.t->isconst : 1, 0, 0);
      *out = p;
      return 1;
    }
    return 0;
  }
  if (base.k == CV_PTR) {
    if (!base.base) return 0;
    if (base.t && base.t->k == TY_PTR && base.t->elem->k == TY_ARRAY && !is_vec(base.t->elem)) {
      if (!strcmp(name, "len")) {
        *out = cv_int(base.t->elem->len, t_usize);
        return 1;
      }
      if (!strcmp(name, "ptr")) {
        CVal p = base;
        if (p.idx < 0) p.idx = 0;
        p.t = mptr_to(base.t->elem->elem, base.t->isconst, 0, 0);
        *out = p;
        return 1;
      }
    }
    CVal *c = deref_cell(&base);
    if (base.t && base.t->k == TY_PTR) return c ? ceval_member(*c, name, out) : 0;
    return 0;
  }
  if (base.k == CV_UNDEF && base.t && base.t->k == TY_ARRAY && !strcmp(name, "len")) {
    *out = cv_int(base.t->len, t_usize);
    return 1;
  }
  if (base.k == CV_AGG) {
    Type *t = base.t;
    if (t->k == TY_ARRAY) {
      if (!strcmp(name, "len")) {
        *out = cv_int(t->len, t_usize);
        return 1;
      }
      return 0;
    }
    if (t->k == TY_UNION) {
      int fi = field_index(t, name);
      if (fi >= 0) {
        if (fi != base.i) die("access of inactive union field '%s' at comptime", name);
        *out = *base.el[0];
        return 1;
      }
    } else if (is_struct_like(t)) {
      int fi = field_index(t, name);
      if (fi >= 0) {
        *out = *base.el[fi];
        return 1;
      }
      if (!strcmp(name, "len") && is_tuple_type(t)) {
        *out = cv_int(base.n, t_usize);
        return 1;
      }
    }
    if (t->ct) {
      Decl *d = find_decl(t->ct, name);
      if (d) {
        resolve_decl(d);
        if (d->kind == D_CONST || d->kind == D_FN) {
          *out = d->cv;
          return 1;
        }
      }
    }
    return 0;
  }
  return 0;
}

/* ---------- helpers for the evaluator ---------- */
void step(void) {
  if (++ct_steps > 200000000L) die("comptime evaluation exceeded the branch quota");
}
void bind_cap(Scope *s, char *name, CVal v) {
  if (name && strcmp(name, "_")) bind_cval(s, name, cv_copy(v));
}
CVal mk_union(Type *u, const char *field, CVal payload) {
  CVal a = agg_new(u);
  a.i = field_index(u, field);
  if (a.i < 0) die("no field %s in %s", field, tname(u));
  *a.el[0] = ccoerce(payload, field_at(u, (int)a.i)->t);
  return a;
}
int ev_block(Node *n, Scope *s, CVal *out) {
  Scope *bs = new_scope(s, NULL);
  Vec dfr = {0};
  int r = R_OK;
  CVal v = cv_void();
  for (int i = 0; i < n->list.n; i++) {
    Node *st = n->list.a[i];
    if (st->k == N_DEFER) {
      vpush(&dfr, st->a);
      continue;
    }
    if (st->k == N_ERRDEFER) continue;
    r = ev(st, bs, &v);
    if (r != R_OK) break;
  }
  for (int i = dfr.n - 1; i >= 0; i--) {
    int sxs = xs;
    char *sl = xlabel;
    CVal sv = xval;
    CVal dv;
    int rr = ev(dfr.a[i], bs, &dv);
    xs = sxs;
    xlabel = sl;
    xval = sv;
    if (rr == R_FAIL) r = R_FAIL;
  }
  if (r == R_CF && xs == X_BRK && n->label && xlabel && !strcmp(xlabel, n->label)) {
    xs = X_NONE;
    *out = xval;
    return R_OK;
  }
  if (r != R_OK) return r;
  *out = cv_void();
  return R_OK;
}
Type *rt_static_type(Scope *s, Node *n) { /* static type of a runtime local / field chain, or NULL */
  if (n->k == N_IDENT) {
    Sym *y;
    Decl *d;
    if (!lookup(s, n->s, &y, &d)) return NULL;
    if (y && y->k == S_LOCAL) return y->t;
    return NULL;
  }
  if (n->k == N_FIELD) {
    Type *t = rt_static_type(s, n->a);
    if (!t) return NULL;
    if (t->k == TY_PTR) t = t->elem;
    if ((t->k == TY_STRUCT || t->k == TY_TUPLE) && t->ct) {
      layout(t->ct);
      Field *f = find_field(t->ct, n->s);
      return f ? f->t : NULL;
    }
  }
  return NULL;
}
int ct_field_of(Scope *s, Node *n, CVal *out) {
  Type *t = rt_static_type(s, n->a);
  if (!t) return 0;
  if (t->k == TY_PTR) t = t->elem;
  if ((t->k != TY_STRUCT && t->k != TY_TUPLE) || !t->ct) return 0;
  layout(t->ct);
  Field *f = find_field(t->ct, n->s);
  if (!f || !f->is_ct) return 0;
  *out = *(CVal *)f->defcv;
  return 1;
}
int is_local_array(Scope *s, Node *n, Type **at) {
  Sym *y;
  Decl *d;
  if (n->k != N_IDENT || !lookup(s, n->s, &y, &d)) return 0;
  Type *t = NULL;
  if (y && y->k == S_LOCAL)
    t = y->t;
  else if (d && d->state == 2 && d->kind == D_VAR)
    t = d->t;
  if (!t) return 0;
  if (t->k == TY_PTR && t->elem->k == TY_ARRAY) t = t->elem;
  if (t->k != TY_ARRAY) return 0;
  *at = t;
  return 1;
}
int fn_ret_type(Decl *fd, Scope *fs, Type **rt) {
  Node *f = fd->node;
  CVal tv;
  ct_force++;
  int r = ev(f->a, fs, &tv);
  ct_force--;
  if (r != R_OK || tv.k != CV_TYPE) return 0;
  *rt = tv.t;
  if (f->flags & F_INFERR) *rt = erru_of2(*rt, fn_is_generic(f) ? NULL : decl_iset(fd));
  return 1;
}
int fn_returns_ctonly(Decl *fd) {
  Node *f = fd->node;
  if (!f->a) return 0;
  {
    Node *r = f->a;
    while ((r->k == N_TOPT || r->k == N_TERRU) && (r->k == N_TOPT ? r->a : r->b)) r = r->k == N_TOPT ? r->a : r->b;
    if (r->k == N_IDENT && (!strcmp(r->s, "type") || !strcmp(r->s, "comptime_int") || !strcmp(r->s, "comptime_float")))
      return 1;
  }
  if (fn_is_generic(f)) return 0;
  CVal tv;
  int sf = ct_force;
  ct_force = 0;
  int sxs = xs;
  int r = ev(f->a, fd->ct->scope, &tv);
  ct_force = sf;
  xs = sxs;
  return r == R_OK && tv.k == CV_TYPE && type_is_ctonly(tv.t);
}
int fn_takes_ctonly(Decl *fd) {
  Node *f = fd->node;
  for (int i = 0; i < f->list.n; i++) {
    Node *p = f->list.a[i];
    if (!p->a || (p->flags & (F_ANYTYPE | F_VARARGS))) break;
    if (p->a->k == N_IDENT && !strcmp(p->a->s, "type")) break;
    CVal tv;
    int sf = ct_force;
    ct_force = 0;
    int sxs = xs;
    int r = ev(p->a, fd->ct->scope, &tv);
    ct_force = sf;
    xs = sxs;
    if (r == R_OK && tv.k == CV_TYPE && type_is_ctonly(tv.t)) return 1;
    if (p->flags & F_COMPTIME) break;
  }
  return 0;
}
int self_arg(Node *recv, Scope *s, Scope *ps, CVal base, Node *param, CVal *out) {
  /* method call receiver: pass by pointer or by value according to the parameter type */
  Type *pt = NULL;
  if (param && param->a && !(param->flags & F_ANYTYPE)) {
    CVal tv;
    ct_force++;
    int r = ev(param->a, ps, &tv);
    ct_force--;
    if (r == R_OK && tv.k == CV_TYPE) pt = tv.t;
  }
  int want_ptr = pt && pt->k == TY_PTR && !(base.k == CV_PTR);
  if (want_ptr) {
    CVal *cell;
    int r = clval(recv, s, &cell);
    if (r == R_OK) {
      CVal p = {0};
      p.k = CV_PTR;
      p.base = cell;
      p.idx = -1;
      p.t = pt;
      *out = p;
      return R_OK;
    }
    CVal p = {0};
    p.k = CV_PTR;
    p.base = box(cv_copy(base));
    p.idx = -1;
    p.t = pt;
    *out = p;
    return R_OK;
  }
  if (base.k == CV_PTR && pt && pt->k != TY_PTR && base.t && base.t->k == TY_PTR) {
    CVal *c = deref_cell(&base);
    if (!c) return R_FAIL;
    *out = *c;
    return R_OK;
  }
  *out = base;
  return R_OK;
}
int ev_call_fn(Node *n, Scope *s, CVal fnv, int has_self, CVal self, Node *recv, CVal *out) {
  if (fnv.k != CV_FN) return R_FAIL;
  Decl *fd = fnv.fn;
  Node *f = fd->node;
  if (!ct_force && !fn_returns_ctonly(fd) && !fn_takes_ctonly(fd)) {
    int allct = (f->flags & F_INLINE) && f->list.n > 0;
    for (int i = 0; allct && i < f->list.n; i++)
      if (!(((Node *)f->list.a[i])->flags & F_COMPTIME)) allct = 0;
    if (!allct || !f->a || f->a->k != N_IDENT || (strcmp(f->a->s, "bool") && strcmp(f->a->s, "type"))) return R_FAIL;
    ct_force++;
    int r = ev_call_fn(n, s, fnv, has_self, self, recv, out);
    ct_force--;
    return r;
  }
  int np = f->list.n, na = n->list.n + has_self;
  CVal *args = xalloc(sizeof(CVal) * (na + 1));
  Scope *ps = new_scope(fd->ct->scope, NULL); /* to evaluate parameter types for result-typed args */
  for (int i = 0; i < na; i++) {
    Node *p = i < np ? f->list.a[i] : NULL;
    if (i == 0 && has_self) {
      int r = (recv ? self_arg(recv, s, ps, self, p, &args[0]) : (args[0] = self, R_OK));
      if (r != R_OK) return r;
      if (p && p->s) bind_cval(ps, p->s, args[0]);
      continue;
    }
    Node *an = n->list.a[i - has_self];
    Type *pt = NULL;
    if (p && p->a && !(p->flags & (F_ANYTYPE | F_VARARGS))) {
      CVal tv;
      ct_force++;
      int r = ev(p->a, ps, &tv);
      ct_force--;
      if (r == R_OK && tv.k == CV_TYPE) pt = tv.t;
    }
    EVR(an, s, pt, &args[i]);
    if (p && p->s) bind_cval(ps, p->s, pt ? ccoerce(args[i], pt) : args[i]);
  }
  return ct_call(fd, args, na, out);
}
int ev_call(Node *n, Scope *s, CVal *out) {
  Node *cal = n->a;
  CVal fnv;
  int has_self = 0;
  CVal self = {0};
  if (cal->k == N_ENUMLIT) return R_FAIL; /* decl literal call needs a result type (ev_rt) */
  if (cal->k == N_FIELD) {
    CVal base;
    int r = ev(cal->a, s, &base);
    if (r == R_CF) return r;
    if (r != R_OK) return R_FAIL;
    if (base.k == CV_TYPE) {
      if (!ceval_member(base, cal->s, &fnv)) return R_FAIL;
    } else {
      Type *bt = cv_typeof(&base);
      if (bt->k == TY_PTR) bt = bt->elem;
      Decl *d = bt->ct ? find_decl(bt->ct, cal->s) : NULL;
      if (d) {
        resolve_decl(d);
        if (d->cv.k != CV_FN) return R_FAIL;
        fnv = d->cv;
        has_self = 1;
        self = base;
      } else if (!ceval_member(base, cal->s, &fnv))
        return R_FAIL;
    }
  } else
    EV(cal, s, &fnv);
  return ev_call_fn(n, s, fnv, has_self, self, cal->k == N_FIELD ? cal->a : NULL, out);
}
int ev_while(Node *n, Scope *s, CVal *out) {
  if (!ct_force) return R_FAIL;
  for (;;) {
    step();
    Scope *bs = new_scope(s, NULL);
    CVal c;
    EV(n->a, s, &c);
    int go;
    if (n->cap) {
      if (ISNULL(c))
        go = 0;
      else if (c.k == CV_NULL)
        c = unwrap_some_null(c);
      else if (c.k == CV_ERR) {
        go = 0;
        if (n->c && n->cap2) {
          Scope *es = new_scope(s, NULL);
          bind_cap(es, n->cap2, c);
          CVal ev2;
          int r = ev(n->c, es, &ev2);
          if (r == R_OK) *out = ev2;
          return r;
        }
      } else if (c.k == CV_UNDEF)
        return R_FAIL;
      else {
        go = 1;
        if (n->capref) {
          CVal p = {0};
          p.k = CV_PTR;
          p.base = box(c);
          p.idx = -1;
          p.t = ptr_to(cv_typeof(&c), 0);
          bind_cap(bs, n->cap, p);
        } else
          bind_cap(bs, n->cap, c);
      }
    } else {
      if (c.k != CV_BOOL) return R_FAIL;
      go = (int)c.i;
    }
    if (!go) break;
    CVal bv;
    int r = ev(n->b, bs, &bv);
    if (r == R_CF) {
      if (xs == X_BRK && (!xlabel || (n->label && !strcmp(xlabel, n->label)))) {
        xs = X_NONE;
        *out = xval;
        return R_OK;
      }
      if (xs == X_CONT && (!xlabel || (n->label && !strcmp(xlabel, n->label))))
        xs = X_NONE;
      else
        return r;
    } else if (r != R_OK)
      return r;
    if (n->d) {
      CVal dv;
      EV(n->d, bs, &dv);
    }
  }
  if (n->c) return ev(n->c, s, out);
  *out = cv_void();
  return R_OK;
}
int ev_for(Node *n, Scope *s, CVal *out) {
  if (!ct_force) return R_FAIL;
  int ni = n->list.n;
  CVal *objs = xalloc(sizeof(CVal) * ni);
  CVal **cells = xalloc(sizeof(CVal *) * ni);
  int64_t *starts = xalloc(sizeof(int64_t) * ni);
  char *isr = xalloc(ni);
  int64_t len = -1;
  for (int i = 0; i < ni; i++) {
    Node *e = n->list.a[i];
    if (e->k == N_RANGE) {
      CVal lo;
      EV(e->a, s, &lo);
      if (lo.k != CV_INT) return R_FAIL;
      isr[i] = 1;
      starts[i] = (int64_t)lo.i;
      if (e->b) {
        CVal hi;
        EV(e->b, s, &hi);
        if (hi.k != CV_INT) return R_FAIL;
        len = (int64_t)(hi.i - lo.i);
      }
      continue;
    }
    Node *cp = i < n->list2.n ? n->list2.a[i] : NULL;
    if (cp && (cp->flags & F_REF)) {
      CVal *cell;
      int r = clval(e, s, &cell);
      if (r != R_OK) {
        CVal v;
        EV(e, s, &v);
        if (v.k != CV_PTR && v.k != CV_SLICE) return R_FAIL;
        objs[i] = v;
      } else {
        cells[i] = cell;
        objs[i] = *cell;
        if (cell->k == CV_PTR) {
          cells[i] = NULL;
        }
      }
    } else
      EV(e, s, &objs[i]);
    int64_t l;
    if (!cv_len(&objs[i], &l)) {
      Type *t = cv_typeof(&objs[i]);
      if (objs[i].k == CV_PTR && t->k == TY_PTR && t->elem->k == TY_ARRAY)
        l = t->elem->len;
      else
        return R_FAIL;
    }
    if (len < 0) len = l;
  }
  if (len < 0) return R_FAIL;
  for (int64_t k = 0; k < len; k++) {
    step();
    Scope *bs = new_scope(s, NULL);
    for (int i = 0; i < ni && i < n->list2.n; i++) {
      Node *cp = n->list2.a[i];
      if (isr[i]) {
        bind_cap(bs, cp->s, cv_int(starts[i] + k, t_usize));
        continue;
      }
      if (cp->flags & F_REF) {
        CVal p = {0};
        p.k = CV_PTR;
        Type *ot = cv_typeof(&objs[i]);
        Type *et = ot->k == TY_ARRAY                              ? ot->elem
                   : (ot->k == TY_PTR && ot->elem->k == TY_ARRAY) ? ot->elem->elem
                                                                  : ot->elem;
        if (cells[i]) {
          p.base = cells[i];
          p.idx = k;
        } else if (objs[i].k == CV_PTR) {
          CVal *c = elem_cell(&objs[i], k);
          p.base = c;
          p.idx = -1;
        } else if (objs[i].k == CV_SLICE) {
          p.base = objs[i].base;
          p.idx = objs[i].idx + k;
        }
        p.t = ptr_to(et ? et : t_u8, 0);
        bind_cap(bs, cp->s, p);
      } else
        bind_cap(bs, cp->s, cv_elem(&objs[i], k));
    }
    CVal bv;
    int r = ev(n->b, bs, &bv);
    if (r == R_CF) {
      if (xs == X_BRK && (!xlabel || (n->label && !strcmp(xlabel, n->label)))) {
        xs = X_NONE;
        *out = xval;
        return R_OK;
      }
      if (xs == X_CONT && (!xlabel || (n->label && !strcmp(xlabel, n->label)))) {
        xs = X_NONE;
        continue;
      }
      return r;
    } else if (r != R_OK)
      return r;
  }
  if (n->c) return ev(n->c, s, out);
  *out = cv_void();
  return R_OK;
}
int item_matches(Node *it, Scope *s, CVal *v, int *m) {
  if (it->k == N_RANGE) {
    CVal lo, hi;
    EV(it->a, s, &lo);
    EV(it->b, s, &hi);
    if (v->k != CV_INT || lo.k != CV_INT || hi.k != CV_INT) return R_FAIL;
    *m = v->i >= lo.i && v->i <= hi.i;
    return R_OK;
  }
  CVal iv;
  int r = ev_rt(it, s, v->k == CV_INT ? cv_typeof(v) : NULL, &iv);
  if (r != R_OK) return r;
  if (v->k == CV_AGG && v->t->k == TY_UNION) {
    *m = union_tag_is(v, &iv);
    return R_OK;
  }
  CVal e;
  if (ev_bin("==", *v, iv, &e) != R_OK) return R_FAIL;
  *m = (int)e.i;
  return R_OK;
}
int ev_switch(Node *n, Scope *s, Type *rt, CVal *out) {
  CVal v;
  EV(n->a, s, &v);
  if (v.k == CV_UNDEF) return R_FAIL;
  for (;;) {
    step();
    Node *hit = NULL, *els = NULL;
    for (int i = 0; i < n->list.n && !hit; i++) {
      Node *pr = n->list.a[i];
      if (pr->flags & F_ELSE) {
        els = pr;
        continue;
      }
      for (int j = 0; j < pr->list.n; j++) {
        int m;
        int r = item_matches(pr->list.a[j], s, &v, &m);
        if (r != R_OK) return r;
        if (m) {
          hit = pr;
          break;
        }
      }
    }
    if (!hit) hit = els;
    if (!hit) return R_FAIL;
    Scope *ps = new_scope(s, NULL);
    if (hit->cap) {
      CVal pv = v;
      if (v.k == CV_AGG && v.t->k == TY_UNION) pv = *v.el[0];
      if (hit->capref) {
        CVal p = {0};
        p.k = CV_PTR;
        p.base = (v.k == CV_AGG && v.t->k == TY_UNION) ? v.el[0] : box(v);
        p.idx = -1;
        p.t = ptr_to(cv_typeof(&pv), 0);
        bind_cap(ps, hit->cap, p);
      } else
        bind_cap(ps, hit->cap, pv);
    }
    if (hit->cap2) {
      if (v.k == CV_AGG && v.t->k == TY_UNION) {
        Field *f = field_at(v.t, (int)v.i);
        bind_cap(ps, hit->cap2, cv_int(f->val, v.t->ct->tag));
      } else
        bind_cap(ps, hit->cap2, v);
    }
    int r = ev_rt(hit->b, ps, rt, out);
    if (r == R_CF && n->label && xlabel && !strcmp(xlabel, n->label)) {
      if (xs == X_BRK) {
        xs = X_NONE;
        *out = xval;
        return R_OK;
      }
      if (xs == X_CONT) {
        xs = X_NONE;
        v = ccoerce(xval, cv_typeof(&v));
        continue;
      }
    }
    return r;
  }
}
int ev_slice(Node *n, Scope *s, CVal *out) {
  CVal base, lo, hi;
  int has_hi = n->c != NULL;
  CVal *cell = NULL;
  int r = R_FAIL;
  {
    char *gs;
    int64_t go;
    Type *gt; /* slice of a runtime global array with comptime bounds: pointer into the global */
    if ((n->a->k == N_IDENT || n->a->k == N_FIELD || n->a->k == N_INDEX) && global_addr(n->a, s, &gs, &go, &gt) &&
        gt->k == TY_ARRAY) {
      EV(n->b, s, &lo);
      if (lo.k != CV_INT) return R_FAIL;
      int64_t h = gt->len;
      if (has_hi) {
        EV(n->c, s, &hi);
        if (hi.k != CV_INT) return R_FAIL;
        h = (int64_t)hi.i;
      }
      CVal p = {0};
      p.k = CV_PTR;
      p.s = gs;
      p.i = go + (int64_t)lo.i * tsize(gt->elem);
      p.t = ptr_to(array_of(gt->elem, h - (int64_t)lo.i, 0, 0), 0);
      *out = p;
      return R_OK;
    }
  }
  if (n->a->k == N_IDENT || n->a->k == N_FIELD || n->a->k == N_INDEX || n->a->k == N_DEREF) r = clval(n->a, s, &cell);
  if (r == R_OK && cell->k != CV_PTR && cell->k != CV_SLICE && cell->k != CV_STR)
    base = *cell;
  else {
    cell = NULL;
    EV(n->a, s, &base);
  }
  EV(n->b, s, &lo);
  if (lo.k != CV_INT) return R_FAIL;
  if (has_hi) {
    EV(n->c, s, &hi);
    if (hi.k != CV_INT) return R_FAIL;
  }
  int hs = 0;
  int64_t sv = 0;
  if (n->d) {
    CVal sn;
    EV(n->d, s, &sn);
    hs = 1;
    sv = (int64_t)sn.i;
  }
  int64_t l = (int64_t)lo.i;
  Type *bt = cv_typeof(&base);
  if (base.k == CV_STR) {
    int64_t h = has_hi ? (int64_t)hi.i : base.slen;
    CVal r2 = cv_str(base.s + l, (int)(h - l));
    r2.t = ptr_to(array_of(t_u8, h - l, hs, sv), 1);
    *out = r2;
    return R_OK;
  }
  if (base.k == CV_AGG && bt->k == TY_ARRAY) {
    if (!cell) cell = box(base);
    int64_t h = has_hi ? (int64_t)hi.i : base.n;
    CVal p = {0};
    p.k = CV_PTR;
    p.base = cell;
    p.idx = l;
    p.t = ptr_to(array_of(bt->elem, h - l, hs, sv), 0);
    *out = p;
    return R_OK;
  }
  if (base.k == CV_UNDEF && bt->k == TY_ARRAY) {
    if (!cell) return R_FAIL;
    *cell = agg_new(bt);
    return ev_slice(n, s, out);
  }
  if (base.k == CV_SLICE) {
    int64_t h = has_hi ? (int64_t)hi.i : base.slen;
    if (base.base && base.base->k == CV_STR) {
      CVal r2 = cv_str(base.base->s + base.idx + l, (int)(h - l));
      r2.t = ptr_to(array_of(t_u8, h - l, hs, sv), 1);
      *out = r2;
      return R_OK;
    }
    CVal p = {0};
    p.k = CV_PTR;
    p.base = base.base;
    p.idx = base.idx + l;
    p.t = ptr_to(array_of(bt->elem, h - l, hs, sv), bt->isconst);
    *out = p;
    return R_OK;
  }
  if (base.k == CV_PTR && base.base) {
    Type *et;
    int64_t len = -1;
    int64_t start;
    if (bt->k == TY_PTR && bt->elem->k == TY_ARRAY) {
      et = bt->elem->elem;
      len = bt->elem->len;
      start = base.idx < 0 ? 0 : base.idx;
      if (base.idx < 0) {
        CVal *c = base.base;
        if (c->k == CV_STR) {
          int64_t h = has_hi ? (int64_t)hi.i : c->slen;
          CVal r2 = cv_str(c->s + l, (int)(h - l));
          r2.t = ptr_to(array_of(t_u8, h - l, hs, sv), 1);
          *out = r2;
          return R_OK;
        }
        if (c->k == CV_UNDEF) *c = agg_new(bt->elem);
      }
    } else if (bt->k == TY_MPTR) {
      et = bt->elem;
      start = base.idx < 0 ? 0 : base.idx;
    } else if (bt->k == TY_PTR) {
      et = bt->elem;
      len = 1;
      start = base.idx < 0 ? 0 : base.idx;
    } else
      return R_FAIL;
    int64_t h = has_hi ? (int64_t)hi.i : len;
    if (h < 0) return R_FAIL;
    CVal p = {0};
    p.k = CV_PTR;
    p.base = base.base;
    p.idx = start + l;
    if (bt->k == TY_PTR && bt->elem->k != TY_ARRAY) {
      p.base = box(*base.base);
      p.idx = l;
    } /* single item: view as array of 1 */
    p.t = ptr_to(array_of(et, h - l, hs, sv), bt->isconst);
    *out = p;
    return R_OK;
  }
  if (getenv("ZB_DBG"))
    fprintf(stderr, "slice fail base k=%d t=%s basebase=%d\n", base.k, tname(bt), base.base ? base.base->k : -1);
  return R_FAIL;
}

/* ---------- lvalues ---------- */
int base_cell(Node *a, Scope *s, CVal **cell) {
  /* the cell an lvalue chain operates on; pointers are dereferenced */
  int r = clval(a, s, cell);
  if (r != R_OK) {
    CVal v;
    int r2 = ev(a, s, &v);
    if (r2 != R_OK) return r2;
    if (v.k != CV_PTR && v.k != CV_SLICE) return R_FAIL;
    *cell = box(v);
  }
  return R_OK;
}
/* parent links for struct-field cells (so &agg.field materializes as parent symbol + offset) */
void **cp_k;
CVal **cp_p;
int *cp_f;
int cp_cap, cp_n;
CVal *cell_parent(CVal *c, int *fi) {
  if (!cp_cap) return NULL;
  unsigned h = (unsigned)(((uintptr_t)c >> 4) * 2654435761u) & (cp_cap - 1);
  while (cp_k[h]) {
    if (cp_k[h] == c) {
      *fi = cp_f[h];
      return cp_p[h];
    }
    h = (h + 1) & (cp_cap - 1);
  }
  return NULL;
}
void cp_put(CVal *c, CVal *par, int fi) {
  int dummy;
  if (cell_parent(c, &dummy)) return;
  if (cp_n * 2 >= cp_cap) {
    int oc = cp_cap;
    void **ok = cp_k;
    CVal **op = cp_p;
    int *of = cp_f;
    cp_cap = oc ? oc * 2 : 256;
    cp_k = xalloc(sizeof(void *) * cp_cap);
    cp_p = xalloc(sizeof(CVal *) * cp_cap);
    cp_f = xalloc(sizeof(int) * cp_cap);
    cp_n = 0;
    for (int i = 0; i < oc; i++)
      if (ok[i]) cp_put(ok[i], op[i], of[i]);
  }
  unsigned h = (unsigned)(((uintptr_t)c >> 4) * 2654435761u) & (cp_cap - 1);
  while (cp_k[h]) h = (h + 1) & (cp_cap - 1);
  cp_k[h] = c;
  cp_p[h] = par;
  cp_f[h] = fi;
  cp_n++;
}
int clval(Node *n, Scope *s, CVal **cell) {
  switch (n->k) {
  case N_IDENT: {
    Sym *y;
    Decl *d;
    if (!lookup(s, n->s, &y, &d)) return R_FAIL;
    if (y) {
      if (y->k != S_CVAL) return R_FAIL;
      *cell = &y->cv;
      return R_OK;
    }
    resolve_decl(d);
    if (d->kind == D_CONST) {
      *cell = &d->cv;
      return R_OK;
    }
    return R_FAIL;
  }
  case N_COMPTIME: return clval(n->a, s, cell);
  case N_UNWRAP: return clval(n->a, s, cell);
  case N_DEREF: {
    CVal v;
    EV(n->a, s, &v);
    CVal *c = deref_cell(&v);
    if (!c) return R_FAIL;
    *cell = c;
    return R_OK;
  }
  case N_BUILTIN:
    if (!strcmp(n->s, "field") && n->list.n == 2) {
      CVal nm;
      EV(n->list.a[1], s, &nm);
      if (nm.k != CV_STR) return R_FAIL;
      Node tmp = *n;
      tmp.k = N_FIELD;
      tmp.a = n->list.a[0];
      tmp.s = xstrndup(nm.s, nm.slen);
      return clval(&tmp, s, cell);
    }
    return R_FAIL;
  case N_FIELD: {
    CVal *c;
    int r = base_cell(n->a, s, &c);
    if (r != R_OK) return r;
    while (c->k == CV_PTR) {
      CVal *d = deref_cell(c);
      if (!d) return R_FAIL;
      c = d;
    }
    if (c->k == CV_UNDEF && c->t && (is_struct_like(c->t) || c->t->k == TY_UNION)) *c = agg_new(c->t);
    if (c->k != CV_AGG) return R_FAIL;
    Type *t = c->t;
    if (t->k == TY_UNION) {
      int fi = field_index(t, n->s);
      if (fi < 0) return R_FAIL;
      if (c->i != fi) {
        c->i = fi;
        *c->el[0] = cv_undef(field_at(t, fi)->t);
      }
      cp_put(c->el[0], c, -1);
      *cell = c->el[0];
      return R_OK;
    }
    if (!is_struct_like(t)) return R_FAIL;
    int fi = field_index(t, n->s);
    if (fi < 0) return R_FAIL;
    if (t->k == TY_STRUCT) cp_put(c->el[fi], c, fi);
    *cell = c->el[fi];
    return R_OK;
  }
  case N_INDEX: {
    CVal *c;
    int r = base_cell(n->a, s, &c);
    if (r != R_OK) return r;
    CVal iv;
    EV(n->b, s, &iv);
    if (iv.k != CV_INT) return R_FAIL;
    if (c->k == CV_PTR && c->t && c->t->k == TY_PTR) {
      CVal *d = deref_cell(c);
      if (!d) return R_FAIL;
      c = d;
    }
    if (c->k == CV_UNDEF && c->t && c->t->k == TY_ARRAY) *c = agg_new(c->t);
    if (c->k == CV_STR) return R_FAIL;
    CVal *e = elem_cell(c, (int64_t)iv.i);
    if (!e) return R_FAIL;
    *cell = e;
    return R_OK;
  }
  default: return R_FAIL;
  }
}
int lv_const(Node *n, Scope *s) {
  for (;;) {
    if (n->k == N_FIELD || n->k == N_INDEX || n->k == N_UNWRAP || n->k == N_COMPTIME) {
      n = n->a;
      continue;
    }
    if (n->k == N_IDENT) {
      Sym *y;
      Decl *d;
      if (lookup(s, n->s, &y, &d) && y) return !y->mut;
      return 1;
    }
    return 0;
  }
}
/* address of (a field/element of) a runtime global, as a comptime pointer value */
int global_addr(Node *n, Scope *s, char **sym, int64_t *off, Type **t) {
  if (n->k == N_IDENT) {
    Sym *y;
    Decl *d;
    if (!lookup(s, n->s, &y, &d) || y) return 0;
    resolve_decl(d);
    if (d->kind != D_VAR || !d->sym) return 0;
    *sym = d->sym;
    *off = 0;
    *t = d->t;
    return 1;
  }
  if (n->k == N_FIELD) {
    if (!global_addr(n->a, s, sym, off, t)) return 0;
    if (!is_struct_like(*t) && (*t)->k != TY_UNION) return 0;
    Field *f = find_field((*t)->ct, n->s);
    if (!f) return 0;
    *off += f->off;
    *t = f->t;
    return 1;
  }
  if (n->k == N_INDEX) {
    if (!global_addr(n->a, s, sym, off, t) || (*t)->k != TY_ARRAY) return 0;
    CVal iv;
    if (ev(n->b, s, &iv) != R_OK || iv.k != CV_INT) return 0;
    *t = (*t)->elem;
    *off += (int64_t)iv.i * tsize(*t);
    return 1;
  }
  return 0;
}

/* ---------- main evaluator ---------- */
Node *fail_node;
int ev(Node *n, Scope *s, CVal *out) {
  if (n->tok) ev_cur = n;
  int r = ev_(n, s, out);
  if (r == R_FAIL) {
    if (!fail_node) fail_node = n;
    if (ct_trace < 0) ct_trace = getenv("ZB_CT_TRACE") != NULL;
    if (ct_trace && ct_force)
      fprintf(stderr, "ct: cannot evaluate node kind %d at %s:%d\n", n->k, n->tok ? n->tok->file : "?",
              n->tok ? n->tok->line : 0);
  }
  return r;
}
Type *lab_rt(const char *l) {
  for (int i = lrt_n - 1; i >= 0; i--)
    if (l && lrt_l[i] && !strcmp(lrt_l[i], l)) return lrt_t[i];
  return NULL;
}
int ev_if(Node *n, Scope *s, Type *rt, CVal *out) {
  CVal c;
  EV(n->a, s, &c);
  int some = c.k == CV_NULL && c.slen > 0;
  if (some) c = unwrap_some_null(c);
  if (n->cap || some || c.k == CV_NULL || c.k == CV_ERR) {
    if (c.k == CV_UNDEF) return R_FAIL;
    if (!some && (c.k == CV_NULL || c.k == CV_ERR)) {
      if (!n->c) {
        *out = cv_void();
        return R_OK;
      }
      Scope *es = new_scope(s, NULL);
      if (c.k == CV_ERR) bind_cap(es, n->cap2, c);
      return ev_rt(n->c, es, rt, out);
    }
    if (some || c.k != CV_BOOL || n->cap) {
      Scope *ts = new_scope(s, NULL);
      if (n->capref) {
        CVal p = {0};
        p.k = CV_PTR;
        CVal *cell;
        if (clval(n->a, s, &cell) == R_OK)
          p.base = cell;
        else
          p.base = box(c);
        p.idx = -1;
        p.t = ptr_to(cv_typeof(&c), 0);
        bind_cap(ts, n->cap, p);
      } else
        bind_cap(ts, n->cap, c);
      return ev_rt(n->b, ts, rt, out);
    }
  }
  if (c.k != CV_BOOL) return R_FAIL;
  if (c.i) return ev_rt(n->b, s, rt, out);
  if (!n->c) {
    *out = cv_void();
    return R_OK;
  }
  return ev_rt(n->c, s, rt, out);
}
CVal neg_like(CVal a, const char *op) {
  if (a.k == CV_AGG && a.t->k == TY_ARRAY) {
    CVal r = agg_new(a.t);
    for (int i = 0; i < a.n; i++) *r.el[i] = neg_like(*a.el[i], op);
    return r;
  }
  if (op[0] == '!') return cv_bool(!a.i);
  Type *t = cv_typeof(&a);
  if (a.k == CV_FLOAT) return cv_float(-a.f, t);
  if (op[0] == '~') return cv_int(wrap_int(~a.i, t), t);
  return cv_int(wrap_int(-a.i, t), t);
}
int ev_(Node *n, Scope *s, CVal *out) {
  CVal a, b;
  switch (n->k) {
  case N_INT:
  case N_CHAR: *out = cv_int((i128)n->ival, t_cint); return R_OK;
  case N_FLOAT: *out = cv_float(n->fval, t_cfloat); return R_OK;
  case N_STR: *out = cv_str(n->s, n->slen); return R_OK;
  case N_TRUE: *out = cv_bool(1); return R_OK;
  case N_FALSE: *out = cv_bool(0); return R_OK;
  case N_NULL: *out = cv_null(); return R_OK;
  case N_UNDEF: *out = cv_undef(NULL); return R_OK;
  case N_ENUMLIT: *out = cv_enumlit(n->s); return R_OK;
  case N_ERRVAL: {
    CVal v = {0};
    v.k = CV_ERR;
    v.i = err_id(n->s);
    v.t = t_errset;
    *out = v;
    return R_OK;
  }
  case N_ERRSET: {
    Vec nm = {0};
    for (int i = 0; i < n->list.n; i++) {
      err_id(((Node *)n->list.a[i])->s);
      vpush(&nm, ((Node *)n->list.a[i])->s);
    }
    *out = cv_ty(errset_named((char **)nm.a, nm.n));
    return R_OK;
  }
  case N_UNREACHABLE:
    if (ct_force) die("%s:%d: reached unreachable code at comptime", n->tok->file, n->tok->line);
    return R_FAIL;
  case N_NOP: *out = cv_void(); return R_OK;
  case N_IDENT: {
    Type *pt = n->tok && n->tok->k == TK_ID && n->tok->ival ? NULL : prim_type(n->s);
    if (pt) {
      *out = cv_ty(pt);
      return R_OK;
    }
    Sym *y;
    Decl *d;
    if (!lookup(s, n->s, &y, &d)) die("%s:%d: use of undeclared identifier '%s'", n->tok->file, n->tok->line, n->s);
    if (y) {
      if (y->k == S_CVAL) {
        *out = y->cv;
        return R_OK;
      }
      if (y->t && y->t->k == TY_ENUM && y->t->ct && !y->t->ct->nonexh) {
        layout(y->t->ct);
        if (y->t->ct->fields.n == 1) {
          *out = cv_int(((Field *)y->t->ct->fields.a[0])->val, y->t);
          return R_OK;
        }
      }
      if (y->t && y->t->k == TY_VOID) {
        *out = cv_void();
        return R_OK;
      }
      if (y->t && y->t->k == TY_NULL) {
        *out = cv_null_pub();
        return R_OK;
      }
      return R_FAIL;
    }
    resolve_decl(d);
    if (d->kind == D_CONST || d->kind == D_FN) {
      *out = d->cv;
      return R_OK;
    }
    return R_FAIL;
  }
  case N_FIELD: {
    Type *at;
    if (!strcmp(n->s, "len") && is_local_array(s, n->a, &at)) {
      *out = cv_int(at->len, t_usize);
      return R_OK;
    }
    if (!strcmp(n->s, "len") && n->a->k == N_IDENT) {
      Sym *y;
      Decl *d; /* runtime tuple: length is comptime */
      if (lookup(s, n->a->s, &y, &d) && y && y->k == S_LOCAL && y->t) {
        Type *t = y->t;
        if (t->k == TY_PTR) t = t->elem;
        if (is_tuple_type(t)) {
          layout(t->ct);
          *out = cv_int(t->ct->fields.n, t_cint);
          return R_OK;
        }
      }
    }
    if (ct_field_of(s, n, out)) return R_OK;
    EV(n->a, s, &a);
    if (ceval_member(a, n->s, out)) return R_OK;
    if (a.k == CV_TYPE && ct_force) die("%s:%d: no member '%s' in %s", n->tok->file, n->tok->line, n->s, tname(a.t));
    return R_FAIL;
  }
  case N_INDEX: {
    EV(n->a, s, &a);
    EV(n->b, s, &b);
    if (b.k != CV_INT) return R_FAIL;
    if (a.k == CV_PTR && a.t && a.t->k == TY_PTR && a.t->elem->k != TY_ARRAY) return R_FAIL;
    int64_t l;
    if (a.k == CV_AGG || a.k == CV_STR || a.k == CV_SLICE || (a.k == CV_PTR && a.base)) {
      if (cv_len(&a, &l) && (b.i < 0 || b.i > l))
        die("%s:%d: index %lld out of bounds at comptime", n->tok->file, n->tok->line, (long long)b.i);
      *out = cv_elem(&a, (int64_t)b.i);
      return R_OK;
    }
    return R_FAIL;
  }
  case N_SLICE: return ev_slice(n, s, out);
  case N_DEREF: {
    EV(n->a, s, &a);
    if (a.k == CV_SLICE && a.t && a.t->k == TY_SLICE) { /* 0.17: comptime-length slice deref -> array */
      Type *at = array_of(a.t->elem, a.slen, 0, 0);
      CVal r = agg_new(at);
      for (int64_t i = 0; i < a.slen; i++) *r.el[i] = ccoerce(cv_elem(&a, i), a.t->elem);
      *out = r;
      return R_OK;
    }
    if (a.k == CV_STR ||
        (a.k == CV_PTR && a.base && a.idx >= 0 && a.t && a.t->k == TY_PTR && a.t->elem->k == TY_ARRAY &&
         !is_vec(a.t->elem) &&
         !(a.base->k == CV_AGG && cv_typeof(a.base)->k == TY_ARRAY && cv_typeof(a.base)->elem == a.t->elem))) {
      /* dereferencing a pointer to a (sub-)array: copy the elements out */
      Type *at = a.k == CV_STR
                     ? (a.t && a.t->k == TY_PTR && a.t->elem->k == TY_ARRAY ? a.t->elem : array_of(t_u8, a.slen, 0, 0))
                     : a.t->elem;
      CVal r = agg_new(at);
      for (int64_t i = 0; i < at->len; i++) {
        if (a.k == CV_STR)
          *r.el[i] = cv_int((unsigned char)a.s[i], t_u8);
        else if (a.base->k == CV_STR)
          *r.el[i] = cv_int((unsigned char)a.base->s[a.idx + i], t_u8);
        else {
          CVal *e = elem_cell(a.base, a.idx + i);
          if (!e) {
            if (getenv("ZB_DBG"))
              fprintf(stderr, "copy fail base k=%d t=%s idx=%lld i=%lld\n", a.base->k, tname(cv_typeof(a.base)),
                      (long long)a.idx, (long long)i);
            return R_FAIL;
          }
          *r.el[i] = cv_copy(*e);
        }
      }
      *out = r;
      return R_OK;
    }
    if (a.k == CV_AGG && a.t && a.t->k == TY_ARRAY) {
      *out = a;
      return R_OK;
    } /* `++` result viewed as *const [N]T */
    CVal *c = deref_cell(&a);
    if (!c) {
      if (getenv("ZB_DBG"))
        fprintf(stderr, "deref fail k=%d t=%s idx=%lld basek=%d\n", a.k, a.t ? tname(a.t) : "-", (long long)a.idx,
                a.base ? a.base->k : -1);
      return R_FAIL;
    }
    *out = *c;
    return R_OK;
  }
  case N_UNWRAP:
    EV(n->a, s, &a);
    if (a.k == CV_NULL && a.slen > 0) {
      *out = unwrap_some_null(a);
      return R_OK;
    }
    if (a.k == CV_NULL) {
      if (ct_force) die("%s:%d: attempt to use null value at comptime", n->tok->file, n->tok->line);
      return R_FAIL;
    }
    if (a.k == CV_UNDEF) return R_FAIL;
    *out = a;
    return R_OK;
  case N_UN: {
    if (!strcmp(n->s, "&")) {
      CVal *cell;
      CVal p = {0};
      p.k = CV_PTR;
      p.idx = -1;
      int r = clval(n->a, s, &cell);
      if (r == R_OK) {
        p.base = cell;
        p.t = ptr_to(cv_typeof(cell), lv_const(n->a, s));
        *out = p;
        return R_OK;
      }
      if (r == R_CF) return r;
      char *sym;
      int64_t off;
      Type *gt;
      if (global_addr(n->a, s, &sym, &off, &gt)) {
        p.s = sym;
        p.i = off;
        p.t = ptr_to(gt, 0);
        *out = p;
        return R_OK;
      }
      if (n->a->k == N_FIELD) { /* &(rvalue).field: keep the parent aggregate */
        CVal b;
        int rb = ev(n->a->a, s, &b);
        if (rb == R_OK && b.k == CV_AGG && b.t && b.t->k == TY_STRUCT) {
          int fi = field_index(b.t, n->a->s);
          if (fi >= 0) {
            CVal *bc = box(b);
            CVal *fc = bc->el[fi];
            cp_put(fc, bc, fi);
            p.base = fc;
            p.t = ptr_to(cv_typeof(fc), 1);
            *out = p;
            return R_OK;
          }
        }
      }
      EV(n->a, s, &a);
      p.base = box(a);
      p.t = ptr_to(cv_typeof(&a), 1);
      *out = p;
      return R_OK;
    }
    EV(n->a, s, &a);
    if (a.k == CV_AGG && a.t->k == TY_ARRAY) {
      *out = neg_like(a, n->s);
      return R_OK;
    }
    if (n->s[0] == '!') {
      if (a.k != CV_BOOL) return R_FAIL;
      *out = cv_bool(!a.i);
      return R_OK;
    }
    if (a.k == CV_FLOAT && n->s[0] == '-') {
      *out = neg_like(a, n->s);
      return R_OK;
    }
    if (a.k != CV_INT) return R_FAIL;
    if (n->s[0] == '~' && cv_typeof(&a)->k != TY_INT) return R_FAIL;
    *out = neg_like(a, n->s);
    return R_OK;
  }
  case N_BIN: {
    const char *op = n->s;
    if (!strcmp(op, "and") || !strcmp(op, "or")) {
      EV(n->a, s, &a);
      if (a.k != CV_BOOL) return R_FAIL;
      if ((op[0] == 'a') != !!a.i) {
        *out = a;
        return R_OK;
      }
      EV(n->b, s, &b);
      if (b.k != CV_BOOL) return R_FAIL;
      *out = b;
      return R_OK;
    }
    EV(n->a, s, &a);
    EV(n->b, s, &b);
    if (!strcmp(op, "||")) {
      if (a.k != CV_TYPE || b.k != CV_TYPE) return R_FAIL;
      *out = cv_ty(errset_merge(a.t, b.t));
      return R_OK;
    }
    return ev_bin(op, a, b, out);
  }
  case N_ORELSE:
    EV(n->a, s, &a);
    if (a.k == CV_UNDEF) return R_FAIL;
    if (a.k == CV_NULL && a.slen > 0) {
      *out = unwrap_some_null(a);
      return R_OK;
    }
    if (a.k == CV_NULL) return ev(n->b, s, out);
    *out = a;
    return R_OK;
  case N_CATCH:
    EV(n->a, s, &a);
    if (a.k == CV_UNDEF) return R_FAIL;
    if (a.k == CV_ERR) {
      Scope *cs = new_scope(s, NULL);
      bind_cap(cs, n->cap, a);
      return ev(n->b, cs, out);
    }
    *out = a;
    return R_OK;
  case N_TRY:
    EV(n->a, s, &a);
    if (a.k == CV_ERR) {
      if (!ct_force) return R_FAIL;
      xs = X_RET;
      xlabel = NULL;
      xval = a;
      return R_CF;
    }
    if (a.k == CV_UNDEF) return R_FAIL;
    *out = a;
    return R_OK;
  case N_IF: return ev_if(n, s, NULL, out);
  case N_SWITCH: return ev_switch(n, s, NULL, out);
  case N_WHILE: return ev_while(n, s, out);
  case N_FOR: return ev_for(n, s, out);
  case N_BLOCK: return ev_block(n, s, out);
  case N_BREAK: {
    CVal v = cv_void();
    if (n->a) EVR(n->a, s, lab_rt(n->label), &v);
    xs = X_BRK;
    xlabel = n->label;
    xval = v;
    return R_CF;
  }
  case N_CONTINUE: {
    CVal v = cv_void();
    if (n->a) EV(n->a, s, &v);
    xs = X_CONT;
    xlabel = n->label;
    xval = v;
    return R_CF;
  }
  case N_RETURN: {
    if (!ct_force) return R_FAIL;
    CVal v = cv_void();
    if (n->a) EVR(n->a, s, cur_rt, &v);
    xs = X_RET;
    xlabel = NULL;
    xval = v;
    return R_CF;
  }
  case N_DEFER:
  case N_ERRDEFER: *out = cv_void(); return R_OK;
  case N_VAR: {
    if (!ct_force && !(n->flags & F_CONST)) return R_FAIL;
    Type *t = NULL;
    if (n->a) {
      CVal tv;
      ct_force++;
      int r = ev(n->a, s, &tv);
      ct_force--;
      if (r != R_OK) return r;
      if (tv.k != CV_TYPE) return R_FAIL;
      t = tv.t;
    }
    CVal v;
    if (!n->b)
      v = cv_undef(t);
    else if (n->b->k == N_CONTAINER) {
      Container *c = container_from(n->b, s, NULL);
      if (!strncmp(c->name, "anon", 4)) c->name = n->s;
      v = cv_ty(c->type);
    } else {
      EVR(n->b, s, t, &v);
      if (t) v = ccoerce(v, t);
      if (v.k == CV_UNDEF && t) v.t = t;
    }
    if (v.k == CV_UNDEF && t && (t->k == TY_ARRAY || is_struct_like(t))) v = agg_new(t);
    if (strcmp(n->s, "_")) {
      bind_cval(s, n->s, cv_copy(v));
      if (!(n->flags & F_CONST)) ((Sym *)s->syms.a[s->syms.n - 1])->mut = 1;
    }
    *out = cv_void();
    return R_OK;
  }
  case N_ASSIGN: {
    if (!ct_force) return R_FAIL;
    if (n->a->k == N_IDENT && !strcmp(n->a->s, "_")) {
      EV(n->b, s, &b);
      *out = cv_void();
      return R_OK;
    }
    if (n->a->k == N_DEREF && !strcmp(n->s, "=")) { /* store through a pointer to a sub-array view: elementwise */
      CVal pv;
      EV(n->a->a, s, &pv);
      if (pv.k == CV_PTR && pv.base && pv.idx >= 0 && pv.t && pv.t->k == TY_PTR && pv.t->elem->k == TY_ARRAY &&
          !is_vec(pv.t->elem) && pv.base->k == CV_AGG && cv_typeof(pv.base)->k == TY_ARRAY &&
          cv_typeof(pv.base)->elem != pv.t->elem) {
        Type *at = pv.t->elem;
        EVR(n->b, s, at, &b);
        b = ccoerce(b, at);
        for (int64_t i = 0; i < at->len && pv.idx + i < pv.base->n; i++) {
          CVal e = b.k == CV_AGG   ? *b.el[i]
                   : b.k == CV_STR ? cv_int(i < b.slen ? (unsigned char)b.s[i] : 0, t_u8)
                                   : cv_undef(at->elem);
          assign(pv.base->el[pv.idx + i], cv_copy(e));
        }
        *out = cv_void();
        return R_OK;
      }
    }
    if (n->a->k == N_FIELD && (!strcmp(n->a->s, "len") || !strcmp(n->a->s, "ptr"))) { /* slice.len / slice.ptr */
      CVal *c;
      if (base_cell(n->a->a, s, &c) == R_OK) {
        while (c->k == CV_PTR && c->t && c->t->k == TY_PTR && c->t->elem->k == TY_SLICE) {
          CVal *d = deref_cell(c);
          if (!d) break;
          c = d;
        }
        Type *st = cv_typeof(c);
        if (st && st->k == TY_SLICE && (c->k == CV_SLICE || c->k == CV_PTR || c->k == CV_UNDEF)) {
          if (c->k != CV_SLICE) {
            int64_t l = 0;
            if (c->k == CV_PTR) cv_len(c, &l);
            CVal sl = {0};
            sl.k = CV_SLICE;
            sl.t = st;
            sl.slen = (int)l;
            if (c->k == CV_PTR) {
              sl.base = c->base;
              sl.idx = c->idx < 0 ? 0 : c->idx;
            }
            *c = sl;
          }
          if (!strcmp(n->a->s, "len")) {
            EVR(n->b, s, t_usize, &b);
            CVal cur = cv_int(c->slen, t_usize), rv = b;
            if (strcmp(n->s, "=")) {
              char op[8];
              int l = (int)strlen(n->s) - 1;
              memcpy(op, n->s, l);
              op[l] = 0;
              if (ev_bin(op, cur, ccoerce(b, t_usize), &rv) != R_OK) return R_FAIL;
            }
            if (rv.k != CV_INT) return R_FAIL;
            c->slen = (int)rv.i;
          } else {
            EVR(n->b, s, NULL, &b);
            if (b.k != CV_PTR && b.k != CV_SLICE) return R_FAIL;
            c->base = b.base;
            c->idx = b.idx < 0 ? 0 : b.idx;
          }
          *out = cv_void();
          return R_OK;
        }
      }
    }
    CVal *cell;
    int r = clval(n->a, s, &cell);
    if (r != R_OK) return r;
    Type *ct = cv_typeof(cell);
    if (ct && (ct->k == TY_UNDEF || ct->k == TY_NULL)) ct = NULL;
    if (!strcmp(n->s, "=")) {
      EVR(n->b, s, ct, &b);
      assign(cell, ct ? ccoerce(b, ct) : b);
    } else {
      EVR(n->b, s, NULL, &b);
      char op[8];
      int l = (int)strlen(n->s) - 1;
      memcpy(op, n->s, l);
      op[l] = 0;
      CVal rv;
      if (ev_bin(op, *cell, b, &rv) != R_OK) return R_FAIL;
      assign(cell, ct ? ccoerce(rv, ct) : rv);
    }
    *out = cv_void();
    return R_OK;
  }
  case N_DESTRUCT: {
    for (int i = 0; i < n->list.n; i++) {
      Node *t = n->list.a[i];
      if (!ct_force && !(t->k == N_VAR && (t->flags & F_CONST))) return R_FAIL;
    }
    EV(n->b, s, &a);
    for (int i = 0; i < n->list.n; i++) {
      Node *t = n->list.a[i];
      CVal e = cv_elem(&a, i);
      if (t->k == N_VAR) {
        if (t->a) {
          Type *tt = eval_type(t->a, s);
          e = ccoerce(e, tt);
        }
        bind_cval(s, t->s, cv_copy(e));
        if (!(t->flags & F_CONST)) ((Sym *)s->syms.a[s->syms.n - 1])->mut = 1;
      } else if (t->k == N_IDENT && !strcmp(t->s, "_"))
        continue;
      else {
        CVal *cell;
        int r = clval(t, s, &cell);
        if (r != R_OK) return r;
        assign(cell, ccoerce(e, cv_typeof(cell)));
      }
    }
    *out = cv_void();
    return R_OK;
  }
  case N_COMPTIME: {
    ct_force++;
    int r = ev(n->a, s, out);
    ct_force--;
    return r;
  }
  case N_INIT: return ev_init(n, s, NULL, out);
  case N_CALL: return ev_call(n, s, out);
  case N_BUILTIN: brt = NULL; return ev_builtin(n, s, out);
  case N_TPTR: {
    CVal e;
    ct_force++;
    int r = ev(n->a, s, &e);
    ct_force--;
    if (r != R_OK) return r;
    if (e.k != CV_TYPE) return R_FAIL;
    int c = !!(n->flags & F_CONST);
    if (!strcmp(n->s, "*"))
      *out = cv_ty(ptr_to(e.t, c));
    else if (!strcmp(n->s, "[]")) {
      int64_t sv = 0;
      int hs = 0;
      if (n->b) {
        EVR(n->b, s, e.t, &b);
        sv = (int64_t)b.i;
        hs = 1;
      }
      *out = cv_ty(slice_of_s(e.t, c, hs, sv));
    } else {
      int64_t sv = 0;
      int hs = 0;
      if (n->b) {
        EVR(n->b, s, e.t, &b);
        sv = (int64_t)b.i;
        hs = 1;
      }
      *out = cv_ty(mptr_to(e.t, c, hs, sv));
    }
    return R_OK;
  }
  case N_TARRAY: {
    if (!n->a) return R_FAIL;
    ct_force++;
    int r = ev(n->a, s, &a);
    if (r == R_OK) r = ev(n->b, s, &b);
    ct_force--;
    if (r != R_OK) return r;
    if (a.k != CV_INT || b.k != CV_TYPE) return R_FAIL;
    int hs = 0;
    int64_t sv = 0;
    if (n->c) {
      CVal c;
      EVR(n->c, s, b.t, &c);
      hs = 1;
      sv = (int64_t)c.i;
    }
    *out = cv_ty(array_of(b.t, (int64_t)a.i, hs, sv));
    return R_OK;
  }
  case N_TOPT: {
    ct_force++;
    int r = ev(n->a, s, &a);
    ct_force--;
    if (r != R_OK) return r;
    if (a.k != CV_TYPE) return R_FAIL;
    *out = cv_ty(opt_of(a.t));
    return R_OK;
  }
  case N_TERRU: {
    ct_force++;
    int r = ev(n->a, s, &a);
    if (r == R_OK) r = ev(n->b, s, &b);
    ct_force--;
    if (r != R_OK) return r;
    if (b.k != CV_TYPE) return R_FAIL;
    *out = cv_ty(erru_of2(b.t, a.k == CV_TYPE ? a.t : NULL));
    return R_OK;
  }
  case N_TFN: {
    Vec ps = {0};
    for (int i = 0; i < n->list.n; i++) {
      Node *p = n->list.a[i];
      if (p->flags & F_VARARGS) continue;
      if (!p->a) {
        vpush(&ps, t_anytype);
        continue;
      }
      ct_force++;
      int r = ev(p->a, s, &a);
      ct_force--;
      if (r != R_OK) return r;
      if (a.k != CV_TYPE) return R_FAIL;
      vpush(&ps, a.t);
    }
    ct_force++;
    int r = ev(n->a, s, &a);
    ct_force--;
    if (r != R_OK) return r;
    if (a.k != CV_TYPE) return R_FAIL;
    Type *rt = a.t;
    if (n->flags & F_INFERR) rt = erru_of(rt);
    *out = cv_ty(fn_type(&ps, rt, !!(n->flags & F_VARARGS)));
    return R_OK;
  }
  case N_CONTAINER: *out = cv_ty(container_from(n, s, NULL)->type); return R_OK;
  case N_ASM: return R_FAIL;
  default: return R_FAIL;
  }
}

/* evaluation with a result type */
Type *unwrap_rt(Type *t) {
  while (t && (t->k == TY_OPT || t->k == TY_ERRU)) t = t->elem;
  return t;
}
int ev_rt(Node *n, Scope *s, Type *rt, CVal *out) {
  if (!rt || rt->k == TY_ANYTYPE) return ev(n, s, out);
  int r;
  switch (n->k) {
  case N_INIT:
    if (!n->a) {
      r = ev_init(n, s, rt, out);
      if (r == R_OK) *out = ccoerce(*out, rt);
      return r;
    }
    break;
  case N_UNDEF: *out = cv_undef(rt); return R_OK;
  case N_CALL:
    if (n->a->k == N_ENUMLIT) {
      Type *t = unwrap_rt(rt);
      if (t->k == TY_PTR) t = t->elem;
      if (!t->ct) return R_FAIL;
      Decl *d = find_decl(t->ct, n->a->s);
      if (!d) die("%s:%d: no decl '%s' in %s", n->tok->file, n->tok->line, n->a->s, tname(t));
      resolve_decl(d);
      CVal nv = {0};
      r = ev_call_fn(n, s, d->cv, 0, nv, NULL, out);
      if (r == R_OK) *out = ccoerce(*out, rt);
      return r;
    }
    break;
  case N_UN:
    if (!strcmp(n->s, "&") && (rt->k == TY_PTR || rt->k == TY_SLICE || rt->k == TY_MPTR || unwrap_rt(rt)->k == TY_PTR ||
                               unwrap_rt(rt)->k == TY_SLICE)) {
      Type *pt = unwrap_rt(rt);
      Node *x = n->a;
      if ((x->k == N_INIT && !x->a) || x->k == N_BUILTIN || x->k == N_ENUMLIT ||
          (x->k == N_CALL && x->a->k == N_ENUMLIT)) {
        Type *et = NULL;
        if (pt->k == TY_PTR)
          et = pt->elem;
        else if (x->k == N_INIT)
          et = array_of(pt->elem, x->list.n, 0, 0);
        CVal v;
        if (et && et->k == TY_ARRAY && et->len < 0) et = NULL;
        if (x->k == N_BUILTIN && pt->k == TY_SLICE) {
          r = ev(x, s, &v);
        } else {
          r = ev_rt(x, s, et, &v);
        }
        if (r != R_OK) return r;
        if (v.k == CV_AGG && v.t == t_splat) return R_FAIL;
        CVal p = {0};
        p.k = CV_PTR;
        p.base = box(v);
        p.idx = -1;
        p.t = ptr_to(cv_typeof(&v), 1);
        *out = ccoerce(p, rt);
        return R_OK;
      }
    }
    break;
  case N_BLOCK:
    if (n->label && lrt_n < 64) {
      lrt_l[lrt_n] = n->label;
      lrt_t[lrt_n] = rt;
      lrt_n++;
      r = ev(n, s, out);
      lrt_n--;
      if (r == R_OK) *out = ccoerce(*out, rt);
      return r;
    }
    break;
  case N_IF:
    r = ev_if(n, s, rt, out);
    if (r == R_OK) *out = ccoerce(*out, rt);
    return r;
  case N_SWITCH:
    r = ev_switch(n, s, rt, out);
    if (r == R_OK) *out = ccoerce(*out, rt);
    return r;
  case N_COMPTIME:
    ct_force++;
    r = ev_rt(n->a, s, rt, out);
    ct_force--;
    return r;
  case N_ORELSE: {
    CVal a;
    EVR(n->a, s, opt_of(rt), &a);
    if (a.k == CV_UNDEF) return R_FAIL;
    if (a.k == CV_NULL && a.slen > 0) {
      *out = unwrap_some_null(a);
      return R_OK;
    }
    if (a.k == CV_NULL) return ev_rt(n->b, s, rt, out);
    *out = ccoerce(a, rt);
    return R_OK;
  }
  case N_CATCH: {
    CVal a;
    EV(n->a, s, &a);
    if (a.k == CV_UNDEF) return R_FAIL;
    if (a.k == CV_ERR) {
      Scope *cs = new_scope(s, NULL);
      bind_cap(cs, n->cap, a);
      return ev_rt(n->b, cs, rt, out);
    }
    *out = ccoerce(a, rt);
    return R_OK;
  }
  case N_BUILTIN:
    brt = rt;
    r = ev_builtin(n, s, out);
    if (r == R_OK) *out = ccoerce(*out, rt);
    return r;
  default: break;
  }
  r = ev(n, s, out);
  if (r == R_OK) *out = ccoerce(*out, rt);
  return r;
}

/* ---------- initializers ---------- */
int ev_init(Node *n, Scope *s, Type *t, CVal *out) {
  if (n->a) {
    if (n->a->k == N_TARRAY && !n->a->a) {
      CVal e;
      ct_force++;
      int r = ev(n->a->b, s, &e);
      ct_force--;
      if (r != R_OK) return r;
      int hs = 0;
      int64_t sv = 0;
      if (n->a->c) {
        CVal c;
        EVR(n->a->c, s, e.t, &c);
        hs = 1;
        sv = (int64_t)c.i;
      }
      t = array_of(e.t, n->list.n, hs, sv);
    } else {
      CVal tv;
      ct_force++;
      int r = ev(n->a, s, &tv);
      ct_force--;
      if (r != R_OK) return r;
      if (tv.k != CV_TYPE) return R_FAIL;
      t = tv.t;
    }
  }
  t = unwrap_rt(t);
  if (t && t->k == TY_PTR && !n->a) t = NULL;
  if (t && t->k == TY_SLICE && !n->a && !(n->flags & F_FIELDS)) { /* ZON-style .{...} with a slice result type */
    Type *at = array_of(t->elem, n->list.n, t->hassent, t->sent);
    CVal arr;
    int r = ev_init(n, s, at, &arr);
    if (r != R_OK) return r;
    CVal p = {0};
    p.k = CV_PTR;
    p.idx = -1;
    p.base = box(arr);
    p.t = ptr_to(at, 1);
    *out = ccoerce(p, t);
    return R_OK;
  }
  if (t && t->k == TY_ARRAY) {
    CVal a = agg_new(t);
    if (n->flags & F_FIELDS) return R_FAIL;
    for (int i = 0; i < n->list.n && i < a.n; i++) {
      CVal v;
      EVR(n->list.a[i], s, t->elem, &v);
      *a.el[i] = ccoerce(v, t->elem);
    }
    *out = a;
    return R_OK;
  }
  if (t && t->k == TY_UNION) {
    if (!(n->flags & F_FIELDS) || n->list.n != 1) {
      if (!n->list.n) {
        *out = agg_new(t);
        return R_OK;
      }
      return R_FAIL;
    }
    Node *nm = n->list2.a[0];
    int fi = field_index(t, nm->s);
    if (fi < 0) die("%s:%d: no field %s in %s", n->tok->file, n->tok->line, nm->s, tname(t));
    CVal v;
    EVR(n->list.a[0], s, field_at(t, fi)->t, &v);
    *out = mk_union(t, nm->s, v);
    return R_OK;
  }
  if (t && is_struct_like(t)) {
    CVal a = agg_new(t);
    char *set = xalloc(a.n + 1);
    for (int i = 0; i < n->list.n; i++) {
      int fi = (n->flags & F_FIELDS) ? field_index(t, ((Node *)n->list2.a[i])->s) : i;
      if (fi < 0 || fi >= a.n)
        die("%s:%d: no field %s in %s", n->tok->file, n->tok->line,
            (n->flags & F_FIELDS) ? ((Node *)n->list2.a[i])->s : "?", tname(t));
      Type *ft = field_at(t, fi)->t;
      CVal v;
      EVR(n->list.a[i], s, ft, &v);
      *a.el[fi] = ccoerce(v, ft);
      set[fi] = 1;
    }
    for (int i = 0; i < a.n; i++)
      if (!set[i]) *a.el[i] = default_of(t, field_at(t, i));
    *out = a;
    return R_OK;
  }
  /* anonymous struct / tuple literal */
  Vec names = {0}, types = {0};
  CVal *vals = xalloc(sizeof(CVal) * (n->list.n + 1));
  for (int i = 0; i < n->list.n; i++) {
    EV(n->list.a[i], s, &vals[i]);
    vpush(&names, (n->flags & F_FIELDS) ? ((Node *)n->list2.a[i])->s : fmt("%d", i));
    vpush(&types, cv_typeof(&vals[i]));
  }
  CVal a = agg_new(mk_anon_struct(&names, &types, !(n->flags & F_FIELDS)));
  for (int i = 0; i < n->list.n; i++) *a.el[i] = cv_copy(vals[i]);
  *out = a;
  return R_OK;
}
Vec tmemo;
char *cv_name(CVal *v) {
  switch (v->k) {
  case CV_TYPE: return tname(v->t);
  case CV_INT:
    if (v->t && v->t->k == TY_ENUM) {
      Container *c = v->t->ct;
      layout(c);
      for (int i = 0; i < c->fields.n; i++) {
        Field *f = c->fields.a[i];
        if (f->val == (int64_t)v->i) return fmt(".%s", f->name);
      }
    }
    return fmt("%lld", (long long)v->i);
  case CV_BOOL: return v->i ? "true" : "false";
  case CV_ENUMLIT: return fmt(".%s", v->s);
  case CV_STR: return fmt("\"%.*s\"", v->slen > 20 ? 20 : v->slen, v->s);
  case CV_NULL: return "null";
  case CV_FN: return v->fn->name;
  default: return "{...}";
  }
}
int ct_call(Decl *fd, CVal *args, int na, CVal *out) {
  Node *f = fd->node;
  if (!f->b) return R_FAIL;
  step();
  Scope *fs = new_scope(fd->ct->scope, NULL);
  int np = f->list.n;
  CVal *bound = xalloc(sizeof(CVal) * (np + 1));
  for (int i = 0; i < np; i++) {
    Node *p = f->list.a[i];
    if (p->flags & F_VARARGS) break;
    Type *pt = NULL;
    if (p->a && !(p->flags & F_ANYTYPE)) {
      CVal tv;
      ct_force++;
      int r = ev(p->a, fs, &tv);
      ct_force--;
      if (r == R_OK && tv.k == CV_TYPE) pt = tv.t;
    }
    CVal a = i < na ? args[i] : cv_undef(NULL);
    if (pt) a = ccoerce(a, pt);
    bound[i] = a;
    if (p->s) bind_cval(fs, p->s, cv_copy(a));
  }
  Type *rt = NULL;
  int has_rt = fn_ret_type(fd, fs, &rt);
  int memo = has_rt && rt == t_type;
  if (memo) {
    for (int i = 0; i < tmemo.n; i++) {
      TMemo *m = tmemo.a[i];
      if (m->fd != fd || m->n != np) continue;
      int ok = 1;
      for (int j = 0; j < np && ok; j++)
        if (!cval_eq(&m->args[j], &bound[j])) ok = 0;
      if (ok) {
        *out = m->res;
        return R_OK;
      }
    }
  }
  Type *srt = cur_rt;
  cur_rt = has_rt ? rt : NULL;
  int slrt = lrt_n;
  ct_force++;
  CVal rv;
  int r = ev(f->b, fs, &rv);
  ct_force--;
  cur_rt = srt;
  lrt_n = slrt;
  if (r == R_CF) {
    if (xs == X_RET) {
      xs = X_NONE;
      rv = xval;
      r = R_OK;
    } else
      die("%s:%d: break/continue out of function %s", f->tok->file, f->tok->line, fd->name);
  } else if (r == R_OK)
    rv = cv_void();
  if (r != R_OK) return r;
  if (has_rt) rv = ccoerce(rv, rt);
  if (memo) {
    if (rv.k == CV_TYPE && rv.t->ct &&
        (!strncmp(rv.t->ct->name, "anon", 4) ||
         (rv.t->ct->node && rv.t->ct->scope && rv.t->ct->scope->up && rv.t->ct->scope->up->up == fs))) {
      char nm[512];
      int m = snprintf(nm, sizeof nm, "%s.%s(", fd->ct->name, fd->name);
      for (int i = 0; i < np && m < 400; i++)
        m += snprintf(nm + m, sizeof nm - m, "%s%s", i ? "," : "", cv_name(&bound[i]));
      snprintf(nm + m, sizeof nm - m, ")");
      rv.t->ct->name = xstrndup(nm, strlen(nm));
    }
    TMemo *mm = xalloc(sizeof *mm);
    mm->fd = fd;
    mm->args = bound;
    mm->n = np;
    mm->res = rv;
    vpush(&tmemo, mm);
  }
  *out = rv;
  return R_OK;
}
CtSave ct_enter(int force) {
  CtSave sv = {ct_force, xs, cur_rt, lrt_n, fail_node};
  ct_force = force;
  fail_node = NULL;
  return sv;
}
Node *last_fail;
void ct_leave(CtSave sv) {
  if (fail_node) last_fail = fail_node;
  ct_force = sv.force;
  xs = sv.xs;
  cur_rt = sv.rt;
  lrt_n = sv.lrt;
  fail_node = sv.fail;
}
int ceval(Node *n, Scope *s, CVal *out) {
  CtSave sv = ct_enter(0);
  memset(out, 0, sizeof *out);
  int r = ev(n, s, out);
  ct_leave(sv);
  return r == R_OK;
}
int ceval_force(Node *n, Scope *s, CVal *out) {
  CtSave sv = ct_enter(1);
  memset(out, 0, sizeof *out);
  int r = ev(n, s, out);
  ct_leave(sv);
  return r == R_OK;
}
int ceval_rt(Node *n, Scope *s, Type *rt, CVal *out) {
  CtSave sv = ct_enter(1);
  memset(out, 0, sizeof *out);
  int r = ev_rt(n, s, rt, out);
  ct_leave(sv);
  return r == R_OK;
}
int ceval_ret(Node *n, Scope *s, Type *rt, Type *fnrt, CVal *out, int *returned) {
  CtSave sv = ct_enter(1);
  memset(out, 0, sizeof *out);
  Type *srt = cur_rt;
  cur_rt = fnrt;
  int r = ev_rt(n, s, rt, out);
  if (r == R_CF && xs == X_RET) {
    xs = X_NONE;
    *out = fnrt ? ccoerce(xval, fnrt) : xval;
    *returned = 1;
    r = R_OK;
  }
  cur_rt = srt;
  ct_leave(sv);
  return r == R_OK;
}
int ct_try_store(Node *dst, Node *n, Scope *s) {
  Node *r = dst;
  while (r &&
         (r->k == N_FIELD || r->k == N_INDEX || r->k == N_UNWRAP || r->k == N_DEREF || r->k == N_SLICE || r->k == N_UN))
    r = r->a;
  if (!r || r->k != N_IDENT) return 0;
  Sym *y = lookup_local(s, r->s);
  if (!y || y->k != S_CVAL || !y->mut) return 0;
  CtSave sv = ct_enter(1);
  CVal o;
  int rr = ev(n, s, &o);
  ct_leave(sv);
  if (rr != R_OK)
    die("%s:%d: cannot evaluate store to comptime variable '%s' (at %s)", n->tok->file, n->tok->line, r->s,
        ct_fail_loc());
  return 1;
}
int ct_try_assign(Node *n, Scope *s) {
  Node *r = n->a;
  while (r->k == N_FIELD || r->k == N_INDEX || r->k == N_UNWRAP || (r->k == N_DEREF)) r = r->a;
  if (r->k != N_IDENT) return 0;
  Sym *y = lookup_local(s, r->s);
  if (!y || y->k != S_CVAL || !y->mut) return 0;
  CtSave sv = ct_enter(1);
  CVal o;
  int rr = ev(n, s, &o);
  ct_leave(sv);
  if (rr != R_OK) die("%s:%d: cannot evaluate assignment to comptime variable '%s'", n->tok->file, n->tok->line, r->s);
  return 1;
}
Type *eval_type(Node *n, Scope *s) {
  CVal v;
  CtSave sv = ct_enter(1);
  int r = ev(n, s, &v);
  Node *fn = fail_node;
  ct_leave(sv);
  if (r != R_OK) {
    if (fn && fn->tok)
      die("%s:%d: expected comptime type expression (cannot evaluate expression at %s:%d)", n->tok->file, n->tok->line,
          fn->tok->file, fn->tok->line);
    die("%s:%d: expected comptime type expression", n->tok->file, n->tok->line);
  }
  if (v.k == CV_TYPE) return v.t;
  if (v.k == CV_NULL) return t_null;
  die("%s:%d: expected a type", n->tok->file, n->tok->line);
}
Type *call_type_fn(Decl *d, Vec *argnodes, Scope *s) {
  Node cn = {0};
  cn.k = N_CALL;
  Node fnn = {0};
  cn.a = &fnn;
  cn.tok = d->node->tok;
  cn.list = *argnodes;
  CtSave sv = ct_enter(1);
  CVal r;
  CVal nv = {0};
  int rr = ev_call_fn(&cn, s, d->cv, 0, nv, NULL, &r);
  ct_leave(sv);
  if (rr != R_OK || r.k != CV_TYPE)
    die("%s:%d: cannot evaluate type function %s at comptime", d->node->tok->file, d->node->tok->line, d->name);
  return r.t;
}
const char *ct_fail_loc(void) {
  Node *f = last_fail;
  return f && f->tok ? fmt("%s:%d (node kind %d)", f->tok->file, f->tok->line, f->k) : "?";
}
/* helpers exported to the code generator */
i128 cv_pack(CVal *v) {
  return pack_val(v);
}
int cv_binop(const char *op, CVal a, CVal b, CVal *out) {
  return ev_bin(op, a, b, out) == R_OK;
}
int cv_match(CVal *v, CVal *item) {
  CVal it = *item;
  if (v->k == CV_AGG && v->t->k == TY_UNION) return union_tag_is(v, &it);
  CVal e;
  if (it.k == CV_ENUMLIT && v->k == CV_INT) it = ccoerce(it, cv_typeof(v));
  if (ev_bin("==", *v, it, &e) != R_OK) return 0;
  return (int)e.i;
}
int ceval_ex(Node *n, Scope *s, Type *rt, CVal *out) {
  CtSave sv = ct_enter(0);
  memset(out, 0, sizeof *out);
  int r = ev_rt(n, s, rt, out);
  ct_leave(sv);
  return r == R_OK;
}
