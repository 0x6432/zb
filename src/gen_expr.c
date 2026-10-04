#include "gen_int.h"

/* ---------- expressions ---------- */
Val gen_member(Val base, const char *name, Node *n) {
  if (base.ck) {
    CVal m;
    if (ceval_member(base.cv, name, &m)) return CK(m);
    if (base.cv.k == CV_TYPE && base.cv.t->ct) {
      Decl *d = find_decl(base.cv.t->ct, name);
      if (d) {
        resolve_decl(d);
        if (d->kind == D_VAR) return LV(d->t, fmt("$%s", d->sym));
      }
    }
    if (base.cv.k == CV_PTR && base.t && (base.t->k == TY_PTR || base.t->k == TY_MPTR)) {
      if (!strcmp(name, "len") && base.t->k == TY_PTR && base.t->elem->k == TY_ARRAY) {
        CVal l = {0};
        l.k = CV_INT;
        l.t = t_usize;
        l.i = base.t->elem->len;
        return CK(l);
      }
      base = V(base.t, mat(base));
    } else if ((base.cv.k == CV_SLICE ||
                (base.cv.k == CV_PTR && base.cv.t && base.cv.t->k == TY_PTR && base.cv.t->elem->k == TY_ARRAY)) &&
               base.t && base.t->k == TY_SLICE && (!strcmp(name, "len") || !strcmp(name, "ptr"))) {
      if (name[0] == 'l') {
        CVal l = {0};
        l.k = CV_INT;
        l.t = t_usize;
        l.i = base.cv.k == CV_SLICE ? base.cv.slen : base.cv.t->elem->len;
        return CK(l);
      }
      return V(mptr_to(base.t->elem, base.t->isconst, base.t->hassent, base.t->sent), mat(base));
    } else if (base.cv.k != CV_STR)
      die("%s:%d: no member '%s' (ck kind %d, %s)", n->tok->file, n->tok->line, name, base.cv.k, tname(base.t));
  }
  Type *t = base.t;
  if (t->k == TY_PTR && t->elem->k != TY_OPAQUE) {
    base = LV(t->elem, opnd(base));
    t = t->elem;
  }
  switch (t->k) {
  case TY_STRUCT:
  case TY_UNION:
  case TY_TUPLE: {
    Field *f = find_field(t->ct, name);
    if (!f) {
      Decl *d = find_decl(t->ct, name);
      if (d) {
        resolve_decl(d);
        if (d->kind == D_VAR) return LV(d->t, fmt("$%s", d->sym));
        return CK(d->cv);
      }
      if (!strcmp(name, "len") && is_tuple_type(t)) {
        CVal l = {0};
        l.k = CV_INT;
        l.t = t_cint;
        l.i = t->ct->fields.n;
        return CK(l);
      }
      die("%s:%d: no field '%s' in %s", n->tok->file, n->tok->line, name, tname(t));
    }
    if (f->is_ct) {
      Val r = CK(*(CVal *)f->defcv);
      r.t = f->t;
      return r;
    }
    if (t->k == TY_STRUCT && is_packed(t)) {
      Val r = LV(f->t, NULL);
      if (base.lv && base.bf) {
        r.op = base.op;
        r.hbytes = base.hbytes;
        r.bitoff = base.bitoff + f->bitoff;
      } else {
        r.op = addr_of(base);
        r.hbytes = tsize(t);
        r.bitoff = f->bitoff;
      }
      r.bf = 1;
      if (!base.lv) {
        Val x = r;
        x.lv = 1;
        return rv(x);
      }
      return r;
    }
    if (t->k == TY_UNION && base.lv && base.bf) {
      Val r = base;
      r.t = f->t;
      return r;
    } /* packed union inside a packed struct */
    return LV(f->t, addp(addr_of(base), f->off));
  }
  case TY_SLICE:
    if (!strcmp(name, "len")) return LV(t_usize, addp(addr_of(base), 8));
    if (!strcmp(name, "ptr")) return LV(mptr_to(t->elem, t->isconst, 0, 0), addr_of(base));
    break;
  case TY_ARRAY:
    if (!strcmp(name, "len")) {
      CVal c = {0};
      c.k = CV_INT;
      c.i = t->len;
      c.t = t_cint;
      return CK(c);
    }
    if (!strcmp(name, "ptr")) return V(mptr_to(t->elem, 0, 0, 0), addr_of(base)); /* (*[N]T).ptr */
    break;
  case TY_ENUM:
  case TY_ERRU:
  case TY_OPT: break;
  default: break;
  }
  die("%s:%d: no member '%s' on %s", n->tok->file, n->tok->line, name, tname(t));
}
Val gen_index(Val b, Val i) {
  Type *t = b.t, *et;
  char *base;
  {
    Type *tt = t->k == TY_PTR ? t->elem : t;
    if ((tt->k == TY_TUPLE || (tt->k == TY_STRUCT && tt->ct && tt->ct->is_tuple)) && i.ck) {
      char nb[32];
      snprintf(nb, sizeof nb, "%lld", (long long)i.cv.i);
      return gen_member(b, nb, NULL);
    }
  }
  if (b.ck && b.cv.k == CV_STR) {
    base = mat(b);
    et = t_u8;
  } else if (t->k == TY_PTR && t->elem->k == TY_ARRAY) {
    base = opnd(b);
    et = t->elem->elem;
  } else if (t->k == TY_ARRAY) {
    base = addr_of(b);
    et = t->elem;
  } else if (t->k == TY_SLICE) {
    base = load(t_u64, addr_of(b));
    et = t->elem;
  } else if (t->k == TY_MPTR) {
    base = opnd(b);
    et = t->elem;
  } else {
    Node *cn = gen_cur_pub();
    die("%s:%d: cannot index %s", cn ? cn->tok->file : "?", cn ? cn->tok->line : 0, tname(t));
  }
  i = coerce(i, t_usize);
  if (i.ck) return LV(et, addp(base, i.cv.i * tsize(et)));
  char *o = tmp(), *a = tmp();
  emit("%s =l mul %s, %d", o, opnd(i), tsize(et));
  emit("%s =l add %s, %s", a, base, o);
  return LV(et, a);
}
Val gen_slice(Node *n, Scope *s) {
  Val b = gen(n->a, s, NULL);
  Type *t = b.t, *et;
  char *base, *len = NULL;
  int c = 0;
  if (b.ck && b.cv.k == CV_STR) {
    base = mat(b);
    et = t_u8;
    len = fmt("%d", b.cv.slen);
    c = 1;
  } else if (t->k == TY_PTR && t->elem->k == TY_ARRAY) {
    base = opnd(b);
    et = t->elem->elem;
    len = fmt("%lld", (long long)t->elem->len);
    c = t->isconst;
  } else if (t->k == TY_ARRAY) {
    base = addr_of(b);
    et = t->elem;
    len = fmt("%lld", (long long)t->len);
  } else if (t->k == TY_SLICE) {
    char *a = addr_of(b);
    base = load(t_u64, a);
    len = load(t_u64, addp(a, 8));
    et = t->elem;
    c = t->isconst;
  } else if (t->k == TY_MPTR) {
    base = opnd(b);
    et = t->elem;
    c = t->isconst;
  } else if (t->k == TY_PTR) {
    base = opnd(b);
    et = t->elem;
    c = t->isconst;
    len = "1";
  } else
    die("%s:%d: cannot slice %s", n->tok->file, n->tok->line, tname(t));
  int64_t clen = (t->k == TY_PTR && t->elem->k == TY_ARRAY) ? t->elem->len
                 : t->k == TY_ARRAY                         ? t->len
                 : (t->k == TY_PTR)                         ? 1
                                                            : -1;
  if (b.ck && b.cv.k == CV_STR) clen = b.cv.slen;
  Val lov = coerce(gen(n->b, s, t_usize), t_usize), hiv;
  int hck = 0;
  int64_t hcv = clen;
  if (n->c) {
    hiv = coerce(gen(n->c, s, t_usize), t_usize);
    if (hiv.ck) {
      hck = 1;
      hcv = (int64_t)hiv.cv.i;
    }
  } else
    hck = clen >= 0;
  char *lo = opnd(lov);
  char *hi = n->c ? opnd(hiv) : len;
  if (!hi && t->k == TY_MPTR) { /* mptr[lo..] is a many-pointer */
    char *o = tmp(), *r = tmp();
    emit("%s =l mul %s, %d", o, lo, tsize(et));
    emit("%s =l add %s, %s", r, base, o);
    return V(mptr_to(et, c, 0, 0), r);
  }
  if (!hi) die("slice of many-pointer needs an end");
  if (lov.ck && hck && !(b.ck && b.cv.k == CV_STR)) { /* comptime-known bounds: pointer to array */
    int hs2 = 0;
    int64_t sv2 = 0;
    if (n->d) {
      CVal sc;
      if (ceval_ex(n->d, s, et, &sc)) {
        hs2 = 1;
        sv2 = (int64_t)sc.i;
      }
    } else if (!n->c && t->k == TY_PTR && t->elem->k == TY_ARRAY && t->elem->hassent) {
      hs2 = 1;
      sv2 = t->elem->sent;
    }
    Type *pt = ptr_to(array_of(et, hcv - (int64_t)lov.cv.i, hs2, sv2), c);
    return V(pt, addp(base, (int64_t)lov.cv.i * tsize(et)));
  }
  int hs = 0;
  int64_t sv = 0;
  if (n->d) {
    CVal sc;
    if (!ceval_ex(n->d, s, et, &sc) && !ceval_rt(n->d, s, et, &sc))
      die("%s:%d: slice sentinel must be comptime (at %s)", n->tok->file, n->tok->line, ct_fail_loc());
    hs = 1;
    sv = (int64_t)sc.i;
  } else if (!n->c && t->k == TY_SLICE && t->hassent) {
    hs = 1;
    sv = t->sent;
  } else if (!n->c && t->k == TY_PTR && t->elem->k == TY_ARRAY && t->elem->hassent) {
    hs = 1;
    sv = t->elem->sent;
  }
  Type *st = slice_of_s(et, c, hs, sv);
  char *sl = slot(st);
  char *off = tmp(), *p = tmp(), *l = tmp();
  emit("%s =l mul %s, %d", off, lo, tsize(et));
  emit("%s =l add %s, %s", p, base, off);
  emit("%s =l sub %s, %s", l, hi, lo);
  store(t_u64, p, sl);
  store(t_u64, l, addp(sl, 8));
  return V(st, sl);
}
Val gen_init(Node *n, Scope *s, Type *ex) {
  Type *t;
  if (n->a && n->a->k == N_TARRAY && !n->a->a) {
    int hs = 0;
    int64_t sv = 0;
    if (n->a->c) {
      CVal c;
      ceval(n->a->c, s, &c);
      hs = 1;
      sv = c.i;
    }
    t = array_of(eval_type(n->a->b, s), n->list.n, hs, sv);
  } else
    t = n->a ? eval_type(n->a, s) : ex;
  if (t && (t->k == TY_OPT || t->k == TY_ERRU) && t->elem->k != TY_VOID) return coerce(gen_init(n, s, t->elem), t);
  Type *hint = NULL; /* partially typed tuple (fields of type anytype are inferred) */
  if (t && is_tuple_type(t) && !(n->flags & F_FIELDS)) {
    layout(t->ct);
    for (int i = 0; i < t->ct->fields.n; i++)
      if (((Field *)t->ct->fields.a[i])->t->k == TY_ANYTYPE) {
        hint = t;
        t = NULL;
        break;
      }
  }
  if (!t || t->k == TY_ANYTYPE) {
    Vec names = {0}, types = {0}, vals = {0};
    CVal **cts = xalloc(sizeof(CVal *) * (n->list.n + 1));
    int nct = 0;
    for (int i = 0; i < n->list.n; i++) {
      Type *ht = hint && i < hint->ct->fields.n ? ((Field *)hint->ct->fields.a[i])->t : NULL;
      if (ht && ht->k == TY_ANYTYPE) ht = NULL;
      Val v = rv(gen(n->list.a[i], s, ht));
      if (ht) v = coerce(v, ht);
      if (v.t->k == TY_CINT)
        v = coerce(v, t_i64);
      else if (v.t->k == TY_CFLOAT)
        v = coerce(v, t_f64);
      if (v.ck && (v.cv.k == CV_ENUMLIT || v.cv.k == CV_TYPE)) {
        cts[i] = xalloc(sizeof(CVal));
        *cts[i] = v.cv;
        nct++;
      }
      Val *pv = xalloc(sizeof *pv);
      *pv = v;
      vpush(&vals, pv);
      vpush(&types, v.t);
      vpush(&names, (n->flags & F_FIELDS) ? ((Node *)n->list2.a[i])->s : fmt("%d", i));
    }
    t = nct ? mk_anon_struct_cv(&names, &types, !(n->flags & F_FIELDS), cts)
            : mk_anon_struct(&names, &types, !(n->flags & F_FIELDS));
    char *sl = slot(t);
    for (int i = 0; i < vals.n; i++) {
      Field *f = t->ct->fields.a[i];
      if (f->is_ct) continue;
      put(*(Val *)vals.a[i], f->t, addp(sl, f->off));
    }
    return V(t, sl);
  }
  char *sl = slot(t);
  if (t->k == TY_STRUCT || t->k == TY_TUPLE) {
    Container *c = t->ct;
    layout(c);
    char *set = xalloc(c->fields.n + 1);
    if (is_packed(t)) {
      store(int_type(tsize(t) * 8, 0), "0", sl);
      for (int pass = 0; pass < 2; pass++)
        for (int i = 0; i < (pass ? c->fields.n : n->list.n); i++) {
          Field *f;
          Node *vn;
          if (!pass) {
            f = (n->flags & F_FIELDS) ? find_field(c, ((Node *)n->list2.a[i])->s) : c->fields.a[i];
            vn = n->list.a[i];
            for (int j = 0; j < c->fields.n; j++)
              if (c->fields.a[j] == f) set[j] = 1;
          } else {
            f = c->fields.a[i];
            if (set[i] || !f->def) continue;
            vn = f->def;
          }
          Val v = coerce(gen(vn, pass ? c->scope : s, f->t), f->t);
          if (v.ck && v.cv.k == CV_UNDEF) continue;
          Val l = LV(f->t, sl);
          l.bf = 1;
          l.hbytes = tsize(t);
          l.bitoff = f->bitoff;
          put_lv(v, l);
        }
      return V(t, sl);
    }
    for (int i = 0; i < n->list.n; i++) {
      Field *f = (n->flags & F_FIELDS) ? find_field(c, ((Node *)n->list2.a[i])->s) : c->fields.a[i];
      if (!f) die("%s:%d: no such field", n->tok->file, n->tok->line);
      for (int j = 0; j < c->fields.n; j++)
        if (c->fields.a[j] == f) set[j] = 1;
      Val v = coerce(gen(n->list.a[i], s, f->t), f->t);
      put(v, f->t, addp(sl, f->off));
    }
    for (int j = 0; j < c->fields.n; j++) {
      Field *f = c->fields.a[j];
      if (set[j] || !f->def) continue;
      Val v = coerce(gen(f->def, c->scope, f->t), f->t);
      put(v, f->t, addp(sl, f->off));
    }
    return V(t, sl);
  }
  if (t->k == TY_UNION) {
    if (!n->list.n) return V(t, sl);
    Field *f = find_field(t->ct, ((Node *)n->list2.a[0])->s);
    Val v = coerce(gen(n->list.a[0], s, f->t), f->t);
    put(v, f->t, sl);
    if (t->ct->tagged) store(t->ct->tag, fmt("%lld", (long long)f->val), addp(sl, union_tag_off(t)));
    return V(t, sl);
  }
  if (t->k == TY_ARRAY) {
    int es = tsize(t->elem);
    for (int i = 0; i < n->list.n; i++) {
      Val v = coerce(gen(n->list.a[i], s, t->elem), t->elem);
      put(v, t->elem, addp(sl, (int64_t)i * es));
    }
    if (t->hassent) store(t->elem, fmt("%lld", (long long)t->sent), addp(sl, t->len * es));
    return V(t, sl);
  }
  if (t->k == TY_VOID) return VOIDV();
  die("%s:%d: cannot initialize %s with init list", n->tok->file, n->tok->line, tname(t));
}

/* ---------- calls ---------- */
int all_ct_fields(Type *t) { /* tuple/struct whose fields are all comptime: its value is implied by the type */
  if (!t || !is_tuple_type(t) || !t->ct) return 0;
  layout(t->ct);
  for (int i = 0; i < t->ct->fields.n; i++) {
    Field *f = t->ct->fields.a[i];
    int k = f->t->k;
    if (!f->is_ct && k != TY_ENUMLIT && k != TY_CINT && k != TY_CFLOAT && k != TY_TYPE && k != TY_NULL &&
        !all_ct_fields(f->t))
      return 0;
  }
  return 1;
}
Sym *last_sym(Scope *s) {
  return s->syms.a[s->syms.n - 1];
}
void gen_vardecl(Node *n, Scope *s) {
  Type *t = n->a ? eval_type(n->a, s) : NULL;
  if (n->flags & F_COMPTIME) {
    CVal c;
    if (!n->b) {
      memset(&c, 0, sizeof c);
      c.k = CV_UNDEF;
      c.t = t ? t : t_undef;
    } else if (!ceval_rt(n->b, s, t, &c))
      die("%s:%d: comptime variable initializer is not comptime-known (at %s)", n->tok->file, n->tok->line,
          ct_fail_loc());
    if (t) c = ccoerce(c, t);
    bind_cval(s, n->s, cv_copy(c));
    last_sym(s)->mut = !(n->flags & F_CONST);
    return;
  }
  if ((n->flags & F_CONST) && n->b) {
    CVal c;
    if (n->b->k == N_CONTAINER) {
      c = cv_ty(container_from(n->b, s, n->s)->type);
      bind_cval(s, n->s, c);
      return;
    }
    if (ceval_ex(n->b, s, t, &c) && c.k != CV_UNDEF && c.k != CV_NONE) {
      if (t) c = ccoerce(c, t);
      if ((!t || ck_ok(&c, t)) && !(t && t->k == TY_ERRU && c.k == CV_VOID)) {
        bind_cval(s, n->s, c);
        last_sym(s)->t = t;
        return;
      }
    }
  }
  Val v = n->b ? gen(n->b, s, t) : CK((CVal){.k = CV_UNDEF, .t = t_undef});
  if (v.t->k == TY_NORET) return;
  if ((n->flags & F_CONST) && v.ck && v.cv.k != CV_UNDEF && v.cv.k != CV_NONE &&
      (!t || ck_ok(&v.cv, t))) { /* comptime-known const */
    CVal c = t ? ccoerce(v.cv, t) : v.cv;
    bind_cval(s, n->s, c);
    last_sym(s)->t = t;
    return;
  }
  if (!t) t = v.t;
  if (t->k == TY_CINT) t = t_i64;
  if (v.ck && v.cv.k == CV_STR && !n->a) t = v.t;
  if (type_is_ctonly(t)) {
    if (v.ck) {
      bind_cval(s, n->s, v.cv);
      last_sym(s)->mut = !(n->flags & F_CONST);
      return;
    }
    die("%s:%d: variable of comptime-only type needs comptime", n->tok->file, n->tok->line);
  }
  v = coerce(v, t);
  char *sl = slot(t);
  put(v, t, sl);
  bind_local(s, n->s, t, sl);
}
void gen_assign(Node *n, Scope *s) {
  if (n->a->k == N_IDENT && !strcmp(n->a->s, "_")) {
    discarding++;
    gen(n->b, s, NULL);
    discarding--;
    return;
  }
  if (ct_try_assign(n, s)) return;
  Val l = gen(n->a, s, NULL);
  if (!l.lv) die("%s:%d: cannot assign to rvalue", n->tok->file, n->tok->line);
  if (!strcmp(n->s, "=")) {
    Val v = coerce(gen(n->b, s, l.t), l.t);
    if (v.t->k == TY_NORET) return;
    put_lv(v, l);
    return;
  }
  char op[8];
  strcpy(op, n->s);
  op[strlen(op) - 1] = 0;
  Val r = gen(n->b, s, l.t);
  Val v = coerce(gen_arith(op, rv(l), r), l.t);
  put_lv(v, l);
}
void gen_destruct(Node *n, Scope *s) {
  Type *ext = NULL;
  {
    int allc = n->list.n > 0;
    for (int i = 0; i < n->list.n && allc; i++) {
      Node *tg = n->list.a[i];
      if (!((tg->k == N_VAR && (tg->flags & F_CONST)) || (tg->k == N_IDENT && !strcmp(tg->s, "_")))) allc = 0;
    }
    CVal c;
    int64_t l;
    if (allc && ceval_ex(n->b, s, NULL, &c) && c.k == CV_AGG && cv_len(&c, &l) && l == n->list.n) {
      for (int i = 0; i < n->list.n; i++) {
        Node *tg = n->list.a[i];
        if (tg->k != N_VAR) continue;
        CVal e = cv_elem(&c, i);
        Type *t = tg->a ? eval_type(tg->a, s) : NULL;
        if (t) e = ccoerce(e, t);
        bind_cval(s, tg->s, e);
        if (t) last_sym(s)->t = t;
      }
      return;
    }
  }
  {
    int ok = 1;
    Vec names = {0}, types = {0};
    for (int i = 0; i < n->list.n && ok; i++) {
      Node *tg = n->list.a[i];
      if (tg->k == N_VAR && tg->a) {
        vpush(&names, fmt("%d", i));
        vpush(&types, eval_type(tg->a, s));
      } else if (tg->k != N_VAR && !(tg->k == N_IDENT && !strcmp(tg->s, "_"))) {
        Type *lt = typeof_impl(tg, s);
        if (lt) {
          vpush(&names, fmt("%d", i));
          vpush(&types, lt);
        } else
          ok = 0;
      } else
        ok = 0;
    }
    if (!ok && n->list.n) { /* some untyped targets: take their types from the (dry-run) rhs tuple */
      Vec hn = {0}, ht = {0};
      for (int i = 0; i < n->list.n; i++) {
        Node *tg = n->list.a[i];
        vpush(&hn, fmt("%d", i));
        vpush(&ht, tg->k == N_VAR && tg->a ? eval_type(tg->a, s) : t_anytype);
      }
      int anyt = 0;
      for (int i = 0; i < ht.n; i++)
        if (ht.a[i] != t_anytype) anyt = 1;
      Type *rt = anyt ? typeof_ex(n->b, s, mk_anon_struct(&hn, &ht, 1)) : typeof_impl(n->b, s);
      ok = rt && is_tuple_type(rt) && (layout(rt->ct), rt->ct->fields.n == n->list.n);
      names.n = types.n = 0;
      for (int i = 0; i < n->list.n && ok; i++) {
        Node *tg = n->list.a[i];
        Type *ft = ((Field *)rt->ct->fields.a[i])->t;
        Type *tt;
        if (tg->k == N_VAR && tg->a)
          tt = eval_type(tg->a, s);
        else if (tg->k == N_VAR || (tg->k == N_IDENT && !strcmp(tg->s, "_")))
          tt = ft;
        else
          tt = typeof_impl(tg, s);
        if (!tt || type_incomplete(tt) || type_is_ctonly(tt)) {
          ok = 0;
          break;
        }
        vpush(&names, fmt("%d", i));
        vpush(&types, tt);
      }
    }
    if (ok && n->list.n) ext = mk_anon_struct(&names, &types, 1);
  }
  Val v = gen(n->b, s, ext);
  Type *t = v.t;
  if (t->k == TY_NORET) return;
  if (ext && t != ext && t->k != TY_ARRAY) {
    v = coerce(v, ext);
    t = v.t;
  }
  if (t->k != TY_ARRAY && !t->ct) die("%s:%d: cannot destructure %s", n->tok->file, n->tok->line, tname(t));
  char *a = addr_of(v);
  for (int i = 0; i < n->list.n; i++) {
    Node *tg = n->list.a[i];
    Val e;
    if (t->k == TY_ARRAY)
      e = LV(t->elem, addp(a, (int64_t)i * tsize(t->elem)));
    else {
      Field *f = t->ct->fields.a[i];
      e = LV(f->t, addp(a, f->off));
    }
    if (tg->k == N_VAR) {
      Type *tt = tg->a ? eval_type(tg->a, s) : e.t;
      Val c = coerce(rv(e), tt);
      char *sl = slot(tt);
      put(c, tt, sl);
      bind_local(s, tg->s, tt, sl);
      continue;
    }
    if (tg->k == N_IDENT && !strcmp(tg->s, "_")) continue;
    Val l = gen(tg, s, NULL);
    put_lv(coerce(rv(e), l.t), l);
  }
}
