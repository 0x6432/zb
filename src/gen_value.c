#include "gen_int.h"

int bf_needs_wide(Val *v) { /* field does not fit an 8-byte window of its host */
  if (v->hbytes <= 8) return 0;
  int nb = bits_of(v->t), b0 = v->bitoff / 8;
  if (b0 + 8 > v->hbytes) b0 = v->hbytes - 8;
  return v->bitoff - b0 * 8 + nb > 64;
}
Val bf_wide_window(Val *v, char **base, int *bo) { /* 16-byte window (u128) containing the field */
  int b0 = v->bitoff / 8;
  if (b0 + 16 > v->hbytes) b0 = v->hbytes - 16;
  if (b0 < 0) b0 = 0;
  *bo = v->bitoff - b0 * 8;
  *base = addp(v->op, b0);
  if (v->hbytes - b0 >= 16) return w_from_parts(int_type(128, 0), load(t_u64, *base), load(t_u64, addp(*base, 8)));
  char *sl = slot(int_type(128, 0));
  store(t_u64, "0", sl);
  store(t_u64, "0", addp(sl, 8));
  emit("call $memcpy(l %s, l %s, l %d)", sl, *base, v->hbytes - b0);
  return V(int_type(128, 0), sl);
}
void bf_window(Val *v) { /* hosts wider than 64 bits: use an (unaligned) 8-byte window containing the field */
  if (v->hbytes <= 8) return;
  int nb = bits_of(v->t), b0 = v->bitoff / 8;
  if (b0 + 8 > v->hbytes) b0 = v->hbytes - 8;
  int bo = v->bitoff - b0 * 8;
  if (bo + nb > 64)
    die("packed field of %d bits at bit %d of a %d-byte host is not supported at runtime", nb, v->bitoff, v->hbytes);
  v->op = addp(v->op, b0);
  v->hbytes = 8;
  v->bitoff = bo;
}
char *bf_load(Val v) { /* returns field bits as an integer of the field's int width */
  if (bf_needs_wide(&v)) {
    char *base;
    int bo;
    Val w = bf_wide_window(&v, &base, &bo);
    int nb = bits_of(v.t);
    if (bo) {
      CVal sc = {0};
      sc.k = CV_INT;
      sc.t = t_cint;
      sc.i = bo;
      w = w_arith(">>", int_type(128, 0), w, CK(sc));
    }
    Type *ft = v.t->k == TY_INT ? v.t : int_type(nb, 0);
    return wconv(w, ft).op;
  }
  bf_window(&v);
  Type *h = host_int(v.hbytes);
  char *x = load(h, v.op);
  char c = qc(h);
  int nb = bits_of(v.t);
  if (v.bitoff) {
    char *y = tmp();
    emit("%s =%c shr %s, %d", y, c, x, v.bitoff);
    x = y;
  }
  Type *ft = v.t->k == TY_INT ? v.t : int_type(nb, 0);
  char fc = qc(ft);
  if (fc == 'l' && c == 'w') {
    char *y = tmp();
    emit("%s =l extuw %s", y, x);
    x = y;
  } else if (fc == 'w' && c == 'l') {
    char *y = tmp();
    emit("%s =w copy %s", y, x);
    x = y;
  }
  if (nb < (fc == 'l' ? 64 : 32)) {
    if (ft->sign) {
      char *q = tmp(), *r = tmp();
      int sh = (fc == 'l' ? 64 : 32) - nb;
      emit("%s =%c shl %s, %d", q, fc, x, sh);
      emit("%s =%c sar %s, %d", r, fc, q, sh);
      x = r;
    } else {
      char *r = tmp();
      emit("%s =%c and %s, %llu", r, fc, x, (unsigned long long)((1ULL << nb) - 1));
      x = r;
    }
  }
  return x;
}
void bf_store(Val l, char *v) { /* v: integer operand holding the field bits */
  if (bf_needs_wide(&l)) {
    char *base;
    int bo;
    Val w = bf_wide_window(&l, &base, &bo);
    int nb = bits_of(l.t);
    Type *U = int_type(128, 0);
    Type *ft = l.t->k == TY_INT ? l.t : int_type(nb, 0);
    Val fv = wconv(V(ft, v), U);
    unsigned __int128 m = nb >= 128 ? ~(unsigned __int128)0 : (((unsigned __int128)1 << nb) - 1);
    unsigned __int128 hm = m << bo, keep = ~hm;
    Val mv = w_from_parts(U, fmt("%llu", (unsigned long long)m), fmt("%llu", (unsigned long long)(m >> 64)));
    Val kv = w_from_parts(U, fmt("%llu", (unsigned long long)keep), fmt("%llu", (unsigned long long)(keep >> 64)));
    fv = w_arith("&", U, fv, mv);
    if (bo) {
      CVal sc = {0};
      sc.k = CV_INT;
      sc.t = t_cint;
      sc.i = bo;
      fv = w_arith("<<", U, fv, CK(sc));
    }
    Val r = w_arith("|", U, w_arith("&", U, w, kv), fv);
    int b0 = l.bitoff / 8;
    if (b0 + 16 > l.hbytes) b0 = l.hbytes - 16;
    if (b0 < 0) b0 = 0;
    if (l.hbytes - b0 >= 16) {
      store(t_u64, wlo(r), base);
      store(t_u64, whi(r), addp(base, 8));
    } else
      emit("call $memcpy(l %s, l %s, l %d)", base, addr_of(r), l.hbytes - b0);
    return;
  }
  bf_window(&l);
  Type *h = host_int(l.hbytes);
  char c = qc(h);
  int nb = bits_of(l.t);
  Type *ft = l.t->k == TY_INT ? l.t : int_type(nb, 0);
  unsigned long long m = nb >= 64 ? ~0ULL : ((1ULL << nb) - 1);
  char *x = v;
  if (qc(ft) == 'w' && c == 'l') {
    char *y = tmp();
    emit("%s =l extuw %s", y, x);
    x = y;
  } else if (qc(ft) == 'l' && c == 'w') {
    char *y = tmp();
    emit("%s =w copy %s", y, x);
    x = y;
  }
  char *a = tmp();
  emit("%s =%c and %s, %llu", a, c, x, m);
  if (l.bitoff) {
    char *b = tmp();
    emit("%s =%c shl %s, %d", b, c, a, l.bitoff);
    a = b;
  }
  char *o = load(h, l.op);
  char *k = tmp();
  emit("%s =%c and %s, %llu", k, c, o, ~(m << l.bitoff) & (l.hbytes == 8 ? ~0ULL : ((1ULL << (l.hbytes * 8)) - 1)));
  char *r = tmp();
  emit("%s =%c or %s, %s", r, c, k, a);
  store(h, r, l.op);
}
Val rv(Val v) {
  if (!v.t) {
    Node *cn = gen_cur_pub();
    die("%s:%d: internal: value without type", cn ? cn->tok->file : "?", cn ? cn->tok->line : 0);
  }
  if (v.ck || !v.lv) return v;
  if (v.bf) {
    if (bf_needs_wide(&v) && bits_of(v.t) > 64) return V(v.t, bf_load(v)); /* slot holding the field */
    char *x = bf_load(v);
    if (is_aggr(v.t)) {
      char *sl = slot(v.t);
      store(int_type(tsize(v.t) * 8, 0), x, sl);
      return V(v.t, sl);
    }
    return V(v.t, x);
  }
  if (is_aggr(v.t)) return V(v.t, v.op);
  return V(v.t, load(v.t, v.op));
}
char *opnd(Val v) {
  return mat(rv(v));
}
char *addr_of(Val v) {
  if (v.ck) {
    if (v.cv.k == CV_STR && !is_aggr(v.t)) return mat(v);
    if (is_aggr(v.t) && v.cv.k != CV_UNDEF && !(v.cv.k == CV_NULL && v.t->k == TY_OPT)) return cv_data(&v.cv, v.t);
    if (!is_aggr(v.t) && v.cv.k != CV_UNDEF) {
      char *sl = slot(v.t);
      store(v.t, mat(v), sl);
      return sl;
    }
    char *sl = slot(v.t);
    if (v.cv.k == CV_NULL && v.t->k == TY_OPT) store(t_u8, "0", addp(sl, tsize(v.t->elem)));
    return sl;
  }
  return v.op;
}
void put(Val v, Type *t, char *addr) {
  if (v.ck && v.cv.k == CV_UNDEF) {
    if (!is_aggr(t) && tsize(t) > 0) store(t, "0", addr);
    return;
  }
  if (v.t->k == TY_NORET) return;
  if (is_aggr(t))
    blit(addr_of(v), addr, tsize(t));
  else
    store(t, opnd(v), addr);
}
void put_lv(Val v, Val l) {
  if (!l.bf) {
    put(v, l.t, l.op);
    return;
  }
  if (v.ck && v.cv.k == CV_UNDEF) return;
  if (v.t->k == TY_NORET) return;
  if (bf_needs_wide(&l) && bits_of(l.t) > 64) {
    bf_store(l, addr_of(v));
    return;
  } /* wide field: pass its storage */
  if (is_aggr(l.t))
    bf_store(l, load(int_type(tsize(l.t) * 8, 0), addr_of(v)));
  else
    bf_store(l, opnd(v));
}
int is_ptrish(Type *t) {
  return t->k == TY_PTR || t->k == TY_MPTR || t->k == TY_FN || opt_is_ptr(t);
}
Val retype(Val v, Type *t) {
  v = rv(v);
  v.t = t;
  return v;
}

/* ---------- optionals / error unions ---------- */
char *opt_has(Val v) {
  char *r = tmp();
  if (opt_is_ptr(v.t)) {
    emit("%s =w cnel %s, 0", r, opnd(v));
    return r;
  }
  return load(t_u8, addp(addr_of(v), tsize(v.t->elem)));
}
Val opt_payload(Val v, char *ptrval) {
  if (opt_is_ptr(v.t)) return V(v.t->elem, ptrval ? ptrval : opnd(v));
  return LV(v.t->elem, addr_of(v));
}
void bind_local(Scope *s, char *name, Type *t, char *addr) {
  Sym *y = xalloc(sizeof *y);
  y->name = name;
  y->k = S_LOCAL;
  y->t = t;
  y->addr = addr;
  vpush(&s->syms, y);
}
void bind_val(Scope *s, char *name, Val v) {
  if (!name || !strcmp(name, "_")) return;
  if (v.ck) {
    if (type_is_ctonly(v.t) || v.cv.k == CV_FN) {
      CVal c = v.cv;
      bind_cval(s, name, c);
      return;
    }
  }
  if (is_aggr(v.t)) {
    bind_local(s, name, v.t, addr_of(v));
    return;
  }
  char *sl = slot(v.t);
  store(v.t, opnd(v), sl);
  bind_local(s, name, v.t, sl);
}
void res_put(Res *r, Val v) {
  if (v.t->k == TY_NORET || term) return;
  if (r->collect) {
    Type *p = peer_t(r->t, v.t);
    r->t = p ? p : r->t;
    r->has = 1;
    return;
  }
  if (!r->t) {
    r->t = r->ex ? r->ex : v.t;
    if (r->ex && is_tuple_type(r->ex)) {
      layout(r->ex->ct);
      for (int i = 0; i < r->ex->ct->fields.n; i++)
        if (((Field *)r->ex->ct->fields.a[i])->t->k == TY_ANYTYPE) {
          r->t = coerce(v, r->ex).t;
          break;
        }
    }
    if (r->t->k == TY_CINT) r->t = t_i64;
    if (r->t->k == TY_ENUMLIT || r->t->k == TY_NULL) die("cannot infer type of branch result");
    if (r->t->k != TY_VOID && r->t->k != TY_TYPE && tsize(r->t) > 0) {
      r->slot = slot(r->t);
      int z = tsize(r->t);
      if (z <= 8) fprintf(ab, "\tstore%s 0, %s\n", z == 1 ? "b" : z == 2 ? "h" : z <= 4 ? "w" : "l", r->slot);
    } /* defined even if only void breaks reach it */
  }
  r->has = 1;
  if (r->t->k == TY_VOID) return;
  if (v.t->k == TY_VOID && discarding) return; /* mixed void/value peers (only valid when the result is discarded) */
  v = coerce(v, r->t);
  if (r->slot) put(v, r->t, r->slot);
}
Val res_get(Res *r) {
  if (!r->has) {
    if (!term) emit("hlt");
    term = 1;
    return NORET();
  }
  if (!r->slot) return V(r->t ? r->t : t_void, "0");
  return rv(LV(r->t, r->slot));
}

/* ---------- defers ---------- */
void run_defers(int base, char *errop) {
  for (int i = defers.n - 1; i >= base; i--) {
    Defer *d = defers.a[i];
    if (d->err && !errop) continue;
    if (term) return;
    if (d->err && d->n->k == N_BUILTIN && !strcmp(d->n->s, "compileError"))
      continue; /* guard against error paths that zb cannot prove impossible */
    Scope *s = d->s;
    if (d->err && d->cap) {
      s = new_scope(s, NULL);
      bind_val(s, d->cap, V(t_errset, errop));
    }
    int save = defers.n;
    gen(d->n, s, NULL);
    defers.n = save;
  }
}
int have_errdefer(int base) {
  for (int i = base; i < defers.n; i++)
    if (((Defer *)defers.a[i])->err) return 1;
  return 0;
}
char *tagname_fn(Type *et) {
  for (int i = 0; i < tagfns.n; i++)
    if (tagfns.a[i] == et) return et->ct->tagnames_sym;
  vpush(&tagfns, et);
  Container *c = et->ct;
  layout(c);
  char *sym = fmt("zb.tagName.%d", tagfns.n);
  c->tagnames_sym = sym;
  fprintf(xb, "function l $%s(w %%v) {\n@start\n", sym);
  for (int i = 0; i < c->fields.n; i++) {
    Field *f = c->fields.a[i];
    char *s = strdata(f->name, strlen(f->name));
    fprintf(db, "data $%s.%d = { l %s, l %d }\n", sym, i, s, (int)strlen(f->name));
    fprintf(xb, "\t%%c%d =w ceqw %%v, %lld\n\tjnz %%c%d, @y%d, @n%d\n@y%d\n\tret $%s.%d\n@n%d\n", i, (long long)f->val,
            i, i, i, i, sym, i, i);
  }
  fprintf(xb, "\thlt\n}\n");
  return sym;
}
