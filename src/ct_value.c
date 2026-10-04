#include "ct_int.h"

/* ---------- value constructors ---------- */
long double f16_round_ld(long double f) { /* round to nearest binary16 (11-bit significand) */
  if (f != f || f == 0 || isinf(f)) return f;
  int e;
  frexpl(f, &e);
  if (e > 16) return f > 0 ? INFINITY : -INFINITY;
  int p = e - 11;
  if (p < -24) p = -24;
  long double sc = ldexpl(1, -p);
  return nearbyintl(f * sc) / sc;
}
int f128_isnan(f128 x) {
  return x != x;
}
int f128_isinf(f128 x) {
  return x == x && x - x != x - x;
}
f128 f128_trunc(f128 x) {
  if (f128_isnan(x) || f128_isinf(x)) return x;
  f128 a = x < 0 ? -x : x;
  if (a >= (f128)5192296858534827628530496329220096.0L /* 2^112 */) return x;
  f128 r = (f128)(i128)x;
  return r == 0 && x < 0 ? -r : r;
}
f128 f128_floor(f128 x) {
  f128 t = f128_trunc(x);
  return t > x ? t - 1 : t;
}
f128 f128_ceil(f128 x) {
  f128 t = f128_trunc(x);
  return t < x ? t + 1 : t;
}
f128 f128_round(f128 x) {
  f128 a = x < 0 ? -x : x, r = f128_floor(a + (f128)0.5);
  if (r - a == (f128)0.5 && 0) r -= 1;
  return x < 0 ? -r : r;
}
f128 f128_sqrt(f128 x) {
  if (!(x > 0)) return x == 0 ? x : (f128)NAN;
  f128 r = (f128)sqrtl((long double)x);
  if (f128_isinf(r)) return r;
  r = (r + x / r) / 2;
  return r;
}
f128 fround(f128 f, Type *t) {
  if (!t || t->k != TY_FLOAT) return f;
  switch (t->bits) {
  case 16: return (f128)f16_round_ld((long double)f);
  case 32: return (f128)(float)f;
  case 64: return (f128)(double)f;
  case 80: return (f128)(long double)f;
  default: return f;
  }
}
CVal cv_float(f128 f, Type *t) {
  CVal v = {0};
  v.k = CV_FLOAT;
  v.f = f;
  v.t = t ? t : t_cfloat;
  return v;
}
CVal cv_int(i128 i, Type *t) {
  CVal v = {0};
  v.k = CV_INT;
  v.i = i;
  v.t = t ? t : t_cint;
  return v;
}
CVal cv_bool(int b) {
  CVal v = {0};
  v.k = CV_BOOL;
  v.i = !!b;
  v.t = t_bool;
  return v;
}
CVal cv_ty(Type *t) {
  CVal v = {0};
  v.k = CV_TYPE;
  v.t = t;
  return v;
}
CVal cv_void(void) {
  CVal v = {0};
  v.k = CV_VOID;
  v.t = t_void;
  return v;
}
CVal cv_null(void) {
  CVal v = {0};
  v.k = CV_NULL;
  v.t = t_null;
  return v;
}
CVal cv_undef(Type *t) {
  CVal v = {0};
  v.k = CV_UNDEF;
  v.t = t ? t : t_undef;
  return v;
}
CVal cv_enumlit(const char *s) {
  CVal v = {0};
  v.k = CV_ENUMLIT;
  v.s = (char *)s;
  v.t = t_enumlit;
  return v;
}
CVal cv_str(const char *s, int len) {
  CVal v = {0};
  v.k = CV_STR;
  v.s = (char *)s;
  v.slen = len;
  return v;
}
CVal *box(CVal v) {
  CVal *p = xalloc(sizeof *p);
  *p = v;
  return p;
}
CVal cv_copy(CVal v) {
  if (v.k != CV_AGG) return v;
  CVal r = v;
  r.el = xalloc(sizeof(CVal *) * (v.n + 1));
  for (int i = 0; i < v.n; i++) r.el[i] = box(cv_copy(*v.el[i]));
  return r;
}
int cv_is_mem(CVal *v) {
  return v->k == CV_AGG || v->k == CV_PTR || v->k == CV_SLICE;
}
Type *str_type(CVal *v) {
  return ptr_to(array_of(t_u8, v->slen, 1, 0), 1);
}
Type *cv_typeof(CVal *v) {
  switch (v->k) {
  case CV_INT: return v->t ? v->t : t_cint;
  case CV_FLOAT: return v->t ? v->t : t_cfloat;
  case CV_BOOL: return t_bool;
  case CV_TYPE: return t_type;
  case CV_NULL: return v->t ? v->t : t_null;
  case CV_UNDEF: return v->t ? v->t : t_undef;
  case CV_ENUMLIT: return t_enumlit;
  case CV_ERR: return v->t ? v->t : t_errset;
  case CV_VOID: return t_void;
  case CV_STR: return v->t ? v->t : str_type(v);
  case CV_AGG:
  case CV_PTR:
  case CV_SLICE: return v->t;
  case CV_FN: return v->t ? v->t : t_anytype;
  default: return t_void;
  }
}
int ctonly_rec(Type *t, int depth) {
  if (depth > 8) return 0;
  switch (t->k) {
  case TY_CINT:
  case TY_CFLOAT:
  case TY_TYPE:
  case TY_ENUMLIT:
  case TY_NULL:
  case TY_UNDEF:
  case TY_ANYTYPE: return 1;
  case TY_PTR:
  case TY_SLICE:
  case TY_MPTR: /* don't force layout through pointers (self-referential types) */
    if (t->elem->ct && (t->elem->k == TY_STRUCT || t->elem->k == TY_UNION) && !t->elem->ct->laid) return 0;
    return ctonly_rec(t->elem, depth + 1);
  case TY_OPT:
  case TY_ARRAY:
  case TY_ERRU: return ctonly_rec(t->elem, depth + 1);
  case TY_STRUCT:
  case TY_UNION:
  case TY_TUPLE:
    if (!t->ct || (t->ct->laying && !t->ct->laid)) return 0;
    layout(t->ct);
    for (int i = 0; i < t->ct->fields.n; i++) {
      Field *f = t->ct->fields.a[i];
      if (f->t && ctonly_rec(f->t, depth + 1)) return 1;
    }
    return 0;
  case TY_FN: return 0;
  default: return 0;
  }
}
int type_is_ctonly(Type *t) {
  return t && ctonly_rec(t, 0);
}
int is_packed(Type *t) {
  return t && t->k == TY_STRUCT && t->ct && t->ct->packed;
}

/* ---------- containers / fields ---------- */
Field *field_at(Type *t, int i) {
  layout(t->ct);
  return t->ct->fields.a[i];
}
int field_index(Type *t, const char *name) {
  if (!t->ct) return -1;
  layout(t->ct);
  for (int i = 0; i < t->ct->fields.n; i++)
    if (!strcmp(((Field *)t->ct->fields.a[i])->name, name)) return i;
  return -1;
}
CVal agg_new(Type *t) {
  CVal a = {0};
  a.k = CV_AGG;
  a.t = t;
  if (t->k == TY_ARRAY) {
    a.n = (int)t->len;
    a.el = xalloc(sizeof(CVal *) * (a.n + 1));
    for (int i = 0; i < a.n; i++) a.el[i] = box(cv_undef(t->elem));
  } else if (t->k == TY_UNION) {
    a.n = 1;
    a.el = xalloc(sizeof(CVal *) * 2);
    a.el[0] = box(cv_undef(NULL));
    a.i = -1;
  } else {
    layout(t->ct);
    a.n = t->ct->fields.n;
    a.el = xalloc(sizeof(CVal *) * (a.n + 1));
    for (int i = 0; i < a.n; i++) a.el[i] = box(cv_undef(field_at(t, i)->t));
  }
  return a;
}
int is_struct_like(Type *t) {
  return t && (t->k == TY_STRUCT || t->k == TY_TUPLE);
}
int is_tuple_type(Type *t) {
  return is_struct_like(t) && t->ct && t->ct->is_tuple;
}
int is_anon(Type *t) {
  return is_struct_like(t) && t->ct && t->ct->name &&
         (!strcmp(t->ct->name, "anon_struct") || !strcmp(t->ct->name, "tuple"));
}
Type *mk_anon_struct(Vec *names, Vec *types, int tuple) {
  unsigned h = tuple * 31u + types->n;
  for (int i = 0; i < types->n; i++) {
    h = h * 1000003u ^ (unsigned)(uintptr_t)types->a[i];
    for (const char *q = names->a[i]; q && *q; q++) h = h * 33u + (unsigned char)*q;
  }
  for (AnonE *e = anon_tab[h % ANON_HB]; e; e = e->next) {
    if (e->h != h) continue;
    Container *ec = e->t->ct;
    if (ec->is_tuple != tuple || ec->fields.n != types->n) continue;
    int ok = 1;
    for (int i = 0; ok && i < types->n; i++) {
      Field *f = ec->fields.a[i];
      if (f->t != types->a[i] || strcmp(f->name, names->a[i])) ok = 0;
    }
    if (ok) return e->t;
  }
  Type *nt = mk_anon_struct_new(names, types, tuple);
  AnonE *e = xalloc(sizeof *e);
  e->h = h;
  e->t = nt;
  e->next = anon_tab[h % ANON_HB];
  anon_tab[h % ANON_HB] = e;
  return nt;
}
int ctf_eq(CVal *a, CVal *b) {
  if (!a || !b) return a == b;
  if (a->k != b->k) return 0;
  if (a->k == CV_ENUMLIT) return !strcmp(a->s, b->s);
  if (a->k == CV_TYPE) return a->t == b->t;
  return 0;
}
Type *mk_anon_struct_cv(Vec *names, Vec *types, int tuple, CVal **cts) {
  unsigned h = tuple * 31u + types->n;
  for (int i = 0; i < types->n; i++) {
    h = h * 1000003u ^ (unsigned)(uintptr_t)types->a[i];
    for (const char *q = names->a[i]; q && *q; q++) h = h * 33u + (unsigned char)*q;
    if (cts[i] && cts[i]->k == CV_ENUMLIT)
      for (const char *q = cts[i]->s; *q; q++) h = h * 37u + (unsigned char)*q;
    if (cts[i] && cts[i]->k == CV_TYPE) h = h * 41u ^ (unsigned)(uintptr_t)cts[i]->t;
  }
  for (AnonE *e = anon_ct_tab[h % ANON_CT_HB]; e; e = e->next) {
    if (e->h != h) continue;
    Container *ec = e->t->ct;
    if (ec->is_tuple != tuple || ec->fields.n != types->n) continue;
    int ok = 1;
    for (int i = 0; ok && i < types->n; i++) {
      Field *f = ec->fields.a[i];
      if (f->t != types->a[i] || strcmp(f->name, names->a[i]) || !f->is_ct != !cts[i] ||
          (cts[i] && !ctf_eq(f->defcv, cts[i])))
        ok = 0;
    }
    if (ok) return e->t;
  }
  Type *nt = mk_anon_struct_new(names, types, tuple);
  for (int i = 0; i < types->n; i++)
    if (cts[i]) {
      Field *f = nt->ct->fields.a[i];
      f->is_ct = 1;
      CVal *b = xalloc(sizeof *b);
      *b = *cts[i];
      f->defcv = b;
    }
  AnonE *e = xalloc(sizeof *e);
  e->h = h;
  e->t = nt;
  e->next = anon_ct_tab[h % ANON_CT_HB];
  anon_ct_tab[h % ANON_CT_HB] = e;
  return nt;
}
Type *mk_anon_struct_new(Vec *names, Vec *types, int tuple) {
  Container *c = xalloc(sizeof *c);
  c->name = tuple ? "tuple" : "anon_struct";
  c->is_tuple = tuple;
  Type *t = xalloc(sizeof *t);
  t->k = TY_STRUCT;
  t->ct = c;
  c->type = t;
  t->size = -1;
  int off = 0, al = 1;
  for (int i = 0; i < types->n; i++) {
    Field *f = xalloc(sizeof *f);
    f->name = names->a[i];
    f->t = types->a[i];
    int a = talign(f->t);
    if (a < 1) a = 1;
    if (a > al) al = a;
    off = (off + a - 1) / a * a;
    f->off = off;
    off += tsize(f->t);
    vpush(&c->fields, f);
  }
  t->align = al;
  t->size = (off + al - 1) / al * al;
  c->laid = 1;
  return t;
}

/* ---------- memory access ---------- */
int cv_len(CVal *v, int64_t *len) {
  switch (v->k) {
  case CV_STR: *len = v->slen; return 1;
  case CV_AGG:
    if (v->t->k == TY_ARRAY || is_struct_like(v->t)) {
      *len = v->n;
      return 1;
    }
    return 0;
  case CV_SLICE: *len = v->slen; return 1;
  case CV_PTR:
    if (v->idx < 0 && v->base) return cv_len(v->base, len);
    if (v->t && v->t->k == TY_PTR && v->t->elem->k == TY_ARRAY) {
      *len = v->t->elem->len;
      return 1;
    }
    return 0;
  case CV_UNDEF:
    if (v->t && v->t->k == TY_ARRAY) {
      *len = v->t->len;
      return 1;
    }
    return 0;
  default: return 0;
  }
}
CVal cv_elem(CVal *v, int64_t i) {
  if (v->k == CV_STR) {
    if (i < 0 || i > v->slen) die("comptime index %lld out of bounds", (long long)i);
    return cv_int(i == v->slen ? 0 : (unsigned char)v->s[i], t_u8);
  }
  if (v->k == CV_SLICE && v->base && v->base->k == CV_STR) return cv_int((unsigned char)v->base->s[v->idx + i], t_u8);
  if (v->k == CV_PTR && v->base && v->base->k == CV_STR)
    return cv_int((unsigned char)v->base->s[(v->idx < 0 ? 0 : v->idx) + i], t_u8);
  if (v->k == CV_UNDEF) return cv_undef(v->t && v->t->k == TY_ARRAY ? v->t->elem : NULL);
  CVal *c = elem_cell(v, i);
  if (!c) die("bad comptime element access");
  return *c;
}
CVal *elem_cell(CVal *v, int64_t i) {
  if (v->k == CV_UNDEF && v->t && v->t->k == TY_ARRAY) *v = agg_new(v->t);
  switch (v->k) {
  case CV_AGG:
    if (i < 0 || i >= v->n) {
      if (v->t && v->t->k == TY_ARRAY && v->t->hassent && i == v->n) return box(cv_int(v->t->sent, v->t->elem));
      die("%s:%d: comptime index %lld out of bounds (len %d)", ev_cur ? ev_cur->tok->file : "?",
          ev_cur ? ev_cur->tok->line : 0, (long long)i, v->n);
    }
    return v->el[i];
  case CV_SLICE: return v->base ? elem_cell(v->base, v->idx + i) : NULL;
  case CV_PTR:
    if (!v->base) return NULL;
    if (v->idx < 0) return elem_cell(v->base, i);
    return elem_cell(v->base, v->idx + i);
  default: return NULL;
  }
}
CVal *deref_cell(CVal *p) {
  if (p->k != CV_PTR || !p->base) return NULL;
  if (p->idx < 0) return p->base;
  if (p->t && p->t->k == TY_PTR && p->t->elem->k == TY_ARRAY && !is_vec(p->t->elem) &&
      (p->base->k == CV_STR ||
       (p->base->k == CV_AGG && cv_typeof(p->base)->k == TY_ARRAY && cv_typeof(p->base)->elem != p->t->elem))) {
    /* pointer to a sub-array view */
    Type *at = p->t->elem;
    if (p->base->k == CV_AGG && p->idx == 0 && at->len == p->base->n) return p->base;
    CVal r = agg_new(at);
    for (int64_t i = 0; i < at->len; i++) {
      if (p->base->k == CV_STR)
        *r.el[i] = cv_int(p->idx + i < p->base->slen ? (unsigned char)p->base->s[p->idx + i] : 0, t_u8);
      else if (p->idx + i < p->base->n)
        *r.el[i] = cv_copy(*p->base->el[p->idx + i]);
    }
    return box(r);
  }
  if (p->base->k == CV_STR) return box(cv_int((unsigned char)p->base->s[p->idx], t_u8));
  return elem_cell(p->base, p->idx);
}
/* assignment into a cell, keeping cells (and pointers to elements) alive */
void assign(CVal *cell, CVal v) {
  if (cell->k == CV_AGG && v.k == CV_AGG && cell->t == v.t && cell->n == v.n && cell->t->k != TY_UNION && cell != &v) {
    CVal tmpv = cv_copy(v);
    for (int i = 0; i < v.n; i++) assign(cell->el[i], *tmpv.el[i]);
    return;
  }
  *cell = cv_copy(v);
}

/* ---------- equality (memoization of generic instances) ---------- */
int cval_eq(CVal *a, CVal *b) {
  if (!a || !b) return a == b;
  if (a->k != b->k) return 0;
  switch (a->k) {
  case CV_TYPE: return a->t == b->t && a->slen == b->slen;
  case CV_INT:
  case CV_BOOL:
  case CV_ERR:
    return a->i == b->i &&
           (a->k != CV_INT || cv_typeof(a) == cv_typeof(b) || cv_typeof(a)->k == TY_CINT || cv_typeof(b)->k == TY_CINT);
  case CV_FN: return a->fn == b->fn;
  case CV_FLOAT: return a->t == b->t && (a->f == b->f || (a->f != a->f && b->f != b->f));
  case CV_ENUMLIT: return !strcmp(a->s, b->s);
  case CV_STR: return a->slen == b->slen && !memcmp(a->s, b->s, a->slen);
  case CV_AGG:
    if (a->t != b->t || a->n != b->n || a->i != b->i) return 0;
    for (int i = 0; i < a->n; i++)
      if (!cval_eq(a->el[i], b->el[i])) return 0;
    return 1;
  case CV_PTR:
    return a->base == b->base && a->idx == b->idx && a->t == b->t && a->i == b->i &&
           (a->s == b->s || (a->s && b->s && !strcmp(a->s, b->s)));
  case CV_SLICE: return a->base == b->base && a->idx == b->idx && a->slen == b->slen;
  case CV_NULL:
  case CV_VOID:
  case CV_UNDEF: return 1;
  default: return 1;
  }
}

/* ---------- coercion ---------- */
CVal mk_splat(CVal v) {
  if (!t_splat) {
    t_splat = xalloc(sizeof *t_splat);
    t_splat->k = TY_VOID;
    t_splat->name = "@splat";
    t_splat->size = 0;
    t_splat->align = 1;
  }
  CVal a = {0};
  a.k = CV_AGG;
  a.t = t_splat;
  a.n = 1;
  a.el = xalloc(sizeof(CVal *));
  a.el[0] = box(v);
  return a;
}
CVal ccoerce(CVal v, Type *t) {
  if (!t || t->k == TY_ANYTYPE) return v;
  if (t_splat && v.k == CV_AGG && v.t == t_splat && t->k == TY_ARRAY) {
    CVal a = agg_new(t);
    for (int i = 0; i < a.n; i++) *a.el[i] = ccoerce(*v.el[0], t->elem);
    return a;
  }
  switch (v.k) {
  case CV_UNDEF:
    if (t->k != TY_UNDEF) v.t = t;
    return v;
  case CV_INT:
    if (t->k == TY_INT || t->k == TY_CINT) {
      v.t = t;
      v.i = wrap_int(v.i, t);
      if (t->k == TY_INT) v.big = 0;
      return v;
    }
    if (is_float(t)) return cv_float(fround((f128)v.i, t), t);
    if (t->k == TY_ENUM) {
      v.t = t;
      return v;
    }
    if (t->k == TY_OPT || t->k == TY_ERRU) return ccoerce(v, t->elem);
    if (t->k == TY_PTR || t->k == TY_MPTR || t->k == TY_FN) {
      v.t = t;
      return v;
    }
    if (t->k == TY_BOOL) return v;
    if (is_vec(t)) {
      CVal a = agg_new(t);
      for (int i = 0; i < a.n; i++) *a.el[i] = ccoerce(v, t->elem);
      return a;
    }
    return v;
  case CV_ENUMLIT:
    if (t->k == TY_OPT || t->k == TY_ERRU) return ccoerce(v, t->elem);
    if (t->k == TY_ENUM) {
      int64_t x;
      if (enum_val(t, v.s, &x)) return cv_int(x, t);
      Decl *d = find_decl(t->ct, v.s);
      if (d) {
        resolve_decl(d);
        if (d->kind == D_CONST) return ccoerce(d->cv, t);
      }
      die("no enum field .%s in %s", v.s, tname(t));
    }
    if (t->k == TY_UNION && t->ct && find_field(t->ct, v.s)) {
      CVal a = agg_new(t);
      a.i = field_index(t, v.s);
      *a.el[0] = cv_void();
      return a;
    }
    if (t->ct && (t->k == TY_STRUCT || t->k == TY_UNION || t->k == TY_OPAQUE)) {
      Decl *d = find_decl(t->ct, v.s);
      if (d) {
        resolve_decl(d);
        if (d->kind == D_CONST) return ccoerce(d->cv, t);
      }
    }
    return v;
  case CV_FLOAT:
    if (is_float(t)) return cv_float(fround(v.f, t), t);
    if (t->k == TY_INT || t->k == TY_CINT) return cv_int(wrap_int((i128)v.f, t), t);
    if (t->k == TY_OPT || t->k == TY_ERRU) return ccoerce(v, t->elem);
    if (is_vec(t)) {
      CVal a = agg_new(t);
      for (int i = 0; i < a.n; i++) *a.el[i] = ccoerce(v, t->elem);
      return a;
    }
    return v;
  case CV_NULL:
    if (t->k == TY_OPT) {
      if (v.t && v.t->k == TY_OPT && t->elem == v.t) v.slen++;
      v.t = t;
    }
    return v;
  case CV_ERR:
    if (t->k == TY_ERRSET || t->k == TY_ERRU) v.t = t;
    return v;
  case CV_STR:
    if (t->k == TY_OPT || t->k == TY_ERRU) return ccoerce(v, t->elem);
    if (t->k == TY_ARRAY) {
      CVal a = agg_new(t);
      for (int i = 0; i < a.n && i < v.slen; i++) *a.el[i] = cv_int((unsigned char)v.s[i], t->elem);
      return a;
    }
    if (t->k == TY_SLICE || t->k == TY_MPTR || t->k == TY_PTR) {
      v.t = t;
      return v;
    }
    return v;
  case CV_AGG: {
    Type *f = v.t;
    if (f == t) return v;
    if (t->k == TY_OPT || t->k == TY_ERRU) return ccoerce(v, t->elem);
    if (f->k == TY_ARRAY && t->k == TY_SLICE && f->elem == t->elem) {
      CVal r = {0};
      r.k = CV_SLICE;
      r.base = box(cv_copy(v));
      r.idx = 0;
      r.slen = v.n;
      r.t = t;
      return r;
    }
    if (f->k == TY_ARRAY && t->k == TY_ARRAY && f->len == t->len) {
      CVal a = v;
      a.t = t;
      a.el = xalloc(sizeof(CVal *) * (v.n + 1));
      for (int i = 0; i < v.n; i++) a.el[i] = box(ccoerce(*v.el[i], t->elem));
      return a;
    }
    if (is_struct_like(f) && t->k == TY_ARRAY && (is_anon(f) || is_tuple_type(f))) {
      CVal a = agg_new(t);
      for (int i = 0; i < a.n && i < v.n; i++) *a.el[i] = ccoerce(*v.el[i], t->elem);
      return a;
    }
    if (is_struct_like(f) && is_struct_like(t) && (is_anon(f) || (is_tuple_type(f) && is_tuple_type(t)))) {
      CVal a = agg_new(t);
      int tup = is_tuple_type(f);
      char *set = xalloc(a.n + 1);
      for (int i = 0; i < v.n; i++) {
        int fi = tup ? i : field_index(t, field_at(f, i)->name);
        if (fi < 0 || fi >= a.n) continue;
        *a.el[fi] = ccoerce(*v.el[i], field_at(t, fi)->t);
        set[fi] = 1;
      }
      for (int i = 0; i < a.n; i++)
        if (!set[i]) *a.el[i] = default_of(t, field_at(t, i));
      return a;
    }
    if (is_struct_like(f) && t->k == TY_UNION && is_anon(f) && v.n == 1) {
      CVal a = agg_new(t);
      a.i = field_index(t, field_at(f, 0)->name);
      if (a.i < 0) return v;
      *a.el[0] = ccoerce(*v.el[0], field_at(t, (int)a.i)->t);
      return a;
    }
    if (f->k == TY_UNION && t->k == TY_ENUM && v.i >= 0) {
      int64_t x;
      enum_val(t, field_at(f, (int)v.i)->name, &x);
      return cv_int(x, t);
    }
    return v;
  }
  case CV_PTR: {
    Type *f = v.t;
    if (t->k == TY_OPT && t->elem->k != TY_OPT) {
      CVal r = ccoerce(v, t->elem);
      return r;
    }
    if (t->k == TY_ERRU) return ccoerce(v, t->elem);
    if (t->k == TY_SLICE && v.base && f && f->k == TY_PTR && f->elem->k == TY_ARRAY && v.idx >= 0 &&
        (v.base->k == CV_STR ||
         (v.base->k == CV_AGG && cv_typeof(v.base)->k == TY_ARRAY && cv_typeof(v.base)->elem != f->elem))) {
      int64_t len = f->elem->len; /* pointer to a sub-array view of base */
      if (v.base->k == CV_STR) {
        CVal r = cv_str(v.base->s + v.idx, (int)len);
        r.t = t;
        return r;
      }
      CVal r = {0};
      r.k = CV_SLICE;
      r.base = v.base;
      r.idx = v.idx;
      r.slen = (int)len;
      r.t = t;
      return r;
    }
    if (t->k == TY_SLICE && v.base && f && f->k == TY_PTR && f->elem->k == TY_ARRAY) {
      CVal *arr = deref_cell(&v);
      int64_t len = f->elem->len;
      if (arr && arr->k == CV_STR) {
        CVal r = *arr;
        r.t = t;
        return r;
      }
      CVal r = {0};
      r.k = CV_SLICE;
      r.base = arr;
      r.idx = 0;
      r.slen = (int)len;
      r.t = t;
      return r;
    }
    if ((t->k == TY_SLICE || t->k == TY_MPTR) && v.base && f && f->k == TY_PTR && is_struct_like(f->elem) &&
        f->elem->ct && f->elem->ct->is_tuple) {
      CVal *tu = deref_cell(&v);
      if (tu && (tu->k == CV_AGG || tu->k == CV_UNDEF)) {
        int nn = tu->k == CV_AGG ? tu->n : 0;
        CVal arr = agg_new(array_of(t->elem, nn, 0, 0));
        for (int i = 0; i < nn; i++) *arr.el[i] = ccoerce(cv_copy(*tu->el[i]), t->elem);
        CVal r = {0};
        r.k = t->k == TY_SLICE ? CV_SLICE : CV_PTR;
        r.base = box(arr);
        r.idx = 0;
        r.slen = nn;
        r.t = t;
        return r;
      }
    }
    if (t->k == TY_MPTR && v.base && f && f->k == TY_PTR && f->elem->k == TY_ARRAY && v.idx < 0) {
      CVal r = v;
      r.idx = 0;
      r.t = t;
      return r;
    }
    if (t->k == TY_PTR || t->k == TY_MPTR || t->k == TY_FN) v.t = t;
    return v;
  }
  case CV_SLICE:
    if (t->k == TY_OPT || t->k == TY_ERRU) return ccoerce(v, t->elem);
    if (t->k == TY_SLICE) {
      v.t = t;
      return v;
    }
    if (t->k == TY_MPTR) {
      CVal r = {0};
      r.k = CV_PTR;
      r.base = v.base;
      r.idx = v.idx;
      r.t = t;
      return r;
    }
    if (t->k == TY_ARRAY) {
      CVal a = agg_new(t);
      for (int i = 0; i < a.n && i < v.slen; i++) *a.el[i] = ccoerce(cv_elem(&v, i), t->elem);
      return a;
    }
    return v;
  case CV_FN:
    if (t->k == TY_FN || t->k == TY_PTR) {
      v.t = t;
      return v;
    }
    if (t->k == TY_OPT) return ccoerce(v, t->elem);
    return v;
  case CV_VOID: return v;
  default: return v;
  }
}
CVal default_of(Type *t, Field *f) {
  if (f->defcv) return *(CVal *)f->defcv;
  if (f->def) {
    CVal d;
    ct_force++;
    int sxs = xs;
    int r = ev_rt(f->def, t->ct->scope, f->t, &d);
    ct_force--;
    xs = sxs;
    if (r == R_OK) return ccoerce(d, f->t);
  }
  return cv_undef(f->t);
}
