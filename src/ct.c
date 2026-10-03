/* ct.c: the comptime interpreter.
   Evaluates AST nodes to CVal values. Used for constant folding (ceval), full comptime
   evaluation (ceval_force: comptime blocks/args/decl initializers), type functions, @typeInfo. */
#include "zb.h"

enum { R_FAIL, R_OK, R_CF };
enum { X_NONE, X_BRK, X_CONT, X_RET };
static int xs; static char *xlabel; static CVal xval;  /* pending control flow (R_CF) */
static int ct_force;      /* >0: comptime context (calls/loops/side effects allowed) */
static long ct_steps;
static Type *cur_rt;      /* return type of the function being interpreted */
static Type *brt;         /* result type for the builtin being evaluated */
static int ct_trace = -1;
static Type *t_splat;     /* marker type for @splat values without a result type */
static char *lrt_l[64]; static Type *lrt_t[64]; static int lrt_n; /* labeled-block result types */

static int ev(Node *n, Scope *s, CVal *out);
static int ev_rt(Node *n, Scope *s, Type *rt, CVal *out);
static int clval(Node *n, Scope *s, CVal **cell);
static int ct_call(Decl *fd, CVal *args, int nargs, CVal *out);
static int ev_builtin(Node *n, Scope *s, CVal *out);
static Node *ev_cur;
const char *ct_cur_loc(void) { return ev_cur && ev_cur->tok ? fmt("%s:%d", ev_cur->tok->file, ev_cur->tok->line) : "?"; }
#define EV(n, s, o) do { int r_ = ev(n, s, o); if (r_ != R_OK) return r_; } while (0)
#define EVR(n, s, t, o) do { int r_ = ev_rt(n, s, t, o); if (r_ != R_OK) return r_; } while (0)

/* ---------- value constructors ---------- */
static long double f16_round_ld(long double f) { /* round to nearest binary16 (11-bit significand) */
  if (f != f || f == 0 || isinf(f)) return f;
  int e; frexpl(f, &e); if (e > 16) return f > 0 ? INFINITY : -INFINITY;
  int p = e - 11; if (p < -24) p = -24; long double sc = ldexpl(1, -p);
  return nearbyintl(f * sc) / sc;
}
int f128_isnan(f128 x) { return x != x; }
int f128_isinf(f128 x) { return x == x && x - x != x - x; }
static f128 f128_trunc(f128 x) { if (f128_isnan(x) || f128_isinf(x)) return x; f128 a = x < 0 ? -x : x; if (a >= (f128)5192296858534827628530496329220096.0L /* 2^112 */) return x; f128 r = (f128)(i128)x; return r == 0 && x < 0 ? -r : r; }
static f128 f128_floor(f128 x) { f128 t = f128_trunc(x); return t > x ? t - 1 : t; }
static f128 f128_ceil(f128 x) { f128 t = f128_trunc(x); return t < x ? t + 1 : t; }
static f128 f128_round(f128 x) { f128 a = x < 0 ? -x : x, r = f128_floor(a + (f128)0.5); if (r - a == (f128)0.5 && 0) r -= 1; return x < 0 ? -r : r; }
static f128 f128_sqrt(f128 x) { if (!(x > 0)) return x == 0 ? x : (f128)NAN; f128 r = (f128)sqrtl((long double)x); if (f128_isinf(r)) return r; r = (r + x / r) / 2; return r; }
f128 fround(f128 f, Type *t) {
  if (!t || t->k != TY_FLOAT) return f;
  switch (t->bits) { case 16: return (f128)f16_round_ld((long double)f); case 32: return (f128)(float)f; case 64: return (f128)(double)f; case 80: return (f128)(long double)f; default: return f; }
}
CVal cv_float(f128 f, Type *t) { CVal v = {0}; v.k = CV_FLOAT; v.f = f; v.t = t ? t : t_cfloat; return v; }
CVal cv_int(i128 i, Type *t) { CVal v = {0}; v.k = CV_INT; v.i = i; v.t = t ? t : t_cint; return v; }
CVal cv_bool(int b) { CVal v = {0}; v.k = CV_BOOL; v.i = !!b; v.t = t_bool; return v; }
CVal cv_ty(Type *t) { CVal v = {0}; v.k = CV_TYPE; v.t = t; return v; }
CVal cv_void(void) { CVal v = {0}; v.k = CV_VOID; v.t = t_void; return v; }
static CVal cv_null(void) { CVal v = {0}; v.k = CV_NULL; v.t = t_null; return v; }
#define ISNULL(v) ((v).k == CV_NULL && (v).slen <= 0)
static CVal unwrap_some_null(CVal v) { v.slen--; if (v.t && v.t->k == TY_OPT) v.t = v.t->elem; return v; }
static CVal cv_undef(Type *t) { CVal v = {0}; v.k = CV_UNDEF; v.t = t ? t : t_undef; return v; }
static CVal cv_enumlit(const char *s) { CVal v = {0}; v.k = CV_ENUMLIT; v.s = (char *)s; v.t = t_enumlit; return v; }
CVal cv_str(const char *s, int len) { CVal v = {0}; v.k = CV_STR; v.s = (char *)s; v.slen = len; return v; }
CVal *box(CVal v) { CVal *p = xalloc(sizeof *p); *p = v; return p; }
CVal cv_copy(CVal v) {
  if (v.k != CV_AGG) return v;
  CVal r = v; r.el = xalloc(sizeof(CVal *) * (v.n + 1));
  for (int i = 0; i < v.n; i++) r.el[i] = box(cv_copy(*v.el[i]));
  return r;
}
int cv_is_mem(CVal *v) { return v->k == CV_AGG || v->k == CV_PTR || v->k == CV_SLICE; }
static Type *str_type(CVal *v) { return ptr_to(array_of(t_u8, v->slen, 1, 0), 1); }
Type *cv_typeof(CVal *v) {
  switch (v->k) {
  case CV_INT: return v->t ? v->t : t_cint;
  case CV_FLOAT: return v->t ? v->t : t_cfloat;
  case CV_BOOL: return t_bool; case CV_TYPE: return t_type;
  case CV_NULL: return v->t ? v->t : t_null;
  case CV_UNDEF: return v->t ? v->t : t_undef;
  case CV_ENUMLIT: return t_enumlit;
  case CV_ERR: return v->t ? v->t : t_errset;
  case CV_VOID: return t_void;
  case CV_STR: return v->t ? v->t : str_type(v);
  case CV_AGG: case CV_PTR: case CV_SLICE: return v->t;
  case CV_FN: return v->t ? v->t : t_anytype;
  default: return t_void;
  }
}
static int ctonly_rec(Type *t, int depth) {
  if (depth > 8) return 0;
  switch (t->k) {
  case TY_CINT: case TY_CFLOAT: case TY_TYPE: case TY_ENUMLIT: case TY_NULL: case TY_UNDEF: case TY_ANYTYPE: return 1;
  case TY_PTR: case TY_SLICE: case TY_MPTR: /* don't force layout through pointers (self-referential types) */
    if (t->elem->ct && (t->elem->k == TY_STRUCT || t->elem->k == TY_UNION) && !t->elem->ct->laid) return 0;
    return ctonly_rec(t->elem, depth + 1);
  case TY_OPT: case TY_ARRAY: case TY_ERRU: return ctonly_rec(t->elem, depth + 1);
  case TY_STRUCT: case TY_UNION: case TY_TUPLE:
    if (!t->ct || (t->ct->laying && !t->ct->laid)) return 0;
    layout(t->ct);
    for (int i = 0; i < t->ct->fields.n; i++) { Field *f = t->ct->fields.a[i]; if (f->t && ctonly_rec(f->t, depth + 1)) return 1; }
    return 0;
  case TY_FN: return 0;
  default: return 0;
  }
}
int type_is_ctonly(Type *t) { return t && ctonly_rec(t, 0); }
int is_packed(Type *t) { return t && t->k == TY_STRUCT && t->ct && t->ct->packed; }

/* ---------- containers / fields ---------- */
Field *field_at(Type *t, int i) { layout(t->ct); return t->ct->fields.a[i]; }
int field_index(Type *t, const char *name) {
  if (!t->ct) return -1; layout(t->ct);
  for (int i = 0; i < t->ct->fields.n; i++) if (!strcmp(((Field *)t->ct->fields.a[i])->name, name)) return i;
  return -1;
}
static CVal agg_new(Type *t) {
  CVal a = {0}; a.k = CV_AGG; a.t = t;
  if (t->k == TY_ARRAY) {
    a.n = (int)t->len; a.el = xalloc(sizeof(CVal *) * (a.n + 1));
    for (int i = 0; i < a.n; i++) a.el[i] = box(cv_undef(t->elem));
  } else if (t->k == TY_UNION) {
    a.n = 1; a.el = xalloc(sizeof(CVal *) * 2); a.el[0] = box(cv_undef(NULL)); a.i = -1;
  } else {
    layout(t->ct); a.n = t->ct->fields.n; a.el = xalloc(sizeof(CVal *) * (a.n + 1));
    for (int i = 0; i < a.n; i++) a.el[i] = box(cv_undef(field_at(t, i)->t));
  }
  return a;
}
static int is_struct_like(Type *t) { return t && (t->k == TY_STRUCT || t->k == TY_TUPLE); }
int is_tuple_type(Type *t) { return is_struct_like(t) && t->ct && t->ct->is_tuple; }
int is_anon(Type *t) { return is_struct_like(t) && t->ct && t->ct->name && (!strcmp(t->ct->name, "anon_struct") || !strcmp(t->ct->name, "tuple")); }

Type *mk_anon_struct_new(Vec *names, Vec *types, int tuple);
#define ANON_HB 4096
typedef struct AnonE { struct AnonE *next; unsigned h; Type *t; } AnonE;
static AnonE *anon_tab[ANON_HB];
Type *mk_anon_struct(Vec *names, Vec *types, int tuple) {
  unsigned h = tuple * 31u + types->n;
  for (int i = 0; i < types->n; i++) { h = h * 1000003u ^ (unsigned)(uintptr_t)types->a[i]; for (const char *q = names->a[i]; q && *q; q++) h = h * 33u + (unsigned char)*q; }
  for (AnonE *e = anon_tab[h % ANON_HB]; e; e = e->next) {
    if (e->h != h) continue; Container *ec = e->t->ct;
    if (ec->is_tuple != tuple || ec->fields.n != types->n) continue;
    int ok = 1; for (int i = 0; ok && i < types->n; i++) { Field *f = ec->fields.a[i]; if (f->t != types->a[i] || strcmp(f->name, names->a[i])) ok = 0; }
    if (ok) return e->t;
  }
  Type *nt = mk_anon_struct_new(names, types, tuple);
  AnonE *e = xalloc(sizeof *e); e->h = h; e->t = nt; e->next = anon_tab[h % ANON_HB]; anon_tab[h % ANON_HB] = e; return nt;
}
static int ctf_eq(CVal *a, CVal *b) {
  if (!a || !b) return a == b;
  if (a->k != b->k) return 0;
  if (a->k == CV_ENUMLIT) return !strcmp(a->s, b->s);
  if (a->k == CV_TYPE) return a->t == b->t;
  return 0;
}
#define ANON_CT_HB 1024
static AnonE *anon_ct_tab[ANON_CT_HB];
Type *mk_anon_struct_cv(Vec *names, Vec *types, int tuple, CVal **cts) {
  unsigned h = tuple * 31u + types->n;
  for (int i = 0; i < types->n; i++) { h = h * 1000003u ^ (unsigned)(uintptr_t)types->a[i]; for (const char *q = names->a[i]; q && *q; q++) h = h * 33u + (unsigned char)*q;
    if (cts[i] && cts[i]->k == CV_ENUMLIT) for (const char *q = cts[i]->s; *q; q++) h = h * 37u + (unsigned char)*q;
    if (cts[i] && cts[i]->k == CV_TYPE) h = h * 41u ^ (unsigned)(uintptr_t)cts[i]->t; }
  for (AnonE *e = anon_ct_tab[h % ANON_CT_HB]; e; e = e->next) {
    if (e->h != h) continue; Container *ec = e->t->ct;
    if (ec->is_tuple != tuple || ec->fields.n != types->n) continue;
    int ok = 1; for (int i = 0; ok && i < types->n; i++) { Field *f = ec->fields.a[i]; if (f->t != types->a[i] || strcmp(f->name, names->a[i]) || !f->is_ct != !cts[i] || (cts[i] && !ctf_eq(f->defcv, cts[i]))) ok = 0; }
    if (ok) return e->t;
  }
  Type *nt = mk_anon_struct_new(names, types, tuple);
  for (int i = 0; i < types->n; i++) if (cts[i]) { Field *f = nt->ct->fields.a[i]; f->is_ct = 1; CVal *b = xalloc(sizeof *b); *b = *cts[i]; f->defcv = b; }
  AnonE *e = xalloc(sizeof *e); e->h = h; e->t = nt; e->next = anon_ct_tab[h % ANON_CT_HB]; anon_ct_tab[h % ANON_CT_HB] = e; return nt;
}
Type *mk_anon_struct_new(Vec *names, Vec *types, int tuple) {
  Container *c = xalloc(sizeof *c); c->name = tuple ? "tuple" : "anon_struct"; c->is_tuple = tuple;
  Type *t = xalloc(sizeof *t); t->k = TY_STRUCT; t->ct = c; c->type = t; t->size = -1;
  int off = 0, al = 1;
  for (int i = 0; i < types->n; i++) {
    Field *f = xalloc(sizeof *f); f->name = names->a[i]; f->t = types->a[i];
    int a = talign(f->t); if (a < 1) a = 1; if (a > al) al = a; off = (off + a - 1) / a * a; f->off = off; off += tsize(f->t);
    vpush(&c->fields, f);
  }
  t->align = al; t->size = (off + al - 1) / al * al; c->laid = 1; return t;
}

/* ---------- memory access ---------- */
int cv_len(CVal *v, int64_t *len) {
  switch (v->k) {
  case CV_STR: *len = v->slen; return 1;
  case CV_AGG: if (v->t->k == TY_ARRAY || is_struct_like(v->t)) { *len = v->n; return 1; } return 0;
  case CV_SLICE: *len = v->slen; return 1;
  case CV_PTR: if (v->idx < 0 && v->base) return cv_len(v->base, len);
    if (v->t && v->t->k == TY_PTR && v->t->elem->k == TY_ARRAY) { *len = v->t->elem->len; return 1; } return 0;
  case CV_UNDEF: if (v->t && v->t->k == TY_ARRAY) { *len = v->t->len; return 1; } return 0;
  default: return 0;
  }
}
static CVal *elem_cell(CVal *v, int64_t i);
CVal cv_elem(CVal *v, int64_t i) {
  if (v->k == CV_STR) { if (i < 0 || i > v->slen) die("comptime index %lld out of bounds", (long long)i); return cv_int(i == v->slen ? 0 : (unsigned char)v->s[i], t_u8); }
  if (v->k == CV_SLICE && v->base && v->base->k == CV_STR) return cv_int((unsigned char)v->base->s[v->idx + i], t_u8);
  if (v->k == CV_PTR && v->base && v->base->k == CV_STR) return cv_int((unsigned char)v->base->s[(v->idx < 0 ? 0 : v->idx) + i], t_u8);
  if (v->k == CV_UNDEF) return cv_undef(v->t && v->t->k == TY_ARRAY ? v->t->elem : NULL);
  CVal *c = elem_cell(v, i); if (!c) die("bad comptime element access");
  return *c;
}
static CVal *elem_cell(CVal *v, int64_t i) {
  if (v->k == CV_UNDEF && v->t && v->t->k == TY_ARRAY) *v = agg_new(v->t);
  switch (v->k) {
  case CV_AGG: if (i < 0 || i >= v->n) { if (v->t && v->t->k == TY_ARRAY && v->t->hassent && i == v->n) return box(cv_int(v->t->sent, v->t->elem)); die("%s:%d: comptime index %lld out of bounds (len %d)", ev_cur ? ev_cur->tok->file : "?", ev_cur ? ev_cur->tok->line : 0, (long long)i, v->n); } return v->el[i];
  case CV_SLICE: return v->base ? elem_cell(v->base, v->idx + i) : NULL;
  case CV_PTR:
    if (!v->base) return NULL;
    if (v->idx < 0) return elem_cell(v->base, i);
    return elem_cell(v->base, v->idx + i);
  default: return NULL;
  }
}
static CVal agg_new(Type *t);
CVal *deref_cell(CVal *p) {
  if (p->k != CV_PTR || !p->base) return NULL;
  if (p->idx < 0) return p->base;
  if (p->t && p->t->k == TY_PTR && p->t->elem->k == TY_ARRAY && !is_vec(p->t->elem) &&
      (p->base->k == CV_STR || (p->base->k == CV_AGG && cv_typeof(p->base)->k == TY_ARRAY && cv_typeof(p->base)->elem != p->t->elem))) {
    /* pointer to a sub-array view */
    Type *at = p->t->elem;
    if (p->base->k == CV_AGG && p->idx == 0 && at->len == p->base->n) return p->base;
    CVal r = agg_new(at);
    for (int64_t i = 0; i < at->len; i++) {
      if (p->base->k == CV_STR) *r.el[i] = cv_int(p->idx + i < p->base->slen ? (unsigned char)p->base->s[p->idx + i] : 0, t_u8);
      else if (p->idx + i < p->base->n) *r.el[i] = cv_copy(*p->base->el[p->idx + i]);
    }
    return box(r);
  }
  if (p->base->k == CV_STR) return box(cv_int((unsigned char)p->base->s[p->idx], t_u8));
  return elem_cell(p->base, p->idx);
}
/* assignment into a cell, keeping cells (and pointers to elements) alive */
static void assign(CVal *cell, CVal v) {
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
  case CV_INT: case CV_BOOL: case CV_ERR: return a->i == b->i && (a->k != CV_INT || cv_typeof(a) == cv_typeof(b) || cv_typeof(a)->k == TY_CINT || cv_typeof(b)->k == TY_CINT);
  case CV_FN: return a->fn == b->fn;
  case CV_FLOAT: return a->t == b->t && (a->f == b->f || (a->f != a->f && b->f != b->f));
  case CV_ENUMLIT: return !strcmp(a->s, b->s);
  case CV_STR: return a->slen == b->slen && !memcmp(a->s, b->s, a->slen);
  case CV_AGG:
    if (a->t != b->t || a->n != b->n || a->i != b->i) return 0;
    for (int i = 0; i < a->n; i++) if (!cval_eq(a->el[i], b->el[i])) return 0;
    return 1;
  case CV_PTR: return a->base == b->base && a->idx == b->idx && a->t == b->t && a->i == b->i && (a->s == b->s || (a->s && b->s && !strcmp(a->s, b->s)));
  case CV_SLICE: return a->base == b->base && a->idx == b->idx && a->slen == b->slen;
  case CV_NULL: case CV_VOID: case CV_UNDEF: return 1;
  default: return 1;
  }
}

/* ---------- coercion ---------- */
static CVal mk_splat(CVal v) {
  if (!t_splat) { t_splat = xalloc(sizeof *t_splat); t_splat->k = TY_VOID; t_splat->name = "@splat"; t_splat->size = 0; t_splat->align = 1; }
  CVal a = {0}; a.k = CV_AGG; a.t = t_splat; a.n = 1; a.el = xalloc(sizeof(CVal *)); a.el[0] = box(v); return a;
}
static CVal default_of(Type *t, Field *f);
CVal ccoerce(CVal v, Type *t) {
  if (!t || t->k == TY_ANYTYPE) return v;
  if (t_splat && v.k == CV_AGG && v.t == t_splat && t->k == TY_ARRAY) {
    CVal a = agg_new(t); for (int i = 0; i < a.n; i++) *a.el[i] = ccoerce(*v.el[0], t->elem); return a;
  }
  switch (v.k) {
  case CV_UNDEF: if (t->k != TY_UNDEF) v.t = t; return v;
  case CV_INT:
    if (t->k == TY_INT || t->k == TY_CINT) { v.t = t; v.i = wrap_int(v.i, t); if (t->k == TY_INT) v.big = 0; return v; }
    if (is_float(t)) return cv_float(fround((f128)v.i, t), t);
    if (t->k == TY_ENUM) { v.t = t; return v; }
    if (t->k == TY_OPT || t->k == TY_ERRU) return ccoerce(v, t->elem);
    if (t->k == TY_PTR || t->k == TY_MPTR || t->k == TY_FN) { v.t = t; return v; }
    if (t->k == TY_BOOL) return v;
    if (is_vec(t)) { CVal a = agg_new(t); for (int i = 0; i < a.n; i++) *a.el[i] = ccoerce(v, t->elem); return a; }
    return v;
  case CV_ENUMLIT:
    if (t->k == TY_OPT || t->k == TY_ERRU) return ccoerce(v, t->elem);
    if (t->k == TY_ENUM) {
      int64_t x; if (enum_val(t, v.s, &x)) return cv_int(x, t);
      Decl *d = find_decl(t->ct, v.s);
      if (d) { resolve_decl(d); if (d->kind == D_CONST) return ccoerce(d->cv, t); }
      die("no enum field .%s in %s", v.s, tname(t));
    }
    if (t->k == TY_UNION && t->ct && find_field(t->ct, v.s)) {
      CVal a = agg_new(t); a.i = field_index(t, v.s); *a.el[0] = cv_void(); return a;
    }
    if (t->ct && (t->k == TY_STRUCT || t->k == TY_UNION || t->k == TY_OPAQUE)) {
      Decl *d = find_decl(t->ct, v.s);
      if (d) { resolve_decl(d); if (d->kind == D_CONST) return ccoerce(d->cv, t); }
    }
    return v;
  case CV_FLOAT:
    if (is_float(t)) return cv_float(fround(v.f, t), t);
    if (t->k == TY_INT || t->k == TY_CINT) return cv_int(wrap_int((i128)v.f, t), t);
    if (t->k == TY_OPT || t->k == TY_ERRU) return ccoerce(v, t->elem);
    if (is_vec(t)) { CVal a = agg_new(t); for (int i = 0; i < a.n; i++) *a.el[i] = ccoerce(v, t->elem); return a; }
    return v;
  case CV_NULL: if (t->k == TY_OPT) { if (v.t && v.t->k == TY_OPT && t->elem == v.t) v.slen++; v.t = t; } return v;
  case CV_ERR: if (t->k == TY_ERRSET || t->k == TY_ERRU) v.t = t; return v;
  case CV_STR:
    if (t->k == TY_OPT || t->k == TY_ERRU) return ccoerce(v, t->elem);
    if (t->k == TY_ARRAY) {
      CVal a = agg_new(t);
      for (int i = 0; i < a.n && i < v.slen; i++) *a.el[i] = cv_int((unsigned char)v.s[i], t->elem);
      return a;
    }
    if (t->k == TY_SLICE || t->k == TY_MPTR || t->k == TY_PTR) { v.t = t; return v; }
    return v;
  case CV_AGG: {
    Type *f = v.t;
    if (f == t) return v;
    if (t->k == TY_OPT || t->k == TY_ERRU) return ccoerce(v, t->elem);
    if (f->k == TY_ARRAY && t->k == TY_SLICE && f->elem == t->elem) { CVal r = {0}; r.k = CV_SLICE; r.base = box(cv_copy(v)); r.idx = 0; r.slen = v.n; r.t = t; return r; }
    if (f->k == TY_ARRAY && t->k == TY_ARRAY && f->len == t->len) {
      CVal a = v; a.t = t; a.el = xalloc(sizeof(CVal *) * (v.n + 1));
      for (int i = 0; i < v.n; i++) a.el[i] = box(ccoerce(*v.el[i], t->elem));
      return a;
    }
    if (is_struct_like(f) && t->k == TY_ARRAY && (is_anon(f) || is_tuple_type(f))) {
      CVal a = agg_new(t); for (int i = 0; i < a.n && i < v.n; i++) *a.el[i] = ccoerce(*v.el[i], t->elem); return a;
    }
    if (is_struct_like(f) && is_struct_like(t) && (is_anon(f) || (is_tuple_type(f) && is_tuple_type(t)))) {
      CVal a = agg_new(t); int tup = is_tuple_type(f);
      char *set = xalloc(a.n + 1);
      for (int i = 0; i < v.n; i++) {
        int fi = tup ? i : field_index(t, field_at(f, i)->name);
        if (fi < 0 || fi >= a.n) continue;
        *a.el[fi] = ccoerce(*v.el[i], field_at(t, fi)->t); set[fi] = 1;
      }
      for (int i = 0; i < a.n; i++) if (!set[i]) *a.el[i] = default_of(t, field_at(t, i));
      return a;
    }
    if (is_struct_like(f) && t->k == TY_UNION && is_anon(f) && v.n == 1) {
      CVal a = agg_new(t); a.i = field_index(t, field_at(f, 0)->name); if (a.i < 0) return v;
      *a.el[0] = ccoerce(*v.el[0], field_at(t, (int)a.i)->t); return a;
    }
    if (f->k == TY_UNION && t->k == TY_ENUM && v.i >= 0) {
      int64_t x; enum_val(t, field_at(f, (int)v.i)->name, &x); return cv_int(x, t);
    }
    return v;
  }
  case CV_PTR: {
    Type *f = v.t;
    if (t->k == TY_OPT && t->elem->k != TY_OPT) { CVal r = ccoerce(v, t->elem); return r; }
    if (t->k == TY_ERRU) return ccoerce(v, t->elem);
    if (t->k == TY_SLICE && v.base && f && f->k == TY_PTR && f->elem->k == TY_ARRAY && v.idx >= 0 &&
        (v.base->k == CV_STR || (v.base->k == CV_AGG && cv_typeof(v.base)->k == TY_ARRAY && cv_typeof(v.base)->elem != f->elem))) {
      int64_t len = f->elem->len; /* pointer to a sub-array view of base */
      if (v.base->k == CV_STR) { CVal r = cv_str(v.base->s + v.idx, (int)len); r.t = t; return r; }
      CVal r = {0}; r.k = CV_SLICE; r.base = v.base; r.idx = v.idx; r.slen = (int)len; r.t = t; return r;
    }
    if (t->k == TY_SLICE && v.base && f && f->k == TY_PTR && f->elem->k == TY_ARRAY) {
      CVal *arr = deref_cell(&v); int64_t len = f->elem->len;
      if (arr && arr->k == CV_STR) { CVal r = *arr; r.t = t; return r; }
      CVal r = {0}; r.k = CV_SLICE; r.base = arr; r.idx = 0; r.slen = (int)len; r.t = t; return r;
    }
    if ((t->k == TY_SLICE || t->k == TY_MPTR) && v.base && f && f->k == TY_PTR && is_struct_like(f->elem) && f->elem->ct && f->elem->ct->is_tuple) {
      CVal *tu = deref_cell(&v);
      if (tu && (tu->k == CV_AGG || tu->k == CV_UNDEF)) {
        int nn = tu->k == CV_AGG ? tu->n : 0;
        CVal arr = agg_new(array_of(t->elem, nn, 0, 0));
        for (int i = 0; i < nn; i++) *arr.el[i] = ccoerce(cv_copy(*tu->el[i]), t->elem);
        CVal r = {0}; r.k = t->k == TY_SLICE ? CV_SLICE : CV_PTR; r.base = box(arr); r.idx = 0; r.slen = nn; r.t = t; return r;
      }
    }
    if (t->k == TY_MPTR && v.base && f && f->k == TY_PTR && f->elem->k == TY_ARRAY && v.idx < 0) { CVal r = v; r.idx = 0; r.t = t; return r; }
    if (t->k == TY_PTR || t->k == TY_MPTR || t->k == TY_FN) v.t = t;
    return v;
  }
  case CV_SLICE:
    if (t->k == TY_OPT || t->k == TY_ERRU) return ccoerce(v, t->elem);
    if (t->k == TY_SLICE) { v.t = t; return v; }
    if (t->k == TY_MPTR) { CVal r = {0}; r.k = CV_PTR; r.base = v.base; r.idx = v.idx; r.t = t; return r; }
    if (t->k == TY_ARRAY) { CVal a = agg_new(t); for (int i = 0; i < a.n && i < v.slen; i++) *a.el[i] = ccoerce(cv_elem(&v, i), t->elem); return a; }
    return v;
  case CV_FN:
    if (t->k == TY_FN || t->k == TY_PTR) { v.t = t; return v; }
    if (t->k == TY_OPT) return ccoerce(v, t->elem);
    return v;
  case CV_VOID: return v;
  default: return v;
  }
}
static CVal default_of(Type *t, Field *f) {
  if (f->defcv) return *(CVal *)f->defcv;
  if (f->def) {
    CVal d; ct_force++; int sxs = xs; int r = ev_rt(f->def, t->ct->scope, f->t, &d); ct_force--; xs = sxs;
    if (r == R_OK) return ccoerce(d, f->t);
  }
  return cv_undef(f->t);
}

/* ---------- member access ---------- */
int ceval_member(CVal base, const char *name, CVal *out) {
  if (base.k == CV_TYPE) {
    Type *t = base.t;
    if (t->ct) {
      Decl *d = find_decl(t->ct, name);
      if (d) { resolve_decl(d); if (d->kind == D_CONST || d->kind == D_FN) { *out = d->cv; return 1; } return 0; }
      if (t->k == TY_ENUM) { int64_t v; if (enum_val(t, name, &v)) { *out = cv_int(v, t); return 1; } }
      if (t->k == TY_UNION && t->ct->tagged) { int64_t v; layout(t->ct); if (enum_val(t, name, &v)) { *out = cv_int(v, t->ct->tag); return 1; } }
    }
    if (t->k == TY_ERRSET) { CVal v = {0}; v.k = CV_ERR; v.i = err_id(name); v.t = t_errset; *out = v; return 1; }
    return 0;
  }
  if (base.k == CV_STR) {
    if (!strcmp(name, "len")) { *out = cv_int(base.slen, t_usize); return 1; }
    if (!strcmp(name, "ptr")) { CVal p = {0}; p.k = CV_PTR; p.base = box(base); p.idx = 0; p.t = mptr_to(t_u8, 1, 1, 0); *out = p; return 1; }
    return 0;
  }
  if (base.k == CV_SLICE) {
    if (!strcmp(name, "len")) { *out = cv_int(base.slen, t_usize); return 1; }
    if (!strcmp(name, "ptr")) { CVal p = base; p.k = CV_PTR; p.t = mptr_to(base.t ? base.t->elem : t_u8, base.t ? base.t->isconst : 1, 0, 0); *out = p; return 1; }
    return 0;
  }
  if (base.k == CV_PTR) {
    if (!base.base) return 0;
    if (base.t && base.t->k == TY_PTR && base.t->elem->k == TY_ARRAY && !is_vec(base.t->elem)) {
      if (!strcmp(name, "len")) { *out = cv_int(base.t->elem->len, t_usize); return 1; }
      if (!strcmp(name, "ptr")) { CVal p = base; if (p.idx < 0) p.idx = 0; p.t = mptr_to(base.t->elem->elem, base.t->isconst, 0, 0); *out = p; return 1; }
    }
    CVal *c = deref_cell(&base);
    if (base.t && base.t->k == TY_PTR) return c ? ceval_member(*c, name, out) : 0;
    return 0;
  }
  if (base.k == CV_UNDEF && base.t && base.t->k == TY_ARRAY && !strcmp(name, "len")) { *out = cv_int(base.t->len, t_usize); return 1; }
  if (base.k == CV_AGG) {
    Type *t = base.t;
    if (t->k == TY_ARRAY) { if (!strcmp(name, "len")) { *out = cv_int(t->len, t_usize); return 1; } return 0; }
    if (t->k == TY_UNION) {
      int fi = field_index(t, name);
      if (fi >= 0) { if (fi != base.i) die("access of inactive union field '%s' at comptime", name); *out = *base.el[0]; return 1; }
    } else if (is_struct_like(t)) {
      int fi = field_index(t, name);
      if (fi >= 0) { *out = *base.el[fi]; return 1; }
      if (!strcmp(name, "len") && is_tuple_type(t)) { *out = cv_int(base.n, t_usize); return 1; }
    }
    if (t->ct) {
      Decl *d = find_decl(t->ct, name);
      if (d) { resolve_decl(d); if (d->kind == D_CONST || d->kind == D_FN) { *out = d->cv; return 1; } }
    }
    return 0;
  }
  return 0;
}

/* ---------- operators ---------- */
static int enum_of(CVal *lit, CVal *other) {
  /* resolve an enum literal against the type of the other operand */
  if (lit->k != CV_ENUMLIT) return 0;
  Type *t = cv_typeof(other);
  if (other->k == CV_INT && t && t->k == TY_ENUM) { int64_t v; if (!enum_val(t, lit->s, &v)) die("no enum field .%s in %s", lit->s, tname(t)); *lit = cv_int(v, t); return 1; }
  return 0;
}
static int union_tag_is(CVal *u, CVal *tag) {
  if (u->i < 0) return 0;
  Field *f = field_at(u->t, (int)u->i);
  if (tag->k == CV_ENUMLIT) return !strcmp(f->name, tag->s);
  if (tag->k == CV_INT) return f->val == (int64_t)tag->i;
  return 0;
}
static CVal *as_cells(CVal *v, int64_t *len, Type **et) {
  /* view of a sequence (array/tuple/slice/string/pointer-to-array) as a list of values */
  if (!cv_len(v, len)) {
    if (v->k == CV_PTR && v->t && v->t->k == TY_PTR && v->t->elem->k == TY_ARRAY) *len = v->t->elem->len; else return NULL;
  }
  CVal *r = xalloc(sizeof(CVal) * (*len + 1));
  for (int64_t i = 0; i < *len; i++) r[i] = cv_elem(v, i);
  Type *t = cv_typeof(v);
  if (et) {
    *et = NULL;
    if (v->k == CV_STR) *et = t_u8;
    else if (t->k == TY_ARRAY || t->k == TY_SLICE || t->k == TY_MPTR) *et = t->elem;
    else if (t->k == TY_PTR && t->elem->k == TY_ARRAY) *et = t->elem->elem;
  }
  return r;
}
static int seq_is_str(CVal *v) { return v->k == CV_STR || (v->k == CV_SLICE && v->base && v->base->k == CV_STR); }
static int ev_fbin(const char *op, CVal a, CVal b, CVal *out) {
  Type *ta = cv_typeof(&a), *tb = cv_typeof(&b);
  Type *t = ta->k == TY_FLOAT ? ta : tb->k == TY_FLOAT ? tb : t_cfloat;
  f128 x = a.k == CV_FLOAT ? a.f : (f128)a.i, y = b.k == CV_FLOAT ? b.f : (f128)b.i, r;
  if (!strcmp(op, "==")) { *out = cv_bool(x == y); return R_OK; }
  if (!strcmp(op, "!=")) { *out = cv_bool(x != y); return R_OK; }
  if (!strcmp(op, "<")) { *out = cv_bool(x < y); return R_OK; }
  if (!strcmp(op, ">")) { *out = cv_bool(x > y); return R_OK; }
  if (!strcmp(op, "<=")) { *out = cv_bool(x <= y); return R_OK; }
  if (!strcmp(op, ">=")) { *out = cv_bool(x >= y); return R_OK; }
  switch (op[0]) {
  case '+': r = x + y; break; case '-': r = x - y; break; case '*': r = x * y; break; case '/': r = x / y; break;
  case '%': r = (f128)fmodl((long double)x, (long double)y); break;
  default: return R_FAIL;
  }
  *out = cv_float(fround(r, t), t); return R_OK;
}
/* ---- wide comptime_int arithmetic (256-bit two's complement: hi:lo) ---- */
typedef unsigned __int128 u128;
typedef struct { i128 hi; u128 lo; } W;
static W to_w(CVal *v) {
  W w; w.lo = (u128)v->i;
  if (v->big) w.hi = v->ih;
  else { Type *t = cv_typeof(v); w.hi = (t->k == TY_INT && !t->sign && t->bits >= 128) ? 0 : (v->i < 0 ? -1 : 0); }
  return w;
}
static CVal from_w(W w) { CVal r = cv_int((i128)w.lo, t_cint); i128 sx = (i128)w.lo < 0 ? -1 : 0; if (w.hi != sx) { r.big = 1; r.ih = w.hi; } return r; }
static W w_add(W a, W b) { W r; r.lo = a.lo + b.lo; r.hi = (i128)((u128)a.hi + (u128)b.hi + (r.lo < a.lo)); return r; }
static W w_neg(W a) { W r; r.lo = ~a.lo + 1; r.hi = (i128)(~(u128)a.hi + (r.lo == 0)); return r; }
static int w_cmp(W a, W b) { if (a.hi != b.hi) return a.hi < b.hi ? -1 : 1; return a.lo < b.lo ? -1 : a.lo > b.lo; }
static W w_shl(W a, int n) { W r; if (n <= 0) return a; if (n >= 256) { r.hi = 0; r.lo = 0; return r; }
  if (n >= 128) { r.hi = (i128)(a.lo << (n - 128)); r.lo = 0; return r; }
  r.hi = (i128)(((u128)a.hi << n) | (a.lo >> (128 - n))); r.lo = a.lo << n; return r; }
static W w_sar(W a, int n) { W r; if (n <= 0) return a; if (n >= 256) { r.hi = a.hi < 0 ? -1 : 0; r.lo = (u128)r.hi; return r; }
  if (n >= 128) { r.lo = (u128)(a.hi >> (n - 128)); r.hi = a.hi < 0 ? -1 : 0; return r; }
  r.lo = (a.lo >> n) | ((u128)a.hi << (128 - n)); r.hi = a.hi >> n; return r; }
static int w_fits(W a) { return a.hi == ((i128)a.lo < 0 ? -1 : 0); }
static int ev_bin_wide(const char *op, CVal a, CVal b, CVal *out) {
  W x = to_w(&a), y = to_w(&b), r;
  if ((op[0] == '<' || op[0] == '>') && (!op[1] || (op[1] == '=' && !op[2]))) {
    int c = w_cmp(x, y); int res = !strcmp(op, "<") ? c < 0 : !strcmp(op, ">") ? c > 0 : !strcmp(op, "<=") ? c <= 0 : c >= 0;
    *out = cv_bool(res); return R_OK; }
  if (!strcmp(op, "==") || !strcmp(op, "!=")) { int eq = !w_cmp(x, y); *out = cv_bool(op[0] == '=' ? eq : !eq); return R_OK; }
  if (!strcmp(op, "+")) r = w_add(x, y);
  else if (!strcmp(op, "-")) r = w_add(x, w_neg(y));
  else if (!strcmp(op, "&")) { r.hi = x.hi & y.hi; r.lo = x.lo & y.lo; }
  else if (!strcmp(op, "|")) { r.hi = x.hi | y.hi; r.lo = x.lo | y.lo; }
  else if (!strcmp(op, "^")) { r.hi = x.hi ^ y.hi; r.lo = x.lo ^ y.lo; }
  else if (!strcmp(op, "<<")) { if (!w_fits(y) || (i128)y.lo < 0) return R_FAIL; r = w_shl(x, (int)((i128)y.lo > 300 ? 300 : (i128)y.lo)); }
  else if (!strcmp(op, ">>")) { if (!w_fits(y) || (i128)y.lo < 0) return R_FAIL; r = w_sar(x, (int)((i128)y.lo > 300 ? 300 : (i128)y.lo)); }
  else if (!strcmp(op, "*")) {
    if (!w_fits(x) || !w_fits(y)) return R_FAIL;
    i128 p; if (!__builtin_mul_overflow((i128)x.lo, (i128)y.lo, &p)) { *out = cv_int(p, t_cint); return R_OK; }
    int neg = ((i128)x.lo < 0) != ((i128)y.lo < 0); u128 ma = (i128)x.lo < 0 ? -x.lo : x.lo, mb = (i128)y.lo < 0 ? -y.lo : y.lo;
    uint64_t a0 = (uint64_t)ma, a1 = (uint64_t)(ma >> 64), b0 = (uint64_t)mb, b1 = (uint64_t)(mb >> 64);
    u128 p00 = (u128)a0 * b0, p01 = (u128)a0 * b1, p10 = (u128)a1 * b0, p11 = (u128)a1 * b1;
    u128 mid = (p00 >> 64) + (uint64_t)p01 + (uint64_t)p10;
    r.lo = (p00 & (u128)UINT64_MAX) | (mid << 64); r.hi = (i128)(p11 + (p01 >> 64) + (p10 >> 64) + (mid >> 64));
    if (neg) r = w_neg(r);
  }
  else if (!strcmp(op, "/") || !strcmp(op, "%")) {
    if (!w_fits(y) || (i128)y.lo == 0) return R_FAIL;
    if (w_fits(x)) return R_FAIL; /* handled by the narrow path */
    if (x.hi < 0 || (i128)y.lo < 0) return R_FAIL;
    /* non-negative wide / small positive: long division by bits */
    u128 d = y.lo; W q = {0, 0}; W rem = {0, 0};
    for (int i = 255; i >= 0; i--) {
      rem = w_shl(rem, 1); int bit = i >= 128 ? (int)(((u128)x.hi >> (i - 128)) & 1) : (int)((x.lo >> i) & 1); rem.lo |= (u128)bit;
      W dw = { 0, d }; if (w_cmp(rem, dw) >= 0) { rem = w_add(rem, w_neg(dw)); if (i >= 128) q.hi |= (i128)((u128)1 << (i - 128)); else q.lo |= (u128)1 << i; }
    }
    r = op[0] == '/' ? q : rem;
  }
  else return R_FAIL;
  *out = from_w(r); return R_OK;
}
static int ev_bin(const char *op, CVal a, CVal b, CVal *out) {
  if (a.k == CV_INT && b.k == CV_INT && (a.big || b.big || ((cv_typeof(&a)->k == TY_CINT && (cv_typeof(&b)->k == TY_CINT || !strcmp(op, "<<") || !strcmp(op, ">>"))) &&
      strcmp(op, "/") && strcmp(op, "%") && strcmp(op, "<<|") && strcmp(op, "+%") && strcmp(op, "-%") && strcmp(op, "*%") && strcmp(op, "+|") && strcmp(op, "-|") && strcmp(op, "*|")))) {
    if (a.big || b.big) { Type *ta = cv_typeof(&a), *tb = cv_typeof(&b);
      if ((ta->k == TY_CINT || a.big) && (tb->k == TY_CINT || b.big || !strcmp(op, "<<") || !strcmp(op, ">>"))) { int r = ev_bin_wide(op, a, b, out); if (r == R_OK) return r; }
      else if (!strcmp(op, "<") || !strcmp(op, ">") || !strcmp(op, "<=") || !strcmp(op, ">=") || !strcmp(op, "==") || !strcmp(op, "!=")) return ev_bin_wide(op, a, b, out);
    } else { int r = ev_bin_wide(op, a, b, out); if (r == R_OK) return r; }
  }
  enum_of(&a, &b); enum_of(&b, &a);
  if ((a.k == CV_FLOAT && (b.k == CV_FLOAT || b.k == CV_INT)) || (b.k == CV_FLOAT && a.k == CV_INT)) return ev_fbin(op, a, b, out);
  if (!strcmp(op, "==") || !strcmp(op, "!=")) {
    int eq;
    if (a.k == CV_UNDEF || b.k == CV_UNDEF) return R_FAIL;
    if (a.k == CV_AGG && a.t->k == TY_UNION && (b.k == CV_ENUMLIT || b.k == CV_INT)) eq = union_tag_is(&a, &b);
    else if (b.k == CV_AGG && b.t->k == TY_UNION && (a.k == CV_ENUMLIT || a.k == CV_INT)) eq = union_tag_is(&b, &a);
    else if (a.k == CV_AGG && b.k == CV_AGG && a.t->k == TY_ARRAY) { /* vectors: elementwise */
      CVal r = agg_new(vec_of(t_bool, a.n));
      for (int i = 0; i < a.n; i++) { CVal e; if (ev_bin(op, *a.el[i], *b.el[i], &e) != R_OK) return R_FAIL; *r.el[i] = e; }
      *out = r; return R_OK;
    }
    else if (a.k != b.k) { if (a.k == CV_NULL || b.k == CV_NULL) eq = 0; else return R_FAIL; }
    else if (a.k == CV_TYPE) eq = a.t == b.t;
    else if (a.k == CV_INT || a.k == CV_BOOL || a.k == CV_ERR) eq = a.i == b.i;
    else if (a.k == CV_ENUMLIT) eq = !strcmp(a.s, b.s);
    else if (a.k == CV_NULL) eq = (a.slen > 0) == (b.slen > 0) && (a.slen <= 0 || a.slen == b.slen);
    else if (a.k == CV_VOID) eq = 1;
    else if (a.k == CV_FN) eq = a.fn == b.fn;
    else if (a.k == CV_PTR) eq = a.base == b.base && a.idx == b.idx && a.i == b.i;
    else return R_FAIL;
    *out = cv_bool(op[0] == '=' ? eq : !eq); return R_OK;
  }
  if (!strcmp(op, "++") || !strcmp(op, "**")) {
    int64_t la, lb = 0; Type *ea = NULL, *eb = NULL;
    CVal *xa = as_cells(&a, &la, &ea); if (!xa) return R_FAIL;
    if (op[1] == '*') { if (b.k != CV_INT) return R_FAIL; lb = (int64_t)b.i; }
    CVal *xb = op[1] == '+' ? as_cells(&b, &lb, &eb) : NULL; if (op[1] == '+' && !xb) return R_FAIL;
    int64_t n = op[1] == '+' ? la + lb : la * lb;
    if (seq_is_str(&a) && (op[1] == '*' || seq_is_str(&b))) {
      char *r = xalloc(n + 1); int64_t k = 0;
      if (op[1] == '+') { for (int64_t i = 0; i < la; i++) r[k++] = (char)xa[i].i; for (int64_t i = 0; i < lb; i++) r[k++] = (char)xb[i].i; }
      else for (int64_t j = 0; j < lb; j++) for (int64_t i = 0; i < la; i++) r[k++] = (char)xa[i].i;
      *out = cv_str(r, (int)n); return R_OK;
    }
    Type *at = cv_typeof(&a), *bt2 = cv_typeof(&b);
    int tup = (is_struct_like(at) && !ea) || (op[1] == '+' && is_struct_like(bt2) && !eb && !ea);
    Type *et = ea ? ea : eb;
    if (tup || !et) {
      Vec names = {0}, types = {0}; CVal r = {0};
      for (int64_t i = 0; i < n; i++) {
        CVal e = op[1] == '+' ? (i < la ? xa[i] : xb[i - la]) : xa[i % la];
        vpush(&names, fmt("%d", (int)i)); vpush(&types, cv_typeof(&e));
      }
      r = agg_new(mk_anon_struct(&names, &types, 1));
      for (int64_t i = 0; i < n; i++) *r.el[i] = op[1] == '+' ? (i < la ? xa[i] : xb[i - la]) : xa[i % la];
      *out = r; return R_OK;
    }
    Type *ft = cv_typeof(&a); int hs = 0; int64_t sv = 0;
    if (ft->k == TY_PTR && ft->elem->k == TY_ARRAY) ft = ft->elem;
    if (ft->k == TY_ARRAY && ft->hassent) { hs = 1; sv = ft->sent; }
    CVal r = agg_new(array_of(et, n, hs, sv));
    for (int64_t i = 0; i < n; i++) *r.el[i] = ccoerce(op[1] == '+' ? (i < la ? xa[i] : xb[i - la]) : xa[i % la], et);
    *out = r; return R_OK;
  }
  if (a.k == CV_AGG && a.t->k == TY_ARRAY && (b.k == CV_AGG || b.k == CV_INT || b.k == CV_BOOL || b.k == CV_FLOAT)) { /* vector ops */
    CVal r = agg_new(a.t); int cmp = !strcmp(op, "<") || !strcmp(op, ">") || !strcmp(op, "<=") || !strcmp(op, ">=");
    if (cmp) r = agg_new(vec_of(t_bool, a.n));
    for (int i = 0; i < a.n; i++) { CVal e; if (ev_bin(op, *a.el[i], b.k == CV_AGG ? *b.el[i] : b, &e) != R_OK) return R_FAIL; *r.el[i] = e; }
    *out = r; return R_OK;
  }
  if (a.k == CV_BOOL && b.k == CV_BOOL) {
    if (!strcmp(op, "&")) { *out = cv_bool(a.i & b.i); return R_OK; }
    if (!strcmp(op, "|")) { *out = cv_bool(a.i | b.i); return R_OK; }
    if (!strcmp(op, "^")) { *out = cv_bool(a.i ^ b.i); return R_OK; }
    return R_FAIL;
  }
  if (a.k == CV_PTR && b.k == CV_INT && a.base && (op[0] == '+' || op[0] == '-')) {
    CVal r = a; if (r.idx < 0) r.idx = 0; r.idx += op[0] == '+' ? (int64_t)b.i : -(int64_t)b.i; *out = r; return R_OK;
  }
  if (a.k == CV_PTR && b.k == CV_PTR && op[0] == '-' && a.base == b.base) { *out = cv_int((a.idx < 0 ? 0 : a.idx) - (b.idx < 0 ? 0 : b.idx), t_usize); return R_OK; }
  if (a.k != CV_INT || b.k != CV_INT) return R_FAIL;
  int shift = !strcmp(op, "<<") || !strcmp(op, ">>") || !strcmp(op, "<<|");
  Type *t = shift ? cv_typeof(&a) : (cv_typeof(&a)->k == TY_CINT ? cv_typeof(&b) : cv_typeof(&a));
  if (t->k == TY_ENUM) t = t->ct->tag;
  int uns = t->k == TY_INT && !t->sign;
  i128 x = a.i, y = b.i, r;
  if (op[0] == '<' || op[0] == '>') if (!op[1] || (op[1] == '=' && !op[2])) {
    /* u128 values >= 2^127 are stored as negative i128 */
    Type *ta = cv_typeof(&a), *tb = cv_typeof(&b);
    int ha = ta->k == TY_INT && !ta->sign && ta->bits >= 128 && x < 0, hb = tb->k == TY_INT && !tb->sign && tb->bits >= 128 && y < 0;
    int c = (ha && hb) ? (((unsigned __int128)x > (unsigned __int128)y) - ((unsigned __int128)x < (unsigned __int128)y)) : ha ? 1 : hb ? -1 : (x > y) - (x < y);
    int res = !strcmp(op, "<") ? c < 0 : !strcmp(op, ">") ? c > 0 : !strcmp(op, "<=") ? c <= 0 : c >= 0;
    *out = cv_bool(res); return R_OK;
  }
  int sat = op[1] == '|';
  if (op[0] == '+') r = x + y;
  else if (op[0] == '-') r = x - y;
  else if (op[0] == '*' && op[1] != '*') r = x * y;
  else if (!strcmp(op, "/")) { if (!y) return R_FAIL; r = x / y; }
  else if (!strcmp(op, "%")) { if (!y) return R_FAIL; r = x % y; }
  else if (!strcmp(op, "&")) r = x & y;
  else if (!strcmp(op, "|")) r = x | y;
  else if (!strcmp(op, "^")) r = x ^ y;
  else if (op[0] == '<' && op[1] == '<') { r = y >= 127 ? 0 : x * ((i128)1 << y); if (op[2] == '|') sat = 1; }
  else if (!strcmp(op, ">>")) { if (uns && t->bits >= 128) r = y >= 128 ? 0 : (i128)((unsigned __int128)x >> y); else r = y >= 127 ? (x < 0 ? -1 : 0) : x >> y; }
  else return R_FAIL;
  if (uns && t->bits >= 128 && (op[0] == '/' || op[0] == '%') && !op[1] && (x < 0 || y < 0)) { unsigned __int128 ux = x, uy = y; r = (i128)(op[0] == '/' ? ux / uy : ux % uy); }
  if (sat && t->k == TY_INT) {
    i128 lo = t->sign ? -((i128)1 << (t->bits - 1)) : 0, hi = t->sign ? ((i128)1 << (t->bits - 1)) - 1 : (((i128)1 << t->bits) - 1);
    if (r < lo) r = lo; if (r > hi) r = hi;
  }
  (void)uns;
  *out = cv_int(wrap_int(r, t), t); return R_OK;
}

/* ---------- helpers for the evaluator ---------- */
static void step(void) { if (++ct_steps > 200000000L) die("comptime evaluation exceeded the branch quota"); }
static void bind_cap(Scope *s, char *name, CVal v) { if (name && strcmp(name, "_")) bind_cval(s, name, cv_copy(v)); }
static Type *bt_type(const char *path);
static CVal mk_union(Type *u, const char *field, CVal payload) {
  CVal a = agg_new(u); a.i = field_index(u, field); if (a.i < 0) die("no field %s in %s", field, tname(u));
  *a.el[0] = ccoerce(payload, field_at(u, (int)a.i)->t); return a;
}
static int ev_block(Node *n, Scope *s, CVal *out) {
  Scope *bs = new_scope(s, NULL); Vec dfr = {0}; int r = R_OK; CVal v = cv_void();
  for (int i = 0; i < n->list.n; i++) {
    Node *st = n->list.a[i];
    if (st->k == N_DEFER) { vpush(&dfr, st->a); continue; }
    if (st->k == N_ERRDEFER) continue;
    r = ev(st, bs, &v); if (r != R_OK) break;
  }
  for (int i = dfr.n - 1; i >= 0; i--) {
    int sxs = xs; char *sl = xlabel; CVal sv = xval; CVal dv;
    int rr = ev(dfr.a[i], bs, &dv); xs = sxs; xlabel = sl; xval = sv; if (rr == R_FAIL) r = R_FAIL;
  }
  if (r == R_CF && xs == X_BRK && n->label && xlabel && !strcmp(xlabel, n->label)) { xs = X_NONE; *out = xval; return R_OK; }
  if (r != R_OK) return r;
  *out = cv_void(); return R_OK;
}
static int ev_init(Node *n, Scope *s, Type *t, CVal *out);
static Type *rt_static_type(Scope *s, Node *n) { /* static type of a runtime local / field chain, or NULL */
  if (n->k == N_IDENT) { Sym *y; Decl *d; if (!lookup(s, n->s, &y, &d)) return NULL; if (y && y->k == S_LOCAL) return y->t; return NULL; }
  if (n->k == N_FIELD) { Type *t = rt_static_type(s, n->a); if (!t) return NULL; if (t->k == TY_PTR) t = t->elem;
    if ((t->k == TY_STRUCT || t->k == TY_TUPLE) && t->ct) { layout(t->ct); Field *f = find_field(t->ct, n->s); return f ? f->t : NULL; } }
  return NULL;
}
static int ct_field_of(Scope *s, Node *n, CVal *out) {
  Type *t = rt_static_type(s, n->a); if (!t) return 0; if (t->k == TY_PTR) t = t->elem;
  if ((t->k != TY_STRUCT && t->k != TY_TUPLE) || !t->ct) return 0;
  layout(t->ct); Field *f = find_field(t->ct, n->s); if (!f || !f->is_ct) return 0; *out = *(CVal *)f->defcv; return 1;
}
static int is_local_array(Scope *s, Node *n, Type **at) {
  Sym *y; Decl *d;
  if (n->k != N_IDENT || !lookup(s, n->s, &y, &d)) return 0;
  Type *t = NULL;
  if (y && y->k == S_LOCAL) t = y->t;
  else if (d && d->state == 2 && d->kind == D_VAR) t = d->t;
  if (!t) return 0;
  if (t->k == TY_PTR && t->elem->k == TY_ARRAY) t = t->elem;
  if (t->k != TY_ARRAY) return 0;
  *at = t; return 1;
}
static int fn_ret_type(Decl *fd, Scope *fs, Type **rt) {
  Node *f = fd->node; CVal tv; ct_force++; int r = ev(f->a, fs, &tv); ct_force--;
  if (r != R_OK || tv.k != CV_TYPE) return 0;
  *rt = tv.t; if (f->flags & F_INFERR) *rt = erru_of(*rt);
  return 1;
}
int fn_returns_ctonly(Decl *fd) {
  Node *f = fd->node; if (!f->a) return 0;
  { Node *r = f->a; while ((r->k == N_TOPT || r->k == N_TERRU) && (r->k == N_TOPT ? r->a : r->b)) r = r->k == N_TOPT ? r->a : r->b;
    if (r->k == N_IDENT && (!strcmp(r->s, "type") || !strcmp(r->s, "comptime_int") || !strcmp(r->s, "comptime_float"))) return 1; }
  if (fn_is_generic(f)) return 0;
  CVal tv; int sf = ct_force; ct_force = 0; int sxs = xs; int r = ev(f->a, fd->ct->scope, &tv); ct_force = sf; xs = sxs;
  return r == R_OK && tv.k == CV_TYPE && type_is_ctonly(tv.t);
}
int fn_takes_ctonly(Decl *fd) {
  Node *f = fd->node;
  for (int i = 0; i < f->list.n; i++) { Node *p = f->list.a[i]; if (!p->a || (p->flags & (F_ANYTYPE|F_VARARGS))) break;
    if (p->a->k == N_IDENT && !strcmp(p->a->s, "type")) break;
    CVal tv; int sf = ct_force; ct_force = 0; int sxs = xs; int r = ev(p->a, fd->ct->scope, &tv); ct_force = sf; xs = sxs;
    if (r == R_OK && tv.k == CV_TYPE && type_is_ctonly(tv.t)) return 1;
    if (p->flags & F_COMPTIME) break; }
  return 0;
}
static int self_arg(Node *recv, Scope *s, Scope *ps, CVal base, Node *param, CVal *out) {
  /* method call receiver: pass by pointer or by value according to the parameter type */
  Type *pt = NULL;
  if (param && param->a && !(param->flags & F_ANYTYPE)) { CVal tv; ct_force++; int r = ev(param->a, ps, &tv); ct_force--; if (r == R_OK && tv.k == CV_TYPE) pt = tv.t; }
  int want_ptr = pt && pt->k == TY_PTR && !(base.k == CV_PTR);
  if (want_ptr) {
    CVal *cell; int r = clval(recv, s, &cell);
    if (r == R_OK) { CVal p = {0}; p.k = CV_PTR; p.base = cell; p.idx = -1; p.t = pt; *out = p; return R_OK; }
    CVal p = {0}; p.k = CV_PTR; p.base = box(cv_copy(base)); p.idx = -1; p.t = pt; *out = p; return R_OK;
  }
  if (base.k == CV_PTR && pt && pt->k != TY_PTR && base.t && base.t->k == TY_PTR) { CVal *c = deref_cell(&base); if (!c) return R_FAIL; *out = *c; return R_OK; }
  *out = base; return R_OK;
}
static int ev_call_fn(Node *n, Scope *s, CVal fnv, int has_self, CVal self, Node *recv, CVal *out) {
  if (fnv.k != CV_FN) return R_FAIL;
  Decl *fd = fnv.fn; Node *f = fd->node;
  if (!ct_force && !fn_returns_ctonly(fd) && !fn_takes_ctonly(fd)) {
    int allct = (f->flags & F_INLINE) && f->list.n > 0;
    for (int i = 0; allct && i < f->list.n; i++) if (!(((Node *)f->list.a[i])->flags & F_COMPTIME)) allct = 0;
    if (!allct || !f->a || f->a->k != N_IDENT || (strcmp(f->a->s, "bool") && strcmp(f->a->s, "type"))) return R_FAIL;
    ct_force++; int r = ev_call_fn(n, s, fnv, has_self, self, recv, out); ct_force--; return r;
  }
  int np = f->list.n, na = n->list.n + has_self;
  CVal *args = xalloc(sizeof(CVal) * (na + 1));
  Scope *ps = new_scope(fd->ct->scope, NULL); /* to evaluate parameter types for result-typed args */
  for (int i = 0; i < na; i++) {
    Node *p = i < np ? f->list.a[i] : NULL;
    if (i == 0 && has_self) { int r = (recv ? self_arg(recv, s, ps, self, p, &args[0]) : (args[0] = self, R_OK)); if (r != R_OK) return r; if (p && p->s) bind_cval(ps, p->s, args[0]); continue; }
    Node *an = n->list.a[i - has_self]; Type *pt = NULL;
    if (p && p->a && !(p->flags & (F_ANYTYPE | F_VARARGS))) { CVal tv; ct_force++; int r = ev(p->a, ps, &tv); ct_force--; if (r == R_OK && tv.k == CV_TYPE) pt = tv.t; }
    EVR(an, s, pt, &args[i]);
    if (p && p->s) bind_cval(ps, p->s, pt ? ccoerce(args[i], pt) : args[i]);
  }
  return ct_call(fd, args, na, out);
}
static int ev_call(Node *n, Scope *s, CVal *out) {
  Node *cal = n->a; CVal fnv; int has_self = 0; CVal self = {0};
  if (cal->k == N_ENUMLIT) return R_FAIL; /* decl literal call needs a result type (ev_rt) */
  if (cal->k == N_FIELD) {
    CVal base; int r = ev(cal->a, s, &base);
    if (r == R_CF) return r;
    if (r != R_OK) return R_FAIL;
    if (base.k == CV_TYPE) { if (!ceval_member(base, cal->s, &fnv)) return R_FAIL; }
    else {
      Type *bt = cv_typeof(&base); if (bt->k == TY_PTR) bt = bt->elem;
      Decl *d = bt->ct ? find_decl(bt->ct, cal->s) : NULL;
      if (d) { resolve_decl(d); if (d->cv.k != CV_FN) return R_FAIL; fnv = d->cv; has_self = 1; self = base; }
      else if (!ceval_member(base, cal->s, &fnv)) return R_FAIL;
    }
  } else EV(cal, s, &fnv);
  return ev_call_fn(n, s, fnv, has_self, self, cal->k == N_FIELD ? cal->a : NULL, out);
}
static int ev_while(Node *n, Scope *s, CVal *out) {
  if (!ct_force) return R_FAIL;
  for (;;) {
    step(); Scope *bs = new_scope(s, NULL); CVal c;
    EV(n->a, s, &c);
    int go;
    if (n->cap) {
      if (ISNULL(c)) go = 0; else if (c.k == CV_NULL) c = unwrap_some_null(c);
      else if (c.k == CV_ERR) { go = 0; if (n->c && n->cap2) { Scope *es = new_scope(s, NULL); bind_cap(es, n->cap2, c); CVal ev2; int r = ev(n->c, es, &ev2); if (r == R_OK) *out = ev2; return r; } }
      else if (c.k == CV_UNDEF) return R_FAIL;
      else { go = 1; if (n->capref) { CVal p = {0}; p.k = CV_PTR; p.base = box(c); p.idx = -1; p.t = ptr_to(cv_typeof(&c), 0); bind_cap(bs, n->cap, p); } else bind_cap(bs, n->cap, c); }
    } else { if (c.k != CV_BOOL) return R_FAIL; go = (int)c.i; }
    if (!go) break;
    CVal bv; int r = ev(n->b, bs, &bv);
    if (r == R_CF) {
      if (xs == X_BRK && (!xlabel || (n->label && !strcmp(xlabel, n->label)))) { xs = X_NONE; *out = xval; return R_OK; }
      if (xs == X_CONT && (!xlabel || (n->label && !strcmp(xlabel, n->label)))) xs = X_NONE;
      else return r;
    } else if (r != R_OK) return r;
    if (n->d) { CVal dv; EV(n->d, bs, &dv); }
  }
  if (n->c) return ev(n->c, s, out);
  *out = cv_void(); return R_OK;
}
static int ev_for(Node *n, Scope *s, CVal *out) {
  if (!ct_force) return R_FAIL;
  int ni = n->list.n; CVal *objs = xalloc(sizeof(CVal) * ni); CVal **cells = xalloc(sizeof(CVal *) * ni);
  int64_t *starts = xalloc(sizeof(int64_t) * ni); char *isr = xalloc(ni); int64_t len = -1;
  for (int i = 0; i < ni; i++) {
    Node *e = n->list.a[i];
    if (e->k == N_RANGE) {
      CVal lo; EV(e->a, s, &lo); if (lo.k != CV_INT) return R_FAIL; isr[i] = 1; starts[i] = (int64_t)lo.i;
      if (e->b) { CVal hi; EV(e->b, s, &hi); if (hi.k != CV_INT) return R_FAIL; len = (int64_t)(hi.i - lo.i); }
      continue;
    }
    Node *cp = i < n->list2.n ? n->list2.a[i] : NULL;
    if (cp && (cp->flags & F_REF)) {
      CVal *cell; int r = clval(e, s, &cell);
      if (r != R_OK) { CVal v; EV(e, s, &v); if (v.k != CV_PTR && v.k != CV_SLICE) return R_FAIL; objs[i] = v; }
      else { cells[i] = cell; objs[i] = *cell; if (cell->k == CV_PTR) { cells[i] = NULL; } }
    } else EV(e, s, &objs[i]);
    int64_t l;
    if (!cv_len(&objs[i], &l)) {
      Type *t = cv_typeof(&objs[i]);
      if (objs[i].k == CV_PTR && t->k == TY_PTR && t->elem->k == TY_ARRAY) l = t->elem->len; else return R_FAIL;
    }
    if (len < 0) len = l;
  }
  if (len < 0) return R_FAIL;
  for (int64_t k = 0; k < len; k++) {
    step(); Scope *bs = new_scope(s, NULL);
    for (int i = 0; i < ni && i < n->list2.n; i++) {
      Node *cp = n->list2.a[i];
      if (isr[i]) { bind_cap(bs, cp->s, cv_int(starts[i] + k, t_usize)); continue; }
      if (cp->flags & F_REF) {
        CVal p = {0}; p.k = CV_PTR; Type *ot = cv_typeof(&objs[i]); Type *et = ot->k == TY_ARRAY ? ot->elem : (ot->k == TY_PTR && ot->elem->k == TY_ARRAY) ? ot->elem->elem : ot->elem;
        if (cells[i]) { p.base = cells[i]; p.idx = k; }
        else if (objs[i].k == CV_PTR) { CVal *c = elem_cell(&objs[i], k); p.base = c; p.idx = -1; }
        else if (objs[i].k == CV_SLICE) { p.base = objs[i].base; p.idx = objs[i].idx + k; }
        p.t = ptr_to(et ? et : t_u8, 0);
        bind_cap(bs, cp->s, p);
      } else bind_cap(bs, cp->s, cv_elem(&objs[i], k));
    }
    CVal bv; int r = ev(n->b, bs, &bv);
    if (r == R_CF) {
      if (xs == X_BRK && (!xlabel || (n->label && !strcmp(xlabel, n->label)))) { xs = X_NONE; *out = xval; return R_OK; }
      if (xs == X_CONT && (!xlabel || (n->label && !strcmp(xlabel, n->label)))) { xs = X_NONE; continue; }
      return r;
    } else if (r != R_OK) return r;
  }
  if (n->c) return ev(n->c, s, out);
  *out = cv_void(); return R_OK;
}
static int item_matches(Node *it, Scope *s, CVal *v, int *m) {
  if (it->k == N_RANGE) {
    CVal lo, hi; EV(it->a, s, &lo); EV(it->b, s, &hi);
    if (v->k != CV_INT || lo.k != CV_INT || hi.k != CV_INT) return R_FAIL;
    *m = v->i >= lo.i && v->i <= hi.i; return R_OK;
  }
  CVal iv; int r = ev_rt(it, s, v->k == CV_INT ? cv_typeof(v) : NULL, &iv); if (r != R_OK) return r;
  if (v->k == CV_AGG && v->t->k == TY_UNION) { *m = union_tag_is(v, &iv); return R_OK; }
  CVal e; if (ev_bin("==", *v, iv, &e) != R_OK) return R_FAIL;
  *m = (int)e.i; return R_OK;
}
static int ev_switch(Node *n, Scope *s, Type *rt, CVal *out) {
  CVal v; EV(n->a, s, &v);
  if (v.k == CV_UNDEF) return R_FAIL;
  for (;;) {
    step(); Node *hit = NULL, *els = NULL;
    for (int i = 0; i < n->list.n && !hit; i++) {
      Node *pr = n->list.a[i]; if (pr->flags & F_ELSE) { els = pr; continue; }
      for (int j = 0; j < pr->list.n; j++) { int m; int r = item_matches(pr->list.a[j], s, &v, &m); if (r != R_OK) return r; if (m) { hit = pr; break; } }
    }
    if (!hit) hit = els;
    if (!hit) return R_FAIL;
    Scope *ps = new_scope(s, NULL);
    if (hit->cap) {
      CVal pv = v;
      if (v.k == CV_AGG && v.t->k == TY_UNION) pv = *v.el[0];
      if (hit->capref) {
        CVal p = {0}; p.k = CV_PTR; p.base = (v.k == CV_AGG && v.t->k == TY_UNION) ? v.el[0] : box(v); p.idx = -1; p.t = ptr_to(cv_typeof(&pv), 0); bind_cap(ps, hit->cap, p);
      } else bind_cap(ps, hit->cap, pv);
    }
    if (hit->cap2) {
      if (v.k == CV_AGG && v.t->k == TY_UNION) { Field *f = field_at(v.t, (int)v.i); bind_cap(ps, hit->cap2, cv_int(f->val, v.t->ct->tag)); }
      else bind_cap(ps, hit->cap2, v);
    }
    int r = ev_rt(hit->b, ps, rt, out);
    if (r == R_CF && n->label && xlabel && !strcmp(xlabel, n->label)) {
      if (xs == X_BRK) { xs = X_NONE; *out = xval; return R_OK; }
      if (xs == X_CONT) { xs = X_NONE; v = ccoerce(xval, cv_typeof(&v)); continue; }
    }
    return r;
  }
}
static int global_addr(Node *n, Scope *s, char **sym, int64_t *off, Type **t);
static int ev_slice(Node *n, Scope *s, CVal *out) {
  CVal base, lo, hi; int has_hi = n->c != NULL;
  CVal *cell = NULL; int r = R_FAIL;
  { char *gs; int64_t go; Type *gt; /* slice of a runtime global array with comptime bounds: pointer into the global */
    if ((n->a->k == N_IDENT || n->a->k == N_FIELD || n->a->k == N_INDEX) && global_addr(n->a, s, &gs, &go, &gt) && gt->k == TY_ARRAY) {
      EV(n->b, s, &lo); if (lo.k != CV_INT) return R_FAIL;
      int64_t h = gt->len; if (has_hi) { EV(n->c, s, &hi); if (hi.k != CV_INT) return R_FAIL; h = (int64_t)hi.i; }
      CVal p = {0}; p.k = CV_PTR; p.s = gs; p.i = go + (int64_t)lo.i * tsize(gt->elem); p.t = ptr_to(array_of(gt->elem, h - (int64_t)lo.i, 0, 0), 0); *out = p; return R_OK;
    } }
  if (n->a->k == N_IDENT || n->a->k == N_FIELD || n->a->k == N_INDEX || n->a->k == N_DEREF) r = clval(n->a, s, &cell);
  if (r == R_OK && cell->k != CV_PTR && cell->k != CV_SLICE && cell->k != CV_STR) base = *cell; else { cell = NULL; EV(n->a, s, &base); }
  EV(n->b, s, &lo); if (lo.k != CV_INT) return R_FAIL;
  if (has_hi) { EV(n->c, s, &hi); if (hi.k != CV_INT) return R_FAIL; }
  int hs = 0; int64_t sv = 0;
  if (n->d) { CVal sn; EV(n->d, s, &sn); hs = 1; sv = (int64_t)sn.i; }
  int64_t l = (int64_t)lo.i;
  Type *bt = cv_typeof(&base);
  if (base.k == CV_STR) {
    int64_t h = has_hi ? (int64_t)hi.i : base.slen;
    CVal r2 = cv_str(base.s + l, (int)(h - l)); r2.t = ptr_to(array_of(t_u8, h - l, hs, sv), 1); *out = r2; return R_OK;
  }
  if (base.k == CV_AGG && bt->k == TY_ARRAY) {
    if (!cell) cell = box(base);
    int64_t h = has_hi ? (int64_t)hi.i : base.n;
    CVal p = {0}; p.k = CV_PTR; p.base = cell; p.idx = l; p.t = ptr_to(array_of(bt->elem, h - l, hs, sv), 0); *out = p; return R_OK;
  }
  if (base.k == CV_UNDEF && bt->k == TY_ARRAY) {
    if (!cell) return R_FAIL;
    *cell = agg_new(bt); return ev_slice(n, s, out);
  }
  if (base.k == CV_SLICE) {
    int64_t h = has_hi ? (int64_t)hi.i : base.slen;
    if (base.base && base.base->k == CV_STR) { CVal r2 = cv_str(base.base->s + base.idx + l, (int)(h - l)); r2.t = ptr_to(array_of(t_u8, h - l, hs, sv), 1); *out = r2; return R_OK; }
    CVal p = {0}; p.k = CV_PTR; p.base = base.base; p.idx = base.idx + l; p.t = ptr_to(array_of(bt->elem, h - l, hs, sv), bt->isconst); *out = p; return R_OK;
  }
  if (base.k == CV_PTR && base.base) {
    Type *et; int64_t len = -1; int64_t start;
    if (bt->k == TY_PTR && bt->elem->k == TY_ARRAY) { et = bt->elem->elem; len = bt->elem->len; start = base.idx < 0 ? 0 : base.idx; if (base.idx < 0) { CVal *c = base.base; if (c->k == CV_STR) { int64_t h = has_hi ? (int64_t)hi.i : c->slen; CVal r2 = cv_str(c->s + l, (int)(h - l)); r2.t = ptr_to(array_of(t_u8, h - l, hs, sv), 1); *out = r2; return R_OK; } if (c->k == CV_UNDEF) *c = agg_new(bt->elem); } }
    else if (bt->k == TY_MPTR) { et = bt->elem; start = base.idx < 0 ? 0 : base.idx; }
    else if (bt->k == TY_PTR) { et = bt->elem; len = 1; start = base.idx < 0 ? 0 : base.idx; }
    else return R_FAIL;
    int64_t h = has_hi ? (int64_t)hi.i : len; if (h < 0) return R_FAIL;
    CVal p = {0}; p.k = CV_PTR; p.base = base.base; p.idx = start + l;
    if (bt->k == TY_PTR && bt->elem->k != TY_ARRAY) { p.base = box(*base.base); p.idx = l; } /* single item: view as array of 1 */
    p.t = ptr_to(array_of(et, h - l, hs, sv), bt->isconst); *out = p; return R_OK;
  }
  if (getenv("ZB_DBG")) fprintf(stderr, "slice fail base k=%d t=%s basebase=%d\n", base.k, tname(bt), base.base ? base.base->k : -1);
  return R_FAIL;
}

/* ---------- lvalues ---------- */
static int base_cell(Node *a, Scope *s, CVal **cell) {
  /* the cell an lvalue chain operates on; pointers are dereferenced */
  int r = clval(a, s, cell);
  if (r != R_OK) {
    CVal v; int r2 = ev(a, s, &v); if (r2 != R_OK) return r2;
    if (v.k != CV_PTR && v.k != CV_SLICE) return R_FAIL;
    *cell = box(v);
  }
  return R_OK;
}
/* parent links for struct-field cells (so &agg.field materializes as parent symbol + offset) */
static void **cp_k; static CVal **cp_p; static int *cp_f; static int cp_cap, cp_n;
CVal *cell_parent(CVal *c, int *fi) {
  if (!cp_cap) return NULL;
  unsigned h = (unsigned)(((uintptr_t)c >> 4) * 2654435761u) & (cp_cap - 1);
  while (cp_k[h]) { if (cp_k[h] == c) { *fi = cp_f[h]; return cp_p[h]; } h = (h + 1) & (cp_cap - 1); }
  return NULL;
}
static void cp_put(CVal *c, CVal *par, int fi) {
  int dummy; if (cell_parent(c, &dummy)) return;
  if (cp_n * 2 >= cp_cap) {
    int oc = cp_cap; void **ok = cp_k; CVal **op = cp_p; int *of = cp_f; cp_cap = oc ? oc * 2 : 256;
    cp_k = xalloc(sizeof(void *) * cp_cap); cp_p = xalloc(sizeof(CVal *) * cp_cap); cp_f = xalloc(sizeof(int) * cp_cap); cp_n = 0;
    for (int i = 0; i < oc; i++) if (ok[i]) cp_put(ok[i], op[i], of[i]);
  }
  unsigned h = (unsigned)(((uintptr_t)c >> 4) * 2654435761u) & (cp_cap - 1);
  while (cp_k[h]) h = (h + 1) & (cp_cap - 1);
  cp_k[h] = c; cp_p[h] = par; cp_f[h] = fi; cp_n++;
}
static int clval(Node *n, Scope *s, CVal **cell) {
  switch (n->k) {
  case N_IDENT: {
    Sym *y; Decl *d;
    if (!lookup(s, n->s, &y, &d)) return R_FAIL;
    if (y) { if (y->k != S_CVAL) return R_FAIL; *cell = &y->cv; return R_OK; }
    resolve_decl(d); if (d->kind == D_CONST) { *cell = &d->cv; return R_OK; }
    return R_FAIL;
  }
  case N_COMPTIME: return clval(n->a, s, cell);
  case N_UNWRAP: return clval(n->a, s, cell);
  case N_DEREF: {
    CVal v; EV(n->a, s, &v);
    CVal *c = deref_cell(&v); if (!c) return R_FAIL; *cell = c; return R_OK;
  }
  case N_BUILTIN:
    if (!strcmp(n->s, "field") && n->list.n == 2) {
      CVal nm; EV(n->list.a[1], s, &nm); if (nm.k != CV_STR) return R_FAIL;
      Node tmp = *n; tmp.k = N_FIELD; tmp.a = n->list.a[0]; tmp.s = xstrndup(nm.s, nm.slen);
      return clval(&tmp, s, cell);
    }
    return R_FAIL;
  case N_FIELD: {
    CVal *c; int r = base_cell(n->a, s, &c); if (r != R_OK) return r;
    while (c->k == CV_PTR) { CVal *d = deref_cell(c); if (!d) return R_FAIL; c = d; }
    if (c->k == CV_UNDEF && c->t && (is_struct_like(c->t) || c->t->k == TY_UNION)) *c = agg_new(c->t);
    if (c->k != CV_AGG) return R_FAIL;
    Type *t = c->t;
    if (t->k == TY_UNION) {
      int fi = field_index(t, n->s); if (fi < 0) return R_FAIL;
      if (c->i != fi) { c->i = fi; *c->el[0] = cv_undef(field_at(t, fi)->t); }
      cp_put(c->el[0], c, -1); *cell = c->el[0]; return R_OK;
    }
    if (!is_struct_like(t)) return R_FAIL;
    int fi = field_index(t, n->s); if (fi < 0) return R_FAIL;
    if (t->k == TY_STRUCT) cp_put(c->el[fi], c, fi);
    *cell = c->el[fi]; return R_OK;
  }
  case N_INDEX: {
    CVal *c; int r = base_cell(n->a, s, &c); if (r != R_OK) return r;
    CVal iv; EV(n->b, s, &iv); if (iv.k != CV_INT) return R_FAIL;
    if (c->k == CV_PTR && c->t && c->t->k == TY_PTR) { CVal *d = deref_cell(c); if (!d) return R_FAIL; c = d; }
    if (c->k == CV_UNDEF && c->t && c->t->k == TY_ARRAY) *c = agg_new(c->t);
    if (c->k == CV_STR) return R_FAIL;
    CVal *e = elem_cell(c, (int64_t)iv.i); if (!e) return R_FAIL;
    *cell = e; return R_OK;
  }
  default: return R_FAIL;
  }
}
static int lv_const(Node *n, Scope *s) {
  for (;;) {
    if (n->k == N_FIELD || n->k == N_INDEX || n->k == N_UNWRAP || n->k == N_COMPTIME) { n = n->a; continue; }
    if (n->k == N_IDENT) { Sym *y; Decl *d; if (lookup(s, n->s, &y, &d) && y) return !y->mut; return 1; }
    return 0;
  }
}
/* address of (a field/element of) a runtime global, as a comptime pointer value */
static int global_addr(Node *n, Scope *s, char **sym, int64_t *off, Type **t) {
  if (n->k == N_IDENT) {
    Sym *y; Decl *d; if (!lookup(s, n->s, &y, &d) || y) return 0;
    resolve_decl(d); if (d->kind != D_VAR || !d->sym) return 0;
    *sym = d->sym; *off = 0; *t = d->t; return 1;
  }
  if (n->k == N_FIELD) {
    if (!global_addr(n->a, s, sym, off, t)) return 0;
    if (!is_struct_like(*t) && (*t)->k != TY_UNION) return 0;
    Field *f = find_field((*t)->ct, n->s); if (!f) return 0;
    *off += f->off; *t = f->t; return 1;
  }
  if (n->k == N_INDEX) {
    if (!global_addr(n->a, s, sym, off, t) || (*t)->k != TY_ARRAY) return 0;
    CVal iv; if (ev(n->b, s, &iv) != R_OK || iv.k != CV_INT) return 0;
    *t = (*t)->elem; *off += (int64_t)iv.i * tsize(*t); return 1;
  }
  return 0;
}

/* ---------- main evaluator ---------- */
static Node *fail_node;
static int ev_(Node *n, Scope *s, CVal *out);
static int ev(Node *n, Scope *s, CVal *out) {
  if (n->tok) ev_cur = n;
  int r = ev_(n, s, out);
  if (r == R_FAIL) {
    if (!fail_node) fail_node = n;
    if (ct_trace < 0) ct_trace = getenv("ZB_CT_TRACE") != NULL;
    if (ct_trace && ct_force) fprintf(stderr, "ct: cannot evaluate node kind %d at %s:%d\n", n->k, n->tok ? n->tok->file : "?", n->tok ? n->tok->line : 0);
  }
  return r;
}
static Type *lab_rt(const char *l) {
  for (int i = lrt_n - 1; i >= 0; i--) if (l && lrt_l[i] && !strcmp(lrt_l[i], l)) return lrt_t[i];
  return NULL;
}
static int ev_if(Node *n, Scope *s, Type *rt, CVal *out) {
  CVal c; EV(n->a, s, &c);
  int some = c.k == CV_NULL && c.slen > 0; if (some) c = unwrap_some_null(c);
  if (n->cap || some || c.k == CV_NULL || c.k == CV_ERR) {
    if (c.k == CV_UNDEF) return R_FAIL;
    if (!some && (c.k == CV_NULL || c.k == CV_ERR)) {
      if (!n->c) { *out = cv_void(); return R_OK; }
      Scope *es = new_scope(s, NULL); if (c.k == CV_ERR) bind_cap(es, n->cap2, c);
      return ev_rt(n->c, es, rt, out);
    }
    if (some || c.k != CV_BOOL || n->cap) {
      Scope *ts = new_scope(s, NULL);
      if (n->capref) { CVal p = {0}; p.k = CV_PTR; CVal *cell; if (clval(n->a, s, &cell) == R_OK) p.base = cell; else p.base = box(c); p.idx = -1; p.t = ptr_to(cv_typeof(&c), 0); bind_cap(ts, n->cap, p); }
      else bind_cap(ts, n->cap, c);
      return ev_rt(n->b, ts, rt, out);
    }
  }
  if (c.k != CV_BOOL) return R_FAIL;
  if (c.i) return ev_rt(n->b, s, rt, out);
  if (!n->c) { *out = cv_void(); return R_OK; }
  return ev_rt(n->c, s, rt, out);
}
static CVal neg_like(CVal a, const char *op) {
  if (a.k == CV_AGG && a.t->k == TY_ARRAY) {
    CVal r = agg_new(a.t); for (int i = 0; i < a.n; i++) *r.el[i] = neg_like(*a.el[i], op); return r;
  }
  if (op[0] == '!') return cv_bool(!a.i);
  Type *t = cv_typeof(&a);
  if (a.k == CV_FLOAT) return cv_float(-a.f, t);
  if (op[0] == '~') return cv_int(wrap_int(~a.i, t), t);
  return cv_int(wrap_int(-a.i, t), t);
}
static int ev_(Node *n, Scope *s, CVal *out) {
  CVal a, b;
  switch (n->k) {
  case N_INT: case N_CHAR: *out = cv_int((i128)n->ival, t_cint); return R_OK;
  case N_FLOAT: *out = cv_float(n->fval, t_cfloat); return R_OK;
  case N_STR: *out = cv_str(n->s, n->slen); return R_OK;
  case N_TRUE: *out = cv_bool(1); return R_OK;
  case N_FALSE: *out = cv_bool(0); return R_OK;
  case N_NULL: *out = cv_null(); return R_OK;
  case N_UNDEF: *out = cv_undef(NULL); return R_OK;
  case N_ENUMLIT: *out = cv_enumlit(n->s); return R_OK;
  case N_ERRVAL: { CVal v = {0}; v.k = CV_ERR; v.i = err_id(n->s); v.t = t_errset; *out = v; return R_OK; }
  case N_ERRSET: for (int i = 0; i < n->list.n; i++) err_id(((Node *)n->list.a[i])->s); *out = cv_ty(t_errset); return R_OK;
  case N_UNREACHABLE:
    if (ct_force) die("%s:%d: reached unreachable code at comptime", n->tok->file, n->tok->line);
    return R_FAIL;
  case N_NOP: *out = cv_void(); return R_OK;
  case N_IDENT: {
    Type *pt = n->tok && n->tok->k == TK_ID && n->tok->ival ? NULL : prim_type(n->s); if (pt) { *out = cv_ty(pt); return R_OK; }
    Sym *y; Decl *d;
    if (!lookup(s, n->s, &y, &d)) die("%s:%d: use of undeclared identifier '%s'", n->tok->file, n->tok->line, n->s);
    if (y) { if (y->k == S_CVAL) { *out = y->cv; return R_OK; }
      if (y->t && y->t->k == TY_ENUM && y->t->ct && !y->t->ct->nonexh) { layout(y->t->ct);
        if (y->t->ct->fields.n == 1) { *out = cv_int(((Field *)y->t->ct->fields.a[0])->val, y->t); return R_OK; } }
      if (y->t && y->t->k == TY_VOID) { *out = cv_void(); return R_OK; }
      if (y->t && y->t->k == TY_NULL) { *out = cv_null_pub(); return R_OK; }
      return R_FAIL; }
    resolve_decl(d);
    if (d->kind == D_CONST || d->kind == D_FN) { *out = d->cv; return R_OK; }
    return R_FAIL;
  }
  case N_FIELD: {
    Type *at;
    if (!strcmp(n->s, "len") && is_local_array(s, n->a, &at)) { *out = cv_int(at->len, t_usize); return R_OK; }
    if (!strcmp(n->s, "len") && n->a->k == N_IDENT) { Sym *y; Decl *d; /* runtime tuple: length is comptime */
      if (lookup(s, n->a->s, &y, &d) && y && y->k == S_LOCAL && y->t) { Type *t = y->t; if (t->k == TY_PTR) t = t->elem;
        if (is_tuple_type(t)) { layout(t->ct); *out = cv_int(t->ct->fields.n, t_cint); return R_OK; } } }
    if (ct_field_of(s, n, out)) return R_OK;
    EV(n->a, s, &a);
    if (ceval_member(a, n->s, out)) return R_OK;
    if (a.k == CV_TYPE && ct_force) die("%s:%d: no member '%s' in %s", n->tok->file, n->tok->line, n->s, tname(a.t));
    return R_FAIL;
  }
  case N_INDEX: {
    EV(n->a, s, &a); EV(n->b, s, &b);
    if (b.k != CV_INT) return R_FAIL;
    if (a.k == CV_PTR && a.t && a.t->k == TY_PTR && a.t->elem->k != TY_ARRAY) return R_FAIL;
    int64_t l;
    if (a.k == CV_AGG || a.k == CV_STR || a.k == CV_SLICE || (a.k == CV_PTR && a.base)) {
      if (cv_len(&a, &l) && (b.i < 0 || b.i > l)) die("%s:%d: index %lld out of bounds at comptime", n->tok->file, n->tok->line, (long long)b.i);
      *out = cv_elem(&a, (int64_t)b.i); return R_OK;
    }
    return R_FAIL;
  }
  case N_SLICE: return ev_slice(n, s, out);
  case N_DEREF: {
    EV(n->a, s, &a);
    if (a.k == CV_STR || (a.k == CV_PTR && a.base && a.idx >= 0 && a.t && a.t->k == TY_PTR && a.t->elem->k == TY_ARRAY && !is_vec(a.t->elem) &&
        !(a.base->k == CV_AGG && cv_typeof(a.base)->k == TY_ARRAY && cv_typeof(a.base)->elem == a.t->elem))) {
      /* dereferencing a pointer to a (sub-)array: copy the elements out */
      Type *at = a.k == CV_STR ? (a.t && a.t->k == TY_PTR && a.t->elem->k == TY_ARRAY ? a.t->elem : array_of(t_u8, a.slen, 0, 0)) : a.t->elem;
      CVal r = agg_new(at);
      for (int64_t i = 0; i < at->len; i++) {
        if (a.k == CV_STR) *r.el[i] = cv_int((unsigned char)a.s[i], t_u8);
        else if (a.base->k == CV_STR) *r.el[i] = cv_int((unsigned char)a.base->s[a.idx + i], t_u8);
        else { CVal *e = elem_cell(a.base, a.idx + i); if (!e) { if (getenv("ZB_DBG")) fprintf(stderr, "copy fail base k=%d t=%s idx=%lld i=%lld\n", a.base->k, tname(cv_typeof(a.base)), (long long)a.idx, (long long)i); return R_FAIL; } *r.el[i] = cv_copy(*e); }
      }
      *out = r; return R_OK;
    }
    if (a.k == CV_AGG && a.t && a.t->k == TY_ARRAY) { *out = a; return R_OK; } /* `++` result viewed as *const [N]T */
    CVal *c = deref_cell(&a); if (!c) { if (getenv("ZB_DBG")) fprintf(stderr, "deref fail k=%d t=%s idx=%lld basek=%d\n", a.k, a.t ? tname(a.t) : "-", (long long)a.idx, a.base ? a.base->k : -1); return R_FAIL; }
    *out = *c; return R_OK;
  }
  case N_UNWRAP:
    EV(n->a, s, &a);
    if (a.k == CV_NULL && a.slen > 0) { *out = unwrap_some_null(a); return R_OK; }
    if (a.k == CV_NULL) { if (ct_force) die("%s:%d: attempt to use null value at comptime", n->tok->file, n->tok->line); return R_FAIL; }
    if (a.k == CV_UNDEF) return R_FAIL;
    *out = a; return R_OK;
  case N_UN: {
    if (!strcmp(n->s, "&")) {
      CVal *cell; CVal p = {0}; p.k = CV_PTR; p.idx = -1;
      int r = clval(n->a, s, &cell);
      if (r == R_OK) { p.base = cell; p.t = ptr_to(cv_typeof(cell), lv_const(n->a, s)); *out = p; return R_OK; }
      if (r == R_CF) return r;
      char *sym; int64_t off; Type *gt;
      if (global_addr(n->a, s, &sym, &off, &gt)) { p.s = sym; p.i = off; p.t = ptr_to(gt, 0); *out = p; return R_OK; }
      if (n->a->k == N_FIELD) { /* &(rvalue).field: keep the parent aggregate */
        CVal b; int rb = ev(n->a->a, s, &b);
        if (rb == R_OK && b.k == CV_AGG && b.t && b.t->k == TY_STRUCT) {
          int fi = field_index(b.t, n->a->s);
          if (fi >= 0) { CVal *bc = box(b); CVal *fc = bc->el[fi]; cp_put(fc, bc, fi); p.base = fc; p.t = ptr_to(cv_typeof(fc), 1); *out = p; return R_OK; }
        }
      }
      EV(n->a, s, &a);
      p.base = box(a); p.t = ptr_to(cv_typeof(&a), 1); *out = p; return R_OK;
    }
    EV(n->a, s, &a);
    if (a.k == CV_AGG && a.t->k == TY_ARRAY) { *out = neg_like(a, n->s); return R_OK; }
    if (n->s[0] == '!') { if (a.k != CV_BOOL) return R_FAIL; *out = cv_bool(!a.i); return R_OK; }
    if (a.k == CV_FLOAT && n->s[0] == '-') { *out = neg_like(a, n->s); return R_OK; }
    if (a.k != CV_INT) return R_FAIL;
    if (n->s[0] == '~' && cv_typeof(&a)->k != TY_INT) return R_FAIL;
    *out = neg_like(a, n->s); return R_OK;
  }
  case N_BIN: {
    const char *op = n->s;
    if (!strcmp(op, "and") || !strcmp(op, "or")) {
      EV(n->a, s, &a); if (a.k != CV_BOOL) return R_FAIL;
      if ((op[0] == 'a') != !!a.i) { *out = a; return R_OK; }
      EV(n->b, s, &b); if (b.k != CV_BOOL) return R_FAIL; *out = b; return R_OK;
    }
    EV(n->a, s, &a); EV(n->b, s, &b);
    if (!strcmp(op, "||")) { *out = cv_ty(t_errset); return R_OK; }
    return ev_bin(op, a, b, out);
  }
  case N_ORELSE:
    EV(n->a, s, &a);
    if (a.k == CV_UNDEF) return R_FAIL;
    if (a.k == CV_NULL && a.slen > 0) { *out = unwrap_some_null(a); return R_OK; }
    if (a.k == CV_NULL) return ev(n->b, s, out);
    *out = a; return R_OK;
  case N_CATCH:
    EV(n->a, s, &a);
    if (a.k == CV_UNDEF) return R_FAIL;
    if (a.k == CV_ERR) { Scope *cs = new_scope(s, NULL); bind_cap(cs, n->cap, a); return ev(n->b, cs, out); }
    *out = a; return R_OK;
  case N_TRY:
    EV(n->a, s, &a);
    if (a.k == CV_ERR) { if (!ct_force) return R_FAIL; xs = X_RET; xlabel = NULL; xval = a; return R_CF; }
    if (a.k == CV_UNDEF) return R_FAIL;
    *out = a; return R_OK;
  case N_IF: return ev_if(n, s, NULL, out);
  case N_SWITCH: return ev_switch(n, s, NULL, out);
  case N_WHILE: return ev_while(n, s, out);
  case N_FOR: return ev_for(n, s, out);
  case N_BLOCK: return ev_block(n, s, out);
  case N_BREAK: {
    CVal v = cv_void();
    if (n->a) EVR(n->a, s, lab_rt(n->label), &v);
    xs = X_BRK; xlabel = n->label; xval = v; return R_CF;
  }
  case N_CONTINUE: {
    CVal v = cv_void(); if (n->a) EV(n->a, s, &v);
    xs = X_CONT; xlabel = n->label; xval = v; return R_CF;
  }
  case N_RETURN: {
    if (!ct_force) return R_FAIL;
    CVal v = cv_void(); if (n->a) EVR(n->a, s, cur_rt, &v);
    xs = X_RET; xlabel = NULL; xval = v; return R_CF;
  }
  case N_DEFER: case N_ERRDEFER: *out = cv_void(); return R_OK;
  case N_VAR: {
    if (!ct_force && !(n->flags & F_CONST)) return R_FAIL;
    Type *t = NULL;
    if (n->a) { CVal tv; ct_force++; int r = ev(n->a, s, &tv); ct_force--; if (r != R_OK) return r; if (tv.k != CV_TYPE) return R_FAIL; t = tv.t; }
    CVal v;
    if (!n->b) v = cv_undef(t);
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
    if (strcmp(n->s, "_")) { bind_cval(s, n->s, cv_copy(v)); if (!(n->flags & F_CONST)) ((Sym *)s->syms.a[s->syms.n - 1])->mut = 1; }
    *out = cv_void(); return R_OK;
  }
  case N_ASSIGN: {
    if (!ct_force) return R_FAIL;
    if (n->a->k == N_IDENT && !strcmp(n->a->s, "_")) { EV(n->b, s, &b); *out = cv_void(); return R_OK; }
    if (n->a->k == N_DEREF && !strcmp(n->s, "=")) { /* store through a pointer to a sub-array view: elementwise */
      CVal pv; EV(n->a->a, s, &pv);
      if (pv.k == CV_PTR && pv.base && pv.idx >= 0 && pv.t && pv.t->k == TY_PTR && pv.t->elem->k == TY_ARRAY && !is_vec(pv.t->elem) &&
          pv.base->k == CV_AGG && cv_typeof(pv.base)->k == TY_ARRAY && cv_typeof(pv.base)->elem != pv.t->elem) {
        Type *at = pv.t->elem; EVR(n->b, s, at, &b); b = ccoerce(b, at);
        for (int64_t i = 0; i < at->len && pv.idx + i < pv.base->n; i++) {
          CVal e = b.k == CV_AGG ? *b.el[i] : b.k == CV_STR ? cv_int(i < b.slen ? (unsigned char)b.s[i] : 0, t_u8) : cv_undef(at->elem);
          assign(pv.base->el[pv.idx + i], cv_copy(e));
        }
        *out = cv_void(); return R_OK;
      }
    }
    if (n->a->k == N_FIELD && (!strcmp(n->a->s, "len") || !strcmp(n->a->s, "ptr"))) { /* slice.len / slice.ptr */
      CVal *c; if (base_cell(n->a->a, s, &c) == R_OK) {
        while (c->k == CV_PTR && c->t && c->t->k == TY_PTR && c->t->elem->k == TY_SLICE) { CVal *d = deref_cell(c); if (!d) break; c = d; }
        Type *st = cv_typeof(c);
        if (st && st->k == TY_SLICE && (c->k == CV_SLICE || c->k == CV_PTR || c->k == CV_UNDEF)) {
          if (c->k != CV_SLICE) {
            int64_t l = 0; if (c->k == CV_PTR) cv_len(c, &l);
            CVal sl = {0}; sl.k = CV_SLICE; sl.t = st; sl.slen = (int)l;
            if (c->k == CV_PTR) { sl.base = c->base; sl.idx = c->idx < 0 ? 0 : c->idx; }
            *c = sl;
          }
          if (!strcmp(n->a->s, "len")) {
            EVR(n->b, s, t_usize, &b);
            CVal cur = cv_int(c->slen, t_usize), rv = b;
            if (strcmp(n->s, "=")) { char op[8]; int l = (int)strlen(n->s) - 1; memcpy(op, n->s, l); op[l] = 0; if (ev_bin(op, cur, ccoerce(b, t_usize), &rv) != R_OK) return R_FAIL; }
            if (rv.k != CV_INT) return R_FAIL;
            c->slen = (int)rv.i;
          } else {
            EVR(n->b, s, NULL, &b);
            if (b.k != CV_PTR && b.k != CV_SLICE) return R_FAIL;
            c->base = b.base; c->idx = b.idx < 0 ? 0 : b.idx;
          }
          *out = cv_void(); return R_OK;
        }
      }
    }
    CVal *cell; int r = clval(n->a, s, &cell); if (r != R_OK) return r;
    Type *ct = cv_typeof(cell); if (ct && (ct->k == TY_UNDEF || ct->k == TY_NULL)) ct = NULL;
    if (!strcmp(n->s, "=")) {
      EVR(n->b, s, ct, &b);
      assign(cell, ct ? ccoerce(b, ct) : b);
    } else {
      EVR(n->b, s, NULL, &b);
      char op[8]; int l = (int)strlen(n->s) - 1; memcpy(op, n->s, l); op[l] = 0;
      CVal rv; if (ev_bin(op, *cell, b, &rv) != R_OK) return R_FAIL;
      assign(cell, ct ? ccoerce(rv, ct) : rv);
    }
    *out = cv_void(); return R_OK;
  }
  case N_DESTRUCT: {
    for (int i = 0; i < n->list.n; i++) { Node *t = n->list.a[i]; if (!ct_force && !(t->k == N_VAR && (t->flags & F_CONST))) return R_FAIL; }
    EV(n->b, s, &a);
    for (int i = 0; i < n->list.n; i++) {
      Node *t = n->list.a[i]; CVal e = cv_elem(&a, i);
      if (t->k == N_VAR) {
        if (t->a) { Type *tt = eval_type(t->a, s); e = ccoerce(e, tt); }
        bind_cval(s, t->s, cv_copy(e)); if (!(t->flags & F_CONST)) ((Sym *)s->syms.a[s->syms.n - 1])->mut = 1;
      } else if (t->k == N_IDENT && !strcmp(t->s, "_")) continue;
      else { CVal *cell; int r = clval(t, s, &cell); if (r != R_OK) return r; assign(cell, ccoerce(e, cv_typeof(cell))); }
    }
    *out = cv_void(); return R_OK;
  }
  case N_COMPTIME: { ct_force++; int r = ev(n->a, s, out); ct_force--; return r; }
  case N_INIT: return ev_init(n, s, NULL, out);
  case N_CALL: return ev_call(n, s, out);
  case N_BUILTIN: brt = NULL; return ev_builtin(n, s, out);
  case N_TPTR: {
    CVal e; ct_force++; int r = ev(n->a, s, &e); ct_force--; if (r != R_OK) return r; if (e.k != CV_TYPE) return R_FAIL;
    int c = !!(n->flags & F_CONST);
    if (!strcmp(n->s, "*")) *out = cv_ty(ptr_to(e.t, c));
    else if (!strcmp(n->s, "[]")) { int64_t sv = 0; int hs = 0; if (n->b) { EVR(n->b, s, e.t, &b); sv = (int64_t)b.i; hs = 1; } *out = cv_ty(slice_of_s(e.t, c, hs, sv)); }
    else { int64_t sv = 0; int hs = 0; if (n->b) { EVR(n->b, s, e.t, &b); sv = (int64_t)b.i; hs = 1; } *out = cv_ty(mptr_to(e.t, c, hs, sv)); }
    return R_OK;
  }
  case N_TARRAY: {
    if (!n->a) return R_FAIL;
    ct_force++; int r = ev(n->a, s, &a); if (r == R_OK) r = ev(n->b, s, &b); ct_force--;
    if (r != R_OK) return r; if (a.k != CV_INT || b.k != CV_TYPE) return R_FAIL;
    int hs = 0; int64_t sv = 0; if (n->c) { CVal c; EVR(n->c, s, b.t, &c); hs = 1; sv = (int64_t)c.i; }
    *out = cv_ty(array_of(b.t, (int64_t)a.i, hs, sv)); return R_OK;
  }
  case N_TOPT: { ct_force++; int r = ev(n->a, s, &a); ct_force--; if (r != R_OK) return r; if (a.k != CV_TYPE) return R_FAIL; *out = cv_ty(opt_of(a.t)); return R_OK; }
  case N_TERRU: {
    ct_force++; int r = ev(n->a, s, &a); if (r == R_OK) r = ev(n->b, s, &b); ct_force--;
    if (r != R_OK) return r; if (b.k != CV_TYPE) return R_FAIL;
    *out = cv_ty(erru_of(b.t)); return R_OK;
  }
  case N_TFN: {
    Vec ps = {0};
    for (int i = 0; i < n->list.n; i++) {
      Node *p = n->list.a[i]; if (p->flags & F_VARARGS) continue;
      if (!p->a) { vpush(&ps, t_anytype); continue; }
      ct_force++; int r = ev(p->a, s, &a); ct_force--; if (r != R_OK) return r; if (a.k != CV_TYPE) return R_FAIL; vpush(&ps, a.t);
    }
    ct_force++; int r = ev(n->a, s, &a); ct_force--; if (r != R_OK) return r; if (a.k != CV_TYPE) return R_FAIL;
    Type *rt = a.t; if (n->flags & F_INFERR) rt = erru_of(rt);
    *out = cv_ty(fn_type(&ps, rt, !!(n->flags & F_VARARGS))); return R_OK;
  }
  case N_CONTAINER: *out = cv_ty(container_from(n, s, NULL)->type); return R_OK;
  case N_ASM: return R_FAIL;
  default: return R_FAIL;
  }
}

/* evaluation with a result type */
static Type *unwrap_rt(Type *t) { while (t && (t->k == TY_OPT || t->k == TY_ERRU)) t = t->elem; return t; }
static int ev_rt(Node *n, Scope *s, Type *rt, CVal *out) {
  if (!rt || rt->k == TY_ANYTYPE) return ev(n, s, out);
  int r;
  switch (n->k) {
  case N_INIT: if (!n->a) { r = ev_init(n, s, rt, out); if (r == R_OK) *out = ccoerce(*out, rt); return r; } break;
  case N_UNDEF: *out = cv_undef(rt); return R_OK;
  case N_CALL:
    if (n->a->k == N_ENUMLIT) {
      Type *t = unwrap_rt(rt); if (t->k == TY_PTR) t = t->elem;
      if (!t->ct) return R_FAIL;
      Decl *d = find_decl(t->ct, n->a->s); if (!d) die("%s:%d: no decl '%s' in %s", n->tok->file, n->tok->line, n->a->s, tname(t));
      resolve_decl(d); CVal nv = {0};
      r = ev_call_fn(n, s, d->cv, 0, nv, NULL, out); if (r == R_OK) *out = ccoerce(*out, rt); return r;
    }
    break;
  case N_UN:
    if (!strcmp(n->s, "&") && (rt->k == TY_PTR || rt->k == TY_SLICE || rt->k == TY_MPTR || unwrap_rt(rt)->k == TY_PTR || unwrap_rt(rt)->k == TY_SLICE)) {
      Type *pt = unwrap_rt(rt); Node *x = n->a;
      if ((x->k == N_INIT && !x->a) || x->k == N_BUILTIN || x->k == N_ENUMLIT || (x->k == N_CALL && x->a->k == N_ENUMLIT)) {
        Type *et = NULL;
        if (pt->k == TY_PTR) et = pt->elem;
        else if (x->k == N_INIT) et = array_of(pt->elem, x->list.n, 0, 0);
        CVal v;
        if (et && et->k == TY_ARRAY && et->len < 0) et = NULL;
        if (x->k == N_BUILTIN && pt->k == TY_SLICE) { r = ev(x, s, &v); } else { r = ev_rt(x, s, et, &v); }
        if (r != R_OK) return r;
        if (v.k == CV_AGG && v.t == t_splat) return R_FAIL;
        CVal p = {0}; p.k = CV_PTR; p.base = box(v); p.idx = -1; p.t = ptr_to(cv_typeof(&v), 1);
        *out = ccoerce(p, rt); return R_OK;
      }
    }
    break;
  case N_BLOCK:
    if (n->label && lrt_n < 64) {
      lrt_l[lrt_n] = n->label; lrt_t[lrt_n] = rt; lrt_n++;
      r = ev(n, s, out); lrt_n--;
      if (r == R_OK) *out = ccoerce(*out, rt);
      return r;
    }
    break;
  case N_IF: r = ev_if(n, s, rt, out); if (r == R_OK) *out = ccoerce(*out, rt); return r;
  case N_SWITCH: r = ev_switch(n, s, rt, out); if (r == R_OK) *out = ccoerce(*out, rt); return r;
  case N_COMPTIME: ct_force++; r = ev_rt(n->a, s, rt, out); ct_force--; return r;
  case N_ORELSE: {
    CVal a; EVR(n->a, s, opt_of(rt), &a);
    if (a.k == CV_UNDEF) return R_FAIL;
    if (a.k == CV_NULL && a.slen > 0) { *out = unwrap_some_null(a); return R_OK; }
    if (a.k == CV_NULL) return ev_rt(n->b, s, rt, out);
    *out = ccoerce(a, rt); return R_OK;
  }
  case N_CATCH: {
    CVal a; EV(n->a, s, &a);
    if (a.k == CV_UNDEF) return R_FAIL;
    if (a.k == CV_ERR) { Scope *cs = new_scope(s, NULL); bind_cap(cs, n->cap, a); return ev_rt(n->b, cs, rt, out); }
    *out = ccoerce(a, rt); return R_OK;
  }
  case N_BUILTIN: brt = rt; r = ev_builtin(n, s, out); if (r == R_OK) *out = ccoerce(*out, rt); return r;
  default: break;
  }
  r = ev(n, s, out);
  if (r == R_OK) *out = ccoerce(*out, rt);
  return r;
}

/* ---------- initializers ---------- */
static int ev_init(Node *n, Scope *s, Type *t, CVal *out) {
  if (n->a) {
    if (n->a->k == N_TARRAY && !n->a->a) {
      CVal e; ct_force++; int r = ev(n->a->b, s, &e); ct_force--; if (r != R_OK) return r;
      int hs = 0; int64_t sv = 0; if (n->a->c) { CVal c; EVR(n->a->c, s, e.t, &c); hs = 1; sv = (int64_t)c.i; }
      t = array_of(e.t, n->list.n, hs, sv);
    } else {
      CVal tv; ct_force++; int r = ev(n->a, s, &tv); ct_force--; if (r != R_OK) return r;
      if (tv.k != CV_TYPE) return R_FAIL; t = tv.t;
    }
  }
  t = unwrap_rt(t);
  if (t && t->k == TY_PTR && !n->a) t = NULL;
  if (t && t->k == TY_SLICE && !n->a && !(n->flags & F_FIELDS)) { /* ZON-style .{...} with a slice result type */
    Type *at = array_of(t->elem, n->list.n, t->hassent, t->sent); CVal arr; int r = ev_init(n, s, at, &arr); if (r != R_OK) return r;
    CVal p = {0}; p.k = CV_PTR; p.idx = -1; p.base = box(arr); p.t = ptr_to(at, 1); *out = ccoerce(p, t); return R_OK;
  }
  if (t && t->k == TY_ARRAY) {
    CVal a = agg_new(t);
    if (n->flags & F_FIELDS) return R_FAIL;
    for (int i = 0; i < n->list.n && i < a.n; i++) { CVal v; EVR(n->list.a[i], s, t->elem, &v); *a.el[i] = ccoerce(v, t->elem); }
    *out = a; return R_OK;
  }
  if (t && t->k == TY_UNION) {
    if (!(n->flags & F_FIELDS) || n->list.n != 1) { if (!n->list.n) { *out = agg_new(t); return R_OK; } return R_FAIL; }
    Node *nm = n->list2.a[0]; int fi = field_index(t, nm->s); if (fi < 0) die("%s:%d: no field %s in %s", n->tok->file, n->tok->line, nm->s, tname(t));
    CVal v; EVR(n->list.a[0], s, field_at(t, fi)->t, &v);
    *out = mk_union(t, nm->s, v); return R_OK;
  }
  if (t && is_struct_like(t)) {
    CVal a = agg_new(t); char *set = xalloc(a.n + 1);
    for (int i = 0; i < n->list.n; i++) {
      int fi = (n->flags & F_FIELDS) ? field_index(t, ((Node *)n->list2.a[i])->s) : i;
      if (fi < 0 || fi >= a.n) die("%s:%d: no field %s in %s", n->tok->file, n->tok->line, (n->flags & F_FIELDS) ? ((Node *)n->list2.a[i])->s : "?", tname(t));
      Type *ft = field_at(t, fi)->t; CVal v; EVR(n->list.a[i], s, ft, &v);
      *a.el[fi] = ccoerce(v, ft); set[fi] = 1;
    }
    for (int i = 0; i < a.n; i++) if (!set[i]) *a.el[i] = default_of(t, field_at(t, i));
    *out = a; return R_OK;
  }
  /* anonymous struct / tuple literal */
  Vec names = {0}, types = {0}; CVal *vals = xalloc(sizeof(CVal) * (n->list.n + 1));
  for (int i = 0; i < n->list.n; i++) {
    EV(n->list.a[i], s, &vals[i]);
    vpush(&names, (n->flags & F_FIELDS) ? ((Node *)n->list2.a[i])->s : fmt("%d", i));
    vpush(&types, cv_typeof(&vals[i]));
  }
  CVal a = agg_new(mk_anon_struct(&names, &types, !(n->flags & F_FIELDS)));
  for (int i = 0; i < n->list.n; i++) *a.el[i] = cv_copy(vals[i]);
  *out = a; return R_OK;
}

/* ---------- function calls ---------- */
typedef struct { Decl *fd; CVal *args; int n; CVal res; } TMemo;
static Vec tmemo;
static char *cv_name(CVal *v) {
  switch (v->k) {
  case CV_TYPE: return tname(v->t);
  case CV_INT: if (v->t && v->t->k == TY_ENUM) { Container *c = v->t->ct; layout(c); for (int i = 0; i < c->fields.n; i++) { Field *f = c->fields.a[i]; if (f->val == (int64_t)v->i) return fmt(".%s", f->name); } } return fmt("%lld", (long long)v->i);
  case CV_BOOL: return v->i ? "true" : "false";
  case CV_ENUMLIT: return fmt(".%s", v->s);
  case CV_STR: return fmt("\"%.*s\"", v->slen > 20 ? 20 : v->slen, v->s);
  case CV_NULL: return "null";
  case CV_FN: return v->fn->name;
  default: return "{...}";
  }
}
static int ct_call(Decl *fd, CVal *args, int na, CVal *out) {
  Node *f = fd->node;
  if (!f->b) return R_FAIL;
  step();
  Scope *fs = new_scope(fd->ct->scope, NULL);
  int np = f->list.n; CVal *bound = xalloc(sizeof(CVal) * (np + 1));
  for (int i = 0; i < np; i++) {
    Node *p = f->list.a[i];
    if (p->flags & F_VARARGS) break;
    Type *pt = NULL;
    if (p->a && !(p->flags & F_ANYTYPE)) { CVal tv; ct_force++; int r = ev(p->a, fs, &tv); ct_force--; if (r == R_OK && tv.k == CV_TYPE) pt = tv.t; }
    CVal a = i < na ? args[i] : cv_undef(NULL);
    if (pt) a = ccoerce(a, pt);
    bound[i] = a;
    if (p->s) bind_cval(fs, p->s, cv_copy(a));
  }
  Type *rt = NULL; int has_rt = fn_ret_type(fd, fs, &rt);
  int memo = has_rt && rt == t_type;
  if (memo) {
    for (int i = 0; i < tmemo.n; i++) {
      TMemo *m = tmemo.a[i]; if (m->fd != fd || m->n != np) continue;
      int ok = 1; for (int j = 0; j < np && ok; j++) if (!cval_eq(&m->args[j], &bound[j])) ok = 0;
      if (ok) { *out = m->res; return R_OK; }
    }
  }
  Type *srt = cur_rt; cur_rt = has_rt ? rt : NULL; int slrt = lrt_n;
  ct_force++;
  CVal rv; int r = ev(f->b, fs, &rv);
  ct_force--; cur_rt = srt; lrt_n = slrt;
  if (r == R_CF) {
    if (xs == X_RET) { xs = X_NONE; rv = xval; r = R_OK; }
    else die("%s:%d: break/continue out of function %s", f->tok->file, f->tok->line, fd->name);
  } else if (r == R_OK) rv = cv_void();
  if (r != R_OK) return r;
  if (has_rt) rv = ccoerce(rv, rt);
  if (memo) {
    if (rv.k == CV_TYPE && rv.t->ct && (!strncmp(rv.t->ct->name, "anon", 4) || (rv.t->ct->node && rv.t->ct->scope && rv.t->ct->scope->up && rv.t->ct->scope->up->up == fs))) {
      char nm[512]; int m = snprintf(nm, sizeof nm, "%s.%s(", fd->ct->name, fd->name);
      for (int i = 0; i < np && m < 400; i++) m += snprintf(nm + m, sizeof nm - m, "%s%s", i ? "," : "", cv_name(&bound[i]));
      snprintf(nm + m, sizeof nm - m, ")");
      rv.t->ct->name = xstrndup(nm, strlen(nm));
    }
    TMemo *mm = xalloc(sizeof *mm); mm->fd = fd; mm->args = bound; mm->n = np; mm->res = rv; vpush(&tmemo, mm);
  }
  *out = rv; return R_OK;
}

/* ---------- std.builtin access / @typeInfo ---------- */
static Type *bt_type(const char *path);
Type *bt_type_pub(const char *path) { return bt_type(path); }
CVal cv_null_pub(void) { return cv_null(); }
static Type *bt_type(const char *path) {
  Container *c = import_file(std_builtin_file);
  char buf[128]; snprintf(buf, sizeof buf, "%s", path); char *sv; Type *t = NULL;
  for (char *p = strtok_r(buf, ".", &sv); p; p = strtok_r(NULL, ".", &sv)) {
    Decl *d = find_decl(c, p); if (!d) die("std.builtin.%s not found", path);
    resolve_decl(d); if (d->cv.k != CV_TYPE) die("std.builtin.%s is not a type", path);
    t = d->cv.t; c = t->ct;
  }
  return t;
}
static Type *ftype(Type *st, const char *name) { int i = field_index(st, name); if (i < 0) die("no field %s in %s", name, tname(st)); return field_at(st, i)->t; }
static void setf(CVal *a, const char *name, CVal v) { int i = field_index(a->t, name); if (i < 0) die("no field %s in %s", name, tname(a->t)); *a->el[i] = ccoerce(v, field_at(a->t, i)->t); }
static CVal mk_struct(Type *t) { CVal a = agg_new(t); for (int i = 0; i < a.n; i++) *a.el[i] = default_of(t, field_at(t, i)); return a; }
static CVal slice_val(Type *st, CVal *items, int n) {
  Type *et = st->elem; CVal arr = agg_new(array_of(et, n, 0, 0));
  for (int i = 0; i < n; i++) *arr.el[i] = ccoerce(items[i], et);
  CVal r = {0}; r.k = CV_SLICE; r.base = box(arr); r.idx = 0; r.slen = n; r.t = st; return r;
}
static CVal enum_lit_val(Type *et, const char *name) { int64_t v; if (!enum_val(et, name, &v)) die("no field %s in %s", name, tname(et)); return cv_int(v, et); }
static CVal zstr(const char *s) { return cv_str(s, (int)strlen(s)); }
static CVal ptr_to_val(CVal v) { CVal p = {0}; p.k = CV_PTR; p.base = box(v); p.idx = -1; p.t = ptr_to(cv_typeof(&v), 1); return p; }
static CVal decls_val(Type *st, Container *c) {
  Type *dt = ftype(st, "decls"); Vec items = {0};
  if (c) for (int i = 0; i < c->decls.n; i++) {
    Decl *d = c->decls.a[i]; if (!(d->node->flags & F_PUB)) continue;
    CVal *e = xalloc(sizeof *e); *e = mk_struct(dt->elem); setf(e, "name", zstr(d->name)); vpush(&items, e);
  }
  CVal *arr = xalloc(sizeof(CVal) * (items.n + 1)); for (int i = 0; i < items.n; i++) arr[i] = *(CVal *)items.a[i];
  return slice_val(dt, arr, items.n);
}
static CVal type_info(Type *T) {
  Type *TI = bt_type("Type"); const char *tag = NULL; CVal pay = cv_void();
  switch (T->k) {
  case TY_TYPE: tag = "type"; break; case TY_VOID: tag = "void"; break; case TY_BOOL: tag = "bool"; break;
  case TY_NORET: tag = "noreturn"; break; case TY_CINT: tag = "comptime_int"; break; case TY_CFLOAT: tag = "comptime_float"; break;
  case TY_FLOAT: tag = "float"; pay = mk_struct(bt_type("Type.Float")); setf(&pay, "bits", cv_int(T->bits, t_u16)); break;
  case TY_NULL: tag = "null"; break; case TY_UNDEF: tag = "undefined"; break; case TY_ENUMLIT: tag = "enum_literal"; break;
  case TY_INT: {
    tag = "int"; Type *it = bt_type("Type.Int"); pay = mk_struct(it);
    setf(&pay, "signedness", enum_lit_val(bt_type("Signedness"), T->sign ? "signed" : "unsigned"));
    setf(&pay, "bits", cv_int(T->bits, t_u16)); break;
  }
  case TY_PTR: case TY_MPTR: case TY_SLICE: {
    tag = "pointer"; Type *pt = bt_type("Type.Pointer"); pay = mk_struct(pt);
    setf(&pay, "size", enum_lit_val(bt_type("Type.Pointer.Size"), T->k == TY_PTR ? "one" : T->k == TY_MPTR ? "many" : "slice"));
    setf(&pay, "is_const", cv_bool(T->isconst)); setf(&pay, "is_volatile", cv_bool(0));
    setf(&pay, "alignment", cv_null()); setf(&pay, "address_space", enum_lit_val(bt_type("AddressSpace"), "generic"));
    setf(&pay, "child", cv_ty(T->elem)); setf(&pay, "is_allowzero", cv_bool(0));
    setf(&pay, "sentinel_ptr", T->hassent ? ptr_to_val(cv_int(T->sent, T->elem)) : cv_null()); break;
  }
  case TY_ARRAY:
    if (is_vec(T)) { tag = "vector"; pay = mk_struct(bt_type("Type.Vector")); setf(&pay, "len", cv_int(T->len, t_cint)); setf(&pay, "child", cv_ty(T->elem)); break; }
    tag = "array"; pay = mk_struct(bt_type("Type.Array"));
    setf(&pay, "len", cv_int(T->len, t_cint)); setf(&pay, "child", cv_ty(T->elem));
    setf(&pay, "sentinel_ptr", T->hassent ? ptr_to_val(cv_int(T->sent, T->elem)) : cv_null()); break;
  case TY_STRUCT: case TY_TUPLE: {
    tag = "struct"; Type *st = bt_type("Type.Struct"); pay = mk_struct(st); layout(T->ct);
    setf(&pay, "layout", enum_lit_val(bt_type("Type.ContainerLayout"), T->ct->packed ? "packed" : T->ct->layout_kind == 1 ? "extern" : "auto"));
    setf(&pay, "backing_integer", T->ct->packed ? cv_ty(int_type(T->ct->packed, 0)) : cv_null());
    Type *ft = ftype(st, "fields"); int n = T->ct->fields.n; CVal *fs = xalloc(sizeof(CVal) * (n + 1));
    for (int i = 0; i < n; i++) {
      Field *f = T->ct->fields.a[i]; fs[i] = mk_struct(ft->elem);
      setf(&fs[i], "name", zstr(f->name)); setf(&fs[i], "type", cv_ty(f->t));
      CVal dv = (f->def || f->defcv) ? default_of(T, f) : cv_undef(NULL);
      setf(&fs[i], "default_value_ptr", dv.k != CV_UNDEF ? ptr_to_val(dv) : cv_null());
      setf(&fs[i], "is_comptime", cv_bool((type_is_ctonly(f->t) && T->ct->is_tuple) || f->is_ct)); setf(&fs[i], "alignment", cv_null());
    }
    setf(&pay, "fields", slice_val(ft, fs, n)); setf(&pay, "decls", decls_val(st, T->ct)); setf(&pay, "is_tuple", cv_bool(T->ct->is_tuple)); break;
  }
  case TY_ENUM: {
    tag = "enum"; Type *st = bt_type("Type.Enum"); pay = mk_struct(st); layout(T->ct);
    setf(&pay, "tag_type", cv_ty(T->ct->tag));
    Type *ft = ftype(st, "fields"); int n = T->ct->fields.n; CVal *fs = xalloc(sizeof(CVal) * (n + 1));
    for (int i = 0; i < n; i++) { Field *f = T->ct->fields.a[i]; fs[i] = mk_struct(ft->elem); setf(&fs[i], "name", zstr(f->name)); setf(&fs[i], "value", cv_int(f->val, t_cint)); }
    setf(&pay, "fields", slice_val(ft, fs, n)); setf(&pay, "decls", decls_val(st, T->ct)); setf(&pay, "is_exhaustive", cv_bool(!T->ct->nonexh)); break;
  }
  case TY_UNION: {
    tag = "union"; Type *st = bt_type("Type.Union"); pay = mk_struct(st); layout(T->ct);
    setf(&pay, "layout", enum_lit_val(bt_type("Type.ContainerLayout"), T->ct->layout_kind == 1 ? "extern" : T->ct->layout_kind == 2 ? "packed" : "auto"));
    setf(&pay, "tag_type", T->ct->tagged ? cv_ty(T->ct->tag) : cv_null());
    Type *ft = ftype(st, "fields"); int n = T->ct->fields.n; CVal *fs = xalloc(sizeof(CVal) * (n + 1));
    for (int i = 0; i < n; i++) { Field *f = T->ct->fields.a[i]; fs[i] = mk_struct(ft->elem); setf(&fs[i], "name", zstr(f->name)); setf(&fs[i], "type", cv_ty(f->t)); setf(&fs[i], "alignment", cv_null()); }
    setf(&pay, "fields", slice_val(ft, fs, n)); setf(&pay, "decls", decls_val(st, T->ct)); break;
  }
  case TY_OPT: tag = "optional"; pay = mk_struct(bt_type("Type.Optional")); setf(&pay, "child", cv_ty(T->elem)); break;
  case TY_ERRU: tag = "error_union"; pay = mk_struct(bt_type("Type.ErrorUnion")); setf(&pay, "error_set", cv_ty(t_errset)); setf(&pay, "payload", cv_ty(T->elem)); break;
  case TY_ERRSET: tag = "error_set"; pay = cv_null(); break;
  case TY_OPAQUE: tag = "opaque"; { Type *st = bt_type("Type.Opaque"); pay = mk_struct(st); setf(&pay, "decls", decls_val(st, T->ct)); } break;
  case TY_FN: {
    tag = "fn"; Type *st = bt_type("Type.Fn"); pay = mk_struct(st);
    setf(&pay, "calling_convention", enum_lit_val(bt_type("CallingConvention"), "auto"));
    setf(&pay, "is_generic", cv_bool(0)); setf(&pay, "is_var_args", cv_bool(T->varargs));
    setf(&pay, "return_type", T->ret ? cv_ty(T->ret) : cv_null());
    Type *ft = ftype(st, "params"); int n = T->params.n; CVal *ps = xalloc(sizeof(CVal) * (n + 1));
    for (int i = 0; i < n; i++) { ps[i] = mk_struct(ft->elem); setf(&ps[i], "is_generic", cv_bool(0)); setf(&ps[i], "is_noalias", cv_bool(0)); setf(&ps[i], "type", cv_ty(T->params.a[i])); }
    setf(&pay, "params", slice_val(ft, ps, n)); break;
  }
  case TY_ANYTYPE: { /* type of a generic function */
    tag = "fn"; Type *st = bt_type("Type.Fn"); pay = mk_struct(st);
    setf(&pay, "calling_convention", enum_lit_val(bt_type("CallingConvention"), "auto"));
    setf(&pay, "is_generic", cv_bool(1)); setf(&pay, "is_var_args", cv_bool(0)); setf(&pay, "return_type", cv_null());
    Type *ft = ftype(st, "params"); setf(&pay, "params", slice_val(ft, NULL, 0)); break;
  }
  default: die("@typeInfo: unsupported type %s (kind %d)", tname(T), T->k);
  }
  return mk_union(TI, tag, pay);
}

/* ---------- builtins ---------- */
char *cv_cstr(CVal *v, int *lenp) {
  if (v->k == CV_STR) { if (lenp) *lenp = v->slen; return xstrndup(v->s, v->slen); }
  int64_t n; if (!cv_len(v, &n)) { Type *t = cv_typeof(v); if (v->k == CV_PTR && t->k == TY_PTR && t->elem->k == TY_ARRAY) n = t->elem->len; else return NULL; }
  char *r = xalloc(n + 1); for (int64_t i = 0; i < n; i++) r[i] = (char)cv_elem(v, i).i;
  if (lenp) *lenp = (int)n; return r;
}
static CVal seq_at(CVal *v, int64_t i) {
  /* element i of a sequence, where @splat values (and pointers to them) repeat */
  CVal *x = v;
  if (x->k == CV_PTR && x->base && x->idx < 0 && x->base->k == CV_AGG && x->base->t == t_splat) x = x->base;
  if (x->k == CV_AGG && x->t == t_splat) return *x->el[0];
  return cv_elem(v, i);
}
static int agg_get(CVal *a, const char *name, CVal *out) {
  if (a->k != CV_AGG || !is_struct_like(a->t)) return 0;
  int fi = field_index(a->t, name); if (fi < 0) return 0; *out = *a->el[fi]; return 1;
}
int bits_of(Type *t) {
  if (t->k == TY_INT || t->k == TY_FLOAT) return t->bits; if (t->k == TY_BOOL) return 1;
  if (t->k == TY_ENUM) { layout(t->ct); return t->ct->tag->bits; }
  if (is_packed(t)) { layout(t->ct); return t->ct->packed; }
  if (t->k == TY_ARRAY && is_vec(t)) return (int)(bits_of(t->elem) * t->len);
  return tsize(t) * 8;
}
static int log2_bits(int b) { int r = 0; while ((1 << r) <= b) r++; return r; }
static i128 umask(int bits) { return bits >= 127 ? ~(i128)0 : (((i128)1 << bits) - 1); }
static int is_packed_union(Type *t) { return t && t->k == TY_UNION && t->ct && t->ct->node && (t->ct->node->flags & F_PACKED); }
static int packed_type(Type *t) { return t && (is_packed(t) || is_packed_union(t) || t->k == TY_INT || t->k == TY_BOOL || t->k == TY_ENUM || t->k == TY_FLOAT); }
/* IEEE bit patterns of comptime floats */
i128 f_to_bits(f128 f, int bits) {
  if (bits == 32) { float x = (float)f; uint32_t u; memcpy(&u, &x, 4); return u; }
  if (bits == 64) { double x = (double)f; uint64_t u; memcpy(&u, &x, 8); return u; }
  if (bits == 128) { i128 u; memcpy(&u, &f, 16); return u; }
  if (bits == 80) { long double x = (long double)f; unsigned char b[16] = {0}; memcpy(b, &x, 10); uint64_t mant; uint16_t se; memcpy(&mant, b, 8); memcpy(&se, b + 8, 2); return ((i128)se << 64) | mant; }
  /* f16 */
  long double fl = (long double)f; int sg = signbit(fl) ? 1 : 0; long double a = fabsl(fl); uint16_t r;
  if (a != a) r = 0x7e00; else if (isinf(a)) r = 0x7c00;
  else if (a == 0) r = 0;
  else { int e; frexpl(a, &e); e -= 1; /* a = m * 2^e, 1 <= m < 2 */
    if (e < -14) r = (uint16_t)nearbyintl(a * ldexpl(1, 24));
    else { long double m = a * ldexpl(1, -e); int fr = (int)nearbyintl((m - 1) * 1024); if (fr == 1024) { fr = 0; e++; } r = e > 15 ? 0x7c00 : (uint16_t)(((e + 15) << 10) | fr); } }
  return (i128)(r | (sg << 15));
}
f128 bits_to_f(i128 v, int bits) {
  if (bits == 32) { uint32_t u = (uint32_t)v; float x; memcpy(&x, &u, 4); return x; }
  if (bits == 64) { uint64_t u = (uint64_t)v; double x; memcpy(&x, &u, 8); return x; }
  if (bits == 128) { f128 x; memcpy(&x, &v, 16); return x; }
  if (bits == 80) {
    uint64_t mant = (uint64_t)v; uint16_t se = (uint16_t)(v >> 64);
    unsigned char b[16] = {0}; memcpy(b, &mant, 8); memcpy(b + 8, &se, 2); long double f; memcpy(&f, b, sizeof f); return (f128)f;
  }
  uint16_t h = (uint16_t)v; int sg = h >> 15, e = (h >> 10) & 31, fr = h & 1023; long double r;
  if (e == 31) r = fr ? NAN : INFINITY; else if (e == 0) r = ldexpl(fr, -24); else r = ldexpl(fr + 1024, e - 25);
  return (f128)(sg ? -r : r);
}
/* pack/unpack packed structs to/from integers (bitcast) */
static i128 pack_val(CVal *v) {
  if (v->k == CV_AGG && is_packed(v->t)) {
    i128 r = 0;
    for (int i = 0; i < v->n; i++) { Field *f = field_at(v->t, i); r |= (pack_val(v->el[i]) & umask(bits_of(f->t))) << f->bitoff; }
    return r;
  }
  if (v->k == CV_AGG && is_packed_union(v->t)) { Field *f = field_at(v->t, (int)v->i); return pack_val(v->el[0]) & umask(bits_of(f->t)); }
  if (v->k == CV_BOOL || v->k == CV_INT) return v->i;
  if (v->k == CV_FLOAT) return f_to_bits(v->f, v->t && v->t->k == TY_FLOAT ? v->t->bits : 64);
  return 0;
}
static CVal unpack_val(i128 x, Type *t) {
  if (is_packed_union(t)) { CVal a = agg_new(t); Field *f = field_at(t, 0); a.i = 0; *a.el[0] = unpack_val(x & umask(bits_of(f->t)), f->t); return a; }
  if (is_packed(t)) {
    CVal a = agg_new(t);
    for (int i = 0; i < a.n; i++) { Field *f = field_at(t, i); *a.el[i] = unpack_val((x >> f->bitoff) & umask(bits_of(f->t)), f->t); }
    return a;
  }
  if (t->k == TY_BOOL) return cv_bool((int)(x & 1));
  if (t->k == TY_FLOAT) return cv_float(bits_to_f(x & umask(t->bits), t->bits), t);
  return cv_int(wrap_int(x, t->k == TY_ENUM ? t->ct->tag : t), t);
}
static Type *peer_int(CVal *a, CVal *b) { Type *t = cv_typeof(a); if (t->k == TY_CINT) t = cv_typeof(b); return t; }
static CVal ovf_tuple(i128 r, Type *t) {
  Vec names = {0}, types = {0}; vpush(&names, "0"); vpush(&names, "1"); vpush(&types, t); vpush(&types, t_u1);
  Type *tt = mk_anon_struct(&names, &types, 1); CVal a = agg_new(tt);
  i128 w = wrap_int(r, t); *a.el[0] = cv_int(w, t); *a.el[1] = cv_int(w != r, t_u1); return a;
}
static Container *mk_container(int k, const char *name) {
  Container *c = xalloc(sizeof *c); c->name = (char *)name;
  Type *t = xalloc(sizeof *t); t->k = k; t->ct = c; t->size = -1; c->type = t; return c;
}
static int ev_builtin(Node *n, Scope *s, CVal *out) {
  const char *b0 = n->s; Type *rt = brt; brt = NULL;
  int na = n->list.n; Node *x = na > 0 ? n->list.a[0] : NULL, *y = na > 1 ? n->list.a[1] : NULL, *z = na > 2 ? n->list.a[2] : NULL;
  CVal a, b, c;
#define B(nm) (!strcmp(b0, nm))
#define TY(node, var) do { CVal tv_; ct_force++; int r_ = ev(node, s, &tv_); ct_force--; if (r_ != R_OK) return r_; if (tv_.k != CV_TYPE) return R_FAIL; var = tv_.t; } while (0)
  Type *T;
  Type *urt = unwrap_rt(rt);
  if (B("This")) { *out = cv_ty(this_container(s)->type); return R_OK; }
  if (B("import")) { EV(x, s, &a); if (a.k != CV_STR) return R_FAIL;
    if (a.slen > 4 && !memcmp(a.s + a.slen - 4, ".zon", 4)) { /* ZON: evaluate the file's expression with the result type */
      static Vec zp, zn; const char *f = n->tok->file, *sl = strrchr(f, '/');
      char *path = fmt("%s/%.*s", sl ? xstrndup(f, sl - f) : ".", a.slen, a.s); Node *e = NULL;
      for (int i = 0; i < zp.n; i++) if (!strcmp(zp.a[i], path)) e = zn.a[i];
      if (!e) { e = parse_zon(path); vpush(&zp, path); vpush(&zn, e); }
      ct_force++; int r = ev_rt(e, s, urt, out); ct_force--; if (r == R_OK && urt) *out = ccoerce(*out, urt); return r; }
    *out = cv_ty(do_import(n, xstrndup(a.s, a.slen))->type); return R_OK; }
  if (B("embedFile")) {
    EV(x, s, &a); const char *f = n->tok->file; const char *sl = strrchr(f, '/');
    char *dir = sl ? xstrndup(f, sl - f) : "."; long len; char *d = read_file(fmt("%s/%.*s", dir, a.slen, a.s), &len);
    if (!d) die("@embedFile: cannot read %.*s", a.slen, a.s);
    *out = cv_str(d, (int)len); return R_OK;
  }
  if (B("TypeOf")) {
    int sf = ct_force; ct_force = 0; int sxs = xs; Node *sfn = fail_node;
    Type *res = NULL;
    for (int i = 0; i < na; i++) {
      CVal v; int r = ev(n->list.a[i], s, &v); xs = sxs;
      Type *t;
      if (r == R_OK && v.k == CV_FN && !v.t && !fn_is_generic(v.fn->node)) {
        Node *f = v.fn->node; Vec ps = {0}; Scope *fs = v.fn->ct->scope;
        for (int j = 0; j < f->list.n; j++) { Node *p = f->list.a[j]; if (p->flags & F_VARARGS) continue; vpush(&ps, eval_type(p->a, fs)); }
        Type *rr = eval_type(f->a, fs); if (f->flags & F_INFERR) rr = erru_of(rr);
        t = fn_type(&ps, rr, !!(f->flags & F_VARARGS));
      } else if (r == R_OK && v.k != CV_UNDEF) t = cv_typeof(&v);
      else { ct_force = sf; t = typeof_hook(n->list.a[i], s); ct_force = 0; }
      if (!res || res->k == TY_CINT || res->k == TY_NULL) { if (res && res->k == TY_NULL && t->k != TY_NULL && t->k != TY_OPT) t = opt_of(t); res = t; }
      else if (t->k == TY_NULL && res->k != TY_OPT) res = opt_of(res);
    }
    ct_force = sf; fail_node = sfn;
    *out = cv_ty(res); return R_OK;
  }
  if (B("sizeOf")) { TY(x, T); *out = cv_int(type_is_ctonly(T) ? 0 : tsize(T), t_cint); return R_OK; }
  if (B("alignOf")) { TY(x, T); *out = cv_int(talign(T), t_cint); return R_OK; }
  if (B("bitSizeOf")) { TY(x, T); *out = cv_int(bits_of(T), t_cint); return R_OK; }
  if (B("offsetOf") || B("bitOffsetOf")) {
    TY(x, T); EV(y, s, &b); Field *f = find_field(T->ct, cv_cstr(&b, NULL)); if (!f) return R_FAIL;
    *out = cv_int(B("offsetOf") ? (is_packed(T) ? f->bitoff / 8 : f->off) : (is_packed(T) ? f->bitoff : f->off * 8), t_cint); return R_OK;
  }
  if (B("FieldType")) { TY(x, T); EV(y, s, &b); Field *f = find_field(T->ct, cv_cstr(&b, NULL)); if (!f) die("@FieldType: no field"); *out = cv_ty(f->t); return R_OK; }
  if (B("hasDecl")) { TY(x, T); EV(y, s, &b); char *nm = cv_cstr(&b, NULL); *out = cv_bool(T->ct && find_decl(T->ct, nm) != NULL); return R_OK; }
  if (B("hasField")) {
    TY(x, T); EV(y, s, &b); char *nm = cv_cstr(&b, NULL);
    if (T->k == TY_PTR) T = T->elem;
    *out = cv_bool(T->ct && T->k != TY_OPAQUE && find_field(T->ct, nm) != NULL); return R_OK;
  }
  if (B("typeName")) { TY(x, T); *out = zstr(tname(T)); return R_OK; }
  if (B("field")) {
    EV(y, s, &b); char *nm = cv_cstr(&b, NULL); if (!nm) return R_FAIL;
    Type *at;
    if (!strcmp(nm, "len") && is_local_array(s, x, &at)) { *out = cv_int(at->len, t_usize); return R_OK; }
    EV(x, s, &a);
    if (ceval_member(a, nm, out)) return R_OK;
    return R_FAIL;
  }
  if (B("as")) { TY(x, T); CVal v; EVR(y, s, T, &v); *out = ccoerce(v, T); return R_OK; }
  if (B("intCast") || B("truncate")) {
    EV(x, s, &a); if (a.k != CV_INT) return R_FAIL;
    if (!urt || (urt->k != TY_INT && urt->k != TY_CINT)) { *out = a; return R_OK; }
    if (B("intCast") && urt->k == TY_INT) {
      i128 lo = urt->sign ? -((i128)1 << (urt->bits - 1)) : 0, hi = urt->sign ? ((i128)1 << (urt->bits - 1)) - 1 : umask(urt->bits);
      if (urt->bits < 127 && (a.i < lo || a.i > hi) && ct_force) die("%s:%d: @intCast: value %lld does not fit in %s", n->tok->file, n->tok->line, (long long)a.i, tname(urt));
    }
    *out = cv_int(wrap_int(a.i, urt), urt); return R_OK;
  }
  if (B("bitCast")) {
    EV(x, s, &a);
    if (!urt) return R_FAIL;
    if (urt->ct && (urt->k == TY_STRUCT || urt->k == TY_UNION)) layout(urt->ct);
    if (a.k == CV_UNDEF) { *out = cv_undef(urt); return R_OK; }
    Type *ft = cv_typeof(&a); if (ft && ft->ct && (ft->k == TY_STRUCT || ft->k == TY_UNION)) layout(ft->ct);
    if (packed_type(urt) && (packed_type(ft) || a.k == CV_INT || a.k == CV_FLOAT)) {
      i128 v = pack_val(&a); if (ft->k == TY_INT || ft->k == TY_ENUM || ft->k == TY_FLOAT || is_packed(ft)) v &= umask(bits_of(ft));
      *out = unpack_val(v, urt); return R_OK;
    }
    if (urt->k == TY_ARRAY && ft->k == TY_ARRAY && urt->len == ft->len) { *out = ccoerce(a, urt); return R_OK; }
    if (urt->k == TY_ARRAY && (ft->k == TY_INT) && urt->elem->k == TY_INT) {
      CVal r = agg_new(urt); int eb = urt->elem->bits;
      for (int i = 0; i < r.n; i++) *r.el[i] = cv_int(wrap_int((a.i >> (eb * i)) & umask(eb), urt->elem), urt->elem);
      *out = r; return R_OK;
    }
    if (urt->k == TY_INT && ft->k == TY_ARRAY && ft->elem->k == TY_INT && a.k == CV_AGG) {
      i128 v = 0; int eb = ft->elem->bits;
      for (int i = 0; i < a.n; i++) v |= (a.el[i]->i & umask(eb)) << (eb * i);
      *out = cv_int(wrap_int(v, urt), urt); return R_OK;
    }
    return R_FAIL;
  }
  if (B("enumFromInt")) {
    EV(x, s, &a); if (a.k != CV_INT || !urt || urt->k != TY_ENUM) return R_FAIL;
    *out = cv_int(a.i, urt); return R_OK;
  }
  if (B("intFromEnum")) {
    EV(x, s, &a);
    if (a.k == CV_AGG && a.t->k == TY_UNION && a.t->ct->tagged) { Field *f = field_at(a.t, (int)a.i); *out = cv_int(f->val, a.t->ct->tag->ct->tag); return R_OK; }
    if (a.k != CV_INT) return R_FAIL;
    Type *t = cv_typeof(&a); *out = cv_int(a.i, t->k == TY_ENUM ? (layout(t->ct), t->ct->tag) : t); return R_OK;
  }
  if (B("intFromBool")) { EV(x, s, &a); if (a.k != CV_BOOL) return R_FAIL; *out = cv_int(a.i, t_u1); return R_OK; }
  if (B("min") || B("max")) {
    EV(x, s, &a);
    for (int i = 1; i < na; i++) {
      EV(n->list.a[i], s, &b);
      if (a.k == CV_AGG && b.k == CV_AGG) {
        CVal r = agg_new(a.t); for (int j = 0; j < a.n; j++) { CVal p = *a.el[j], q = *b.el[j]; *r.el[j] = (B("min") ? p.i < q.i : p.i > q.i) ? p : q; } a = r; continue;
      }
      if ((a.k == CV_FLOAT || b.k == CV_FLOAT) && (a.k == CV_FLOAT || a.k == CV_INT) && (b.k == CV_FLOAT || b.k == CV_INT)) {
        Type *ta = cv_typeof(&a), *tb = cv_typeof(&b); Type *t = ta->k == TY_FLOAT ? ta : tb->k == TY_FLOAT ? tb : t_cfloat;
        f128 p = a.k == CV_FLOAT ? a.f : (f128)a.i, q = b.k == CV_FLOAT ? b.f : (f128)b.i;
        a = cv_float(p != p ? q : q != q ? p : B("min") ? (p < q ? p : q) : (p > q ? p : q), t); continue;
      }
      if (a.k != CV_INT || b.k != CV_INT) return R_FAIL;
      Type *t = peer_int(&a, &b); CVal m = (B("min") ? a.i <= b.i : a.i >= b.i) ? a : b; a = cv_int(m.i, t);
    }
    *out = a; return R_OK;
  }
  if (B("compileError")) {
    EV(x, s, &a); int l; char *m = cv_cstr(&a, &l);
    die("%s:%d: error: %s", n->tok->file, n->tok->line, m ? m : "@compileError");
  }
  if (B("compileLog")) {
    fprintf(stderr, "%s:%d: @compileLog:", n->tok->file, n->tok->line);
    for (int i = 0; i < na; i++) { CVal v; if (ev(n->list.a[i], s, &v) == R_OK) fprintf(stderr, " %s", cv_name(&v)); else fprintf(stderr, " (runtime)"); }
    fprintf(stderr, "\n"); *out = cv_void(); return R_OK;
  }
  if (B("panic")) { if (!ct_force) return R_FAIL; EV(x, s, &a); die("%s:%d: panic at comptime: %s", n->tok->file, n->tok->line, cv_cstr(&a, NULL)); }
  if (B("inComptime")) { *out = cv_bool(ct_force > 0); return R_OK; }
  if (B("setEvalBranchQuota") || B("setRuntimeSafety") || B("branchHint") || B("setFloatMode") || B("disableInstrumentation") || B("disableIntrinsics")) { *out = cv_void(); return R_OK; }
  if (B("errorReturnTrace")) { *out = cv_null(); return R_OK; }
  if (B("typeInfo")) { TY(x, T); if (T->tinfo) { *out = *(CVal *)T->tinfo; return R_OK; } *out = type_info(T);
    if (!T->ct || (T->ct->laid && !T->ct->laying)) { CVal *c = xalloc(sizeof *c); *c = *out; T->tinfo = c; } return R_OK; }
  if (B("Int")) {
    CVal sg; EVR(x, s, bt_type("Signedness"), &sg); EV(y, s, &b); if (b.k != CV_INT || sg.k != CV_INT) return R_FAIL;
    int64_t sv; enum_val(bt_type("Signedness"), "signed", &sv);
    *out = cv_ty(int_type((int)b.i, sg.i == sv)); return R_OK;
  }
  if (B("Vector")) { EV(x, s, &a); TY(y, T); if (a.k != CV_INT) return R_FAIL; *out = cv_ty(vec_of(T, (int64_t)a.i)); return R_OK; }
  if (B("EnumLiteral")) { *out = cv_ty(t_enumlit); return R_OK; }
  if (B("Tuple")) {
    EV(x, s, &a); int64_t len; if (!cv_len(&a, &len)) return R_FAIL;
    Vec names = {0}, types = {0};
    for (int64_t i = 0; i < len; i++) { CVal e = cv_elem(&a, i); if (e.k != CV_TYPE) return R_FAIL; vpush(&names, fmt("%d", (int)i)); vpush(&types, e.t); }
    *out = cv_ty(mk_anon_struct(&names, &types, 1)); return R_OK;
  }
  if (B("Pointer")) {
    CVal sz; EVR(x, s, bt_type("Type.Pointer.Size"), &sz); CVal at; EVR(y, s, bt_type("Type.Pointer.Attributes"), &at); TY(z, T);
    CVal sn = cv_null(); if (na > 3) EVR(n->list.a[3], s, opt_of(T), &sn);
    CVal cf; int isc = agg_get(&at, "const", &cf) && cf.i;
    int64_t one, many, slc; Type *st = bt_type("Type.Pointer.Size"); enum_val(st, "one", &one); enum_val(st, "many", &many); enum_val(st, "slice", &slc);
    int hs = sn.k != CV_NULL && sn.k != CV_UNDEF;
    if (sz.i == one) *out = cv_ty(ptr_to(T, isc));
    else if (sz.i == slc) *out = cv_ty(slice_of(T, isc));
    else *out = cv_ty(mptr_to(T, isc, hs, hs ? (int64_t)sn.i : 0));
    return R_OK;
  }
  if (B("Struct") || B("Union")) {
    int isu = B("Union");
    CVal lay; EVR(x, s, bt_type("Type.ContainerLayout"), &lay);
    CVal bk; EV(y, s, &bk);
    CVal names; EV(z, s, &names); CVal types; EV(n->list.a[3], s, &types); CVal attrs; EV(n->list.a[4], s, &attrs);
    int64_t len; if (!cv_len(&names, &len)) return R_FAIL;
    Container *ct = mk_container(isu ? TY_UNION : TY_STRUCT, isu ? "union" : "struct");
    int64_t lk_ext, lk_pk; enum_val(bt_type("Type.ContainerLayout"), "extern", &lk_ext); enum_val(bt_type("Type.ContainerLayout"), "packed", &lk_pk);
    ct->layout_kind = lay.i == lk_ext ? 1 : lay.i == lk_pk ? 2 : 0;
    if (!isu && ct->layout_kind == 2) ct->packed = -1;
    if (isu && bk.k == CV_TYPE) { ct->tagged = 1; ct->tag = bk.t; }
    if (!isu && bk.k == CV_TYPE) ct->packed = bk.t->bits;
    for (int64_t i = 0; i < len; i++) {
      CVal nm = cv_elem(&names, i); CVal ty = seq_at(&types, i); CVal at = seq_at(&attrs, i);
      Field *f = xalloc(sizeof *f); f->name = cv_cstr(&nm, NULL); if (ty.k != CV_TYPE) return R_FAIL; f->t = ty.t;
      CVal dp; if (agg_get(&at, "default_value_ptr", &dp) && dp.k == CV_PTR) { CVal *dc = deref_cell(&dp); if (dc) f->defcv = box(ccoerce(*dc, f->t)); }
      vpush(&ct->fields, f);
    }
    if (isu && ct->tagged) { for (int i = 0; i < ct->fields.n; i++) { Field *f = ct->fields.a[i]; int64_t v; if (enum_val(ct->tag, f->name, &v)) f->val = v; } }
    *out = cv_ty(ct->type); return R_OK;
  }
  if (B("Enum")) {
    TY(x, T); CVal mode; EVR(y, s, bt_type("Type.Enum.Mode"), &mode); CVal names; EV(z, s, &names); CVal vals; EV(n->list.a[3], s, &vals);
    int64_t len; if (!cv_len(&names, &len)) return R_FAIL;
    Container *ct = mk_container(TY_ENUM, "enum"); ct->tag = T;
    int64_t nx; enum_val(bt_type("Type.Enum.Mode"), "nonexhaustive", &nx); ct->nonexh = mode.i == nx;
    for (int64_t i = 0; i < len; i++) {
      CVal nm = cv_elem(&names, i); CVal v = seq_at(&vals, i);
      Field *f = xalloc(sizeof *f); f->name = cv_cstr(&nm, NULL); f->val = (int64_t)v.i; f->t = T; vpush(&ct->fields, f);
    }
    ct->type->size = tsize(T); ct->type->align = talign(T); ct->laid = 1;
    *out = cv_ty(ct->type); return R_OK;
  }
  if (B("splat")) {
    EV(x, s, &a);
    if (urt && urt->k == TY_ARRAY) { CVal r = agg_new(urt); for (int i = 0; i < r.n; i++) *r.el[i] = ccoerce(cv_copy(a), urt->elem); *out = r; return R_OK; }
    *out = mk_splat(a); return R_OK;
  }
  if (B("tagName")) {
    EV(x, s, &a);
    if (a.k == CV_ENUMLIT) { *out = zstr(a.s); return R_OK; }
    if (a.k == CV_AGG && a.t->k == TY_UNION) { *out = zstr(field_at(a.t, (int)a.i)->name); return R_OK; }
    if (a.k != CV_INT) return R_FAIL;
    Type *t = cv_typeof(&a); if (t->k != TY_ENUM) return R_FAIL; layout(t->ct);
    for (int i = 0; i < t->ct->fields.n; i++) { Field *f = t->ct->fields.a[i]; if (f->val == (int64_t)a.i) { *out = zstr(f->name); return R_OK; } }
    die("@tagName: invalid enum value");
  }
  if (B("errorName")) { EV(x, s, &a); if (a.k != CV_ERR) return R_FAIL; *out = zstr(errnames.a[a.i - 1]); return R_OK; }
  if (B("intFromError")) { EV(x, s, &a); if (a.k != CV_ERR) return R_FAIL; *out = cv_int(a.i, t_u16); return R_OK; }
  if (B("errorFromInt")) { EV(x, s, &a); CVal e = {0}; e.k = CV_ERR; e.i = a.i; e.t = t_errset; *out = e; return R_OK; }
  if (B("errorCast")) return ev(x, s, out);
  if (B("unionInit")) { TY(x, T); EV(y, s, &b); char *nm = cv_cstr(&b, NULL); int fi = field_index(T, nm); if (fi < 0) return R_FAIL; CVal v; EVR(z, s, field_at(T, fi)->t, &v); *out = mk_union(T, nm, v); return R_OK; }
  if (B("ptrCast") || B("alignCast") || B("constCast") || B("volatileCast") || B("addrSpaceCast")) {
    CVal v; brt = rt; int r = ev_rt(x, s, NULL, &v); if (r != R_OK) return r;
    if (x->k == N_BUILTIN) { /* nested cast: re-evaluate with the result type */ }
    if (v.k == CV_PTR || v.k == CV_SLICE || v.k == CV_NULL || v.k == CV_FN || v.k == CV_STR) { if (urt && (urt->k == TY_PTR || urt->k == TY_MPTR || urt->k == TY_SLICE || urt->k == TY_FN)) { if (v.k == CV_STR) { CVal p = {0}; p.k = CV_PTR; p.base = box(v); p.idx = 0; p.t = urt; *out = p; return R_OK; } v.t = urt; } *out = v; return R_OK; }
    if (v.k == CV_INT && urt) { v.t = urt; *out = v; return R_OK; }
    return R_FAIL;
  }
  if (B("ptrFromInt")) { EV(x, s, &a); if (a.k != CV_INT || !urt) return R_FAIL; a.t = urt; *out = a; return R_OK; }
  if (B("intFromPtr")) { EV(x, s, &a); if (a.k == CV_INT) { *out = cv_int(a.i, t_usize); return R_OK; } return R_FAIL; }
  if (B("call")) {
    EV(y, s, &b); EV(z, s, &c); int64_t len; if (b.k != CV_FN || !cv_len(&c, &len)) return R_FAIL;
    if (!ct_force && !fn_returns_ctonly(b.fn)) return R_FAIL;
    CVal *args = xalloc(sizeof(CVal) * (len + 1)); for (int64_t i = 0; i < len; i++) args[i] = cv_elem(&c, i);
    return ct_call(b.fn, args, (int)len, out);
  }
  if (B("memcpy") || B("memmove")) {
    if (!ct_force) return R_FAIL;
    EV(x, s, &a); EV(y, s, &b); int64_t len;
    if (!cv_len(&b, &len)) { if (!cv_len(&a, &len)) { Type *t = cv_typeof(&a); if (t->k == TY_PTR && t->elem->k == TY_ARRAY) len = t->elem->len; else return R_FAIL; } }
    CVal *tmp = xalloc(sizeof(CVal) * (len + 1)); for (int64_t i = 0; i < len; i++) tmp[i] = cv_elem(&b, i);
    for (int64_t i = 0; i < len; i++) { CVal *cl = elem_cell(&a, i); if (!cl) return R_FAIL; assign(cl, tmp[i]); }
    *out = cv_void(); return R_OK;
  }
  if (B("memset")) {
    if (!ct_force) return R_FAIL;
    EV(x, s, &a); EV(y, s, &b); int64_t len;
    if (!cv_len(&a, &len)) { Type *t = cv_typeof(&a); if (t->k == TY_PTR && t->elem->k == TY_ARRAY) len = t->elem->len; else return R_FAIL; }
    for (int64_t i = 0; i < len; i++) { CVal *cl = elem_cell(&a, i); if (!cl) return R_FAIL; assign(cl, b); }
    *out = cv_void(); return R_OK;
  }
  if (B("divTrunc") || B("divFloor") || B("divExact") || B("mod") || B("rem") || B("shlExact") || B("shrExact")) {
    EV(x, s, &a); EV(y, s, &b); if (a.k != CV_INT || b.k != CV_INT) return R_FAIL;
    Type *t = peer_int(&a, &b); i128 p = a.i, q = b.i, r;
    if (B("shlExact")) r = p << q; else if (B("shrExact")) r = p >> q;
    else { if (!q) return R_FAIL; r = p / q;
      if (B("divFloor") && (p % q != 0) && ((p < 0) != (q < 0))) r--;
      if (B("mod")) { r = p % q; if (r != 0 && ((r < 0) != (q < 0))) r += q; }
      if (B("rem")) r = p % q; }
    *out = cv_int(wrap_int(r, t), t); return R_OK;
  }
  if (B("addWithOverflow") || B("subWithOverflow") || B("mulWithOverflow") || B("shlWithOverflow")) {
    EV(x, s, &a); EV(y, s, &b); if (a.k != CV_INT || b.k != CV_INT) return R_FAIL;
    Type *t = cv_typeof(&a); if (t->k == TY_CINT) t = cv_typeof(&b);
    i128 r = b0[0] == 'a' ? a.i + b.i : b0[0] == 's' && b0[1] == 'u' ? a.i - b.i : b0[0] == 'm' ? a.i * b.i : (b.i >= 127 ? 0 : a.i << b.i);
    *out = ovf_tuple(r, t); return R_OK;
  }
  if (B("floatFromInt")) { EV(x, s, &a); if (a.k != CV_INT && a.k != CV_FLOAT) return R_FAIL; Type *t = urt && is_float(urt) ? urt : t_cfloat;
    *out = cv_float(fround(a.k == CV_INT ? (f128)a.i : a.f, t), t); return R_OK; }
  if (B("intFromFloat")) { EV(x, s, &a); if (a.k != CV_FLOAT && a.k != CV_INT) return R_FAIL; Type *t = urt && is_int(urt) ? urt : t_cint;
    if (a.k == CV_INT) { *out = cv_int(a.i, t); return R_OK; }
    if (f128_isnan(a.f) || f128_isinf(a.f)) { if (ct_force) die("%s:%d: @intFromFloat of non-finite value", n->tok->file, n->tok->line); return R_FAIL; }
    *out = cv_int(wrap_int((i128)a.f, t), t); return R_OK; }
  if (B("floatCast")) { EV(x, s, &a); if (a.k != CV_FLOAT && a.k != CV_INT) return R_FAIL; Type *t = urt && is_float(urt) ? urt : cv_typeof(&a);
    *out = cv_float(fround(a.k == CV_INT ? (f128)a.i : a.f, t), t); return R_OK; }
  if (B("sqrt") || B("sin") || B("cos") || B("tan") || B("exp") || B("exp2") || B("exp10") || B("log") || B("log2") || B("log10") || B("floor") || B("ceil") || B("trunc") || B("round") || (B("abs") && 0)) {
    EV(x, s, &a); if (a.k == CV_AGG && a.t->k == TY_ARRAY) return R_FAIL; if (a.k != CV_FLOAT) return R_FAIL; f128 f = a.f, r; long double lf = (long double)f;
    if (B("sqrt")) r = f128_sqrt(f); else if (B("sin")) r = sinl(lf); else if (B("cos")) r = cosl(lf); else if (B("tan")) r = tanl(lf);
    else if (B("exp")) r = expl(lf); else if (B("exp2")) r = exp2l(lf); else if (B("exp10")) r = powl(10, lf); else if (B("log")) r = logl(lf);
    else if (B("log2")) r = log2l(lf); else if (B("log10")) r = log10l(lf); else if (B("floor")) r = f128_floor(f); else if (B("ceil")) r = f128_ceil(f);
    else if (B("trunc")) r = f128_trunc(f); else r = f128_round(f);
    Type *t = cv_typeof(&a); *out = cv_float(fround(r, t), t); return R_OK;
  }
  if (B("mulAdd")) { TY(x, T); CVal c3; EVR(y, s, T, &a); EVR(n->list.a[2], s, T, &b); EVR(n->list.a[3], s, T, &c3);
    if (a.k != CV_FLOAT || b.k != CV_FLOAT || c3.k != CV_FLOAT) return R_FAIL; *out = cv_float(fround(a.f * b.f + c3.f, T), T); return R_OK; }
  if (B("abs") && x) { EV(x, s, &a); if (a.k == CV_FLOAT) { *out = cv_float(a.f < 0 || (a.f == 0 && signbit((double)a.f)) ? -a.f : a.f, cv_typeof(&a)); return R_OK; } }
  if (B("abs")) {
    EV(x, s, &a); if (a.k != CV_INT) return R_FAIL; Type *t = cv_typeof(&a);
    Type *ut = t->k == TY_INT && t->sign ? int_type(t->bits, 0) : t; *out = cv_int(a.i < 0 ? -a.i : a.i, ut); return R_OK;
  }
  if (B("clz") || B("ctz") || B("popCount") || B("byteSwap") || B("bitReverse")) {
    EV(x, s, &a);
    if (a.k == CV_AGG) return R_FAIL;
    if (a.k != CV_INT) return R_FAIL; Type *t = cv_typeof(&a); if (t->k != TY_INT) return R_FAIL;
    int bits = t->bits; i128 u = a.i & umask(bits); i128 r = 0;
    if (B("clz")) { r = bits; for (int i = bits - 1; i >= 0; i--) if ((u >> i) & 1) { r = bits - 1 - i; break; } *out = cv_int(r, int_type(log2_bits(bits), 0)); return R_OK; }
    if (B("ctz")) { r = bits; for (int i = 0; i < bits; i++) if ((u >> i) & 1) { r = i; break; } *out = cv_int(r, int_type(log2_bits(bits), 0)); return R_OK; }
    if (B("popCount")) { for (int i = 0; i < bits; i++) r += (u >> i) & 1; *out = cv_int(r, int_type(log2_bits(bits), 0)); return R_OK; }
    if (B("byteSwap")) { for (int i = 0; i < bits / 8; i++) r |= ((u >> (8 * i)) & 0xff) << (8 * (bits / 8 - 1 - i)); }
    else for (int i = 0; i < bits; i++) if ((u >> i) & 1) r |= (i128)1 << (bits - 1 - i);
    *out = cv_int(wrap_int(r, t), t); return R_OK;
  }
  if (B("reduce")) {
    CVal op; EVR(x, s, bt_type("ReduceOp"), &op); EV(y, s, &b); if (b.k != CV_AGG || op.k != CV_INT) return R_FAIL;
    Container *rc = bt_type("ReduceOp")->ct; layout(rc); const char *on = NULL;
    for (int i = 0; i < rc->fields.n; i++) { Field *f = rc->fields.a[i]; if (f->val == (int64_t)op.i) on = f->name; }
    CVal acc = *b.el[0];
    for (int i = 1; i < b.n; i++) {
      CVal e = *b.el[i]; const char *bop = !strcmp(on, "And") ? "&" : !strcmp(on, "Or") ? "|" : !strcmp(on, "Xor") ? "^" : !strcmp(on, "Add") ? "+%" : !strcmp(on, "Mul") ? "*%" : NULL;
      if (bop) { if (acc.k == CV_BOOL) { if (bop[0] == '&') acc.i &= e.i; else if (bop[0] == '|') acc.i |= e.i; else acc.i ^= e.i; } else if (ev_bin(bop, acc, e, &acc) != R_OK) return R_FAIL; }
      else if (!strcmp(on, "Min")) { if (e.i < acc.i) acc = e; } else if (e.i > acc.i) acc = e;
    }
    *out = acc; return R_OK;
  }
  if (B("select")) {
    TY(x, T); CVal pr; EV(y, s, &pr); EV(z, s, &a); EV(n->list.a[3], s, &b);
    if (pr.k != CV_AGG) return R_FAIL; CVal r = agg_new(vec_of(T, pr.n));
    for (int i = 0; i < pr.n; i++) *r.el[i] = pr.el[i]->i ? seq_at(&a, i) : seq_at(&b, i);
    *out = r; return R_OK;
  }
  if (B("shuffle")) {
    TY(x, T); EV(y, s, &a); EV(z, s, &b); CVal mk; EV(n->list.a[3], s, &mk); int64_t ml; if (!cv_len(&mk, &ml)) return R_FAIL;
    CVal r = agg_new(vec_of(T, ml));
    for (int64_t i = 0; i < ml; i++) { CVal m = cv_elem(&mk, i); if (m.k == CV_UNDEF) { *r.el[i] = cv_undef(T); continue; } int64_t k = (int64_t)m.i; *r.el[i] = k >= 0 ? seq_at(&a, k) : seq_at(&b, ~k); }
    *out = r; return R_OK;
  }
  if (B("src")) {
    Type *st = bt_type("SourceLocation"); CVal v = mk_struct(st);
    setf(&v, "module", zstr("root")); setf(&v, "file", zstr(n->tok->file)); setf(&v, "fn_name", zstr("?"));
    setf(&v, "line", cv_int(n->tok->line, t_u32)); setf(&v, "column", cv_int(1, t_u32)); *out = v; return R_OK;
  }
  return R_FAIL;
#undef B
#undef TY
}

/* ---------- public entry points ---------- */
typedef struct { int force, xs; Type *rt; int lrt; Node *fail; } CtSave;
static CtSave ct_enter(int force) { CtSave sv = { ct_force, xs, cur_rt, lrt_n, fail_node }; ct_force = force; fail_node = NULL; return sv; }
static Node *last_fail;
static void ct_leave(CtSave sv) { if (fail_node) last_fail = fail_node; ct_force = sv.force; xs = sv.xs; cur_rt = sv.rt; lrt_n = sv.lrt; fail_node = sv.fail; }
int ceval(Node *n, Scope *s, CVal *out) {
  CtSave sv = ct_enter(0); memset(out, 0, sizeof *out);
  int r = ev(n, s, out); ct_leave(sv); return r == R_OK;
}
int ceval_force(Node *n, Scope *s, CVal *out) {
  CtSave sv = ct_enter(1); memset(out, 0, sizeof *out);
  int r = ev(n, s, out); ct_leave(sv); return r == R_OK;
}
int ceval_rt(Node *n, Scope *s, Type *rt, CVal *out) {
  CtSave sv = ct_enter(1); memset(out, 0, sizeof *out);
  int r = ev_rt(n, s, rt, out); ct_leave(sv); return r == R_OK;
}
int ceval_ret(Node *n, Scope *s, Type *rt, Type *fnrt, CVal *out, int *returned) {
  CtSave sv = ct_enter(1); memset(out, 0, sizeof *out); Type *srt = cur_rt; cur_rt = fnrt;
  int r = ev_rt(n, s, rt, out);
  if (r == R_CF && xs == X_RET) { xs = X_NONE; *out = fnrt ? ccoerce(xval, fnrt) : xval; *returned = 1; r = R_OK; }
  cur_rt = srt; ct_leave(sv); return r == R_OK;
}
int ct_try_store(Node *dst, Node *n, Scope *s) {
  Node *r = dst;
  while (r && (r->k == N_FIELD || r->k == N_INDEX || r->k == N_UNWRAP || r->k == N_DEREF || r->k == N_SLICE || r->k == N_UN)) r = r->a;
  if (!r || r->k != N_IDENT) return 0;
  Sym *y = lookup_local(s, r->s); if (!y || y->k != S_CVAL || !y->mut) return 0;
  CtSave sv = ct_enter(1); CVal o; int rr = ev(n, s, &o); ct_leave(sv);
  if (rr != R_OK) die("%s:%d: cannot evaluate store to comptime variable '%s' (at %s)", n->tok->file, n->tok->line, r->s, ct_fail_loc());
  return 1;
}
int ct_try_assign(Node *n, Scope *s) {
  Node *r = n->a;
  while (r->k == N_FIELD || r->k == N_INDEX || r->k == N_UNWRAP || (r->k == N_DEREF)) r = r->a;
  if (r->k != N_IDENT) return 0;
  Sym *y = lookup_local(s, r->s); if (!y || y->k != S_CVAL || !y->mut) return 0;
  CtSave sv = ct_enter(1); CVal o; int rr = ev(n, s, &o); ct_leave(sv);
  if (rr != R_OK) die("%s:%d: cannot evaluate assignment to comptime variable '%s'", n->tok->file, n->tok->line, r->s);
  return 1;
}
Type *eval_type(Node *n, Scope *s) {
  CVal v; CtSave sv = ct_enter(1); int r = ev(n, s, &v); Node *fn = fail_node; ct_leave(sv);
  if (r != R_OK) {
    if (fn && fn->tok) die("%s:%d: expected comptime type expression (cannot evaluate expression at %s:%d)", n->tok->file, n->tok->line, fn->tok->file, fn->tok->line);
    die("%s:%d: expected comptime type expression", n->tok->file, n->tok->line);
  }
  if (v.k == CV_TYPE) return v.t;
  if (v.k == CV_NULL) return t_null;
  die("%s:%d: expected a type", n->tok->file, n->tok->line);
}
Type *call_type_fn(Decl *d, Vec *argnodes, Scope *s) {
  Node cn = {0}; cn.k = N_CALL; Node fnn = {0}; cn.a = &fnn; cn.tok = d->node->tok; cn.list = *argnodes;
  CtSave sv = ct_enter(1); CVal r; CVal nv = {0};
  int rr = ev_call_fn(&cn, s, d->cv, 0, nv, NULL, &r); ct_leave(sv);
  if (rr != R_OK || r.k != CV_TYPE) die("%s:%d: cannot evaluate type function %s at comptime", d->node->tok->file, d->node->tok->line, d->name);
  return r.t;
}
const char *ct_fail_loc(void) { Node *f = last_fail; return f && f->tok ? fmt("%s:%d (node kind %d)", f->tok->file, f->tok->line, f->k) : "?"; }
/* helpers exported to the code generator */
i128 cv_pack(CVal *v) { return pack_val(v); }
int cv_binop(const char *op, CVal a, CVal b, CVal *out) { return ev_bin(op, a, b, out) == R_OK; }
int cv_match(CVal *v, CVal *item) {
  CVal it = *item;
  if (v->k == CV_AGG && v->t->k == TY_UNION) return union_tag_is(v, &it);
  CVal e; if (it.k == CV_ENUMLIT && v->k == CV_INT) it = ccoerce(it, cv_typeof(v));
  if (ev_bin("==", *v, it, &e) != R_OK) return 0;
  return (int)e.i;
}
int ceval_ex(Node *n, Scope *s, Type *rt, CVal *out) {
  CtSave sv = ct_enter(0); memset(out, 0, sizeof *out);
  int r = ev_rt(n, s, rt, out); ct_leave(sv); return r == R_OK;
}
