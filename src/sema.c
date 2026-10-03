#include "zb.h"

Type *t_void, *t_bool, *t_noret, *t_cint, *t_type, *t_null, *t_undef, *t_enumlit, *t_u8, *t_u16,
  *t_u32, *t_u64, *t_i32, *t_i64, *t_usize, *t_isize, *t_errset, *t_anytype, *t_u1,
  *t_cfloat, *t_f16, *t_f32, *t_f64, *t_f80, *t_f128;
static Vec types;
const char *root_dir;
Vec errnames;
Type *(*typeof_hook)(Node *n, Scope *s);

static Type *mkt(int k) { Type *t = xalloc(sizeof *t); t->k = k; t->size = -1; vpush(&types, t); return t; }
void types_init(void) {
  t_void = mkt(TY_VOID); t_bool = mkt(TY_BOOL); t_noret = mkt(TY_NORET); t_cint = mkt(TY_CINT);
  t_type = mkt(TY_TYPE); t_null = mkt(TY_NULL); t_undef = mkt(TY_UNDEF); t_enumlit = mkt(TY_ENUMLIT);
  t_errset = mkt(TY_ERRSET); t_anytype = mkt(TY_ANYTYPE);
  t_u8 = int_type(8, 0); t_u16 = int_type(16, 0); t_u32 = int_type(32, 0); t_u64 = int_type(64, 0);
  t_i32 = int_type(32, 1); t_i64 = int_type(64, 1); t_u1 = int_type(1, 0);
  t_usize = t_u64; t_isize = t_i64;
  t_cfloat = mkt(TY_CFLOAT); t_f16 = float_type(16); t_f32 = float_type(32); t_f64 = float_type(64); t_f80 = float_type(80); t_f128 = float_type(128);
}
Type *float_type(int bits) {
  for (int i = 0; i < types.n; i++) { Type *t = types.a[i]; if (t->k == TY_FLOAT && t->bits == bits) return t; }
  Type *t = mkt(TY_FLOAT); t->bits = bits; t->sign = 1; return t;
}
Type *int_type(int bits, int sign) {
  for (int i = 0; i < types.n; i++) { Type *t = types.a[i]; if (t->k == TY_INT && t->bits == bits && t->sign == sign) return t; }
  Type *t = mkt(TY_INT); t->bits = bits; t->sign = sign; return t;
}
static Type *derived(int k, Type *e, int c, int64_t len, int hs, int64_t sent) {
  for (int i = 0; i < types.n; i++) {
    Type *t = types.a[i];
    if (t->k == k && t->elem == e && t->isconst == c && t->len == len && t->hassent == hs && t->sent == sent) return t;
  }
  Type *t = mkt(k); t->elem = e; t->isconst = c; t->len = len; t->hassent = hs; t->sent = sent; return t;
}
Type *ptr_to(Type *t, int c) { return derived(TY_PTR, t, c, 0, 0, 0); }
Type *bitptr_to(Type *t, int c, int hbytes, int bitoff) { return derived(TY_PTR, t, c, hbytes, 0, bitoff); } /* *align(1:bitoff:hbytes) T */
Type *mptr_to(Type *t, int c, int hs, int64_t s) { return derived(TY_MPTR, t, c, 0, hs, s); }
Type *slice_of(Type *t, int c) { return derived(TY_SLICE, t, c, 0, 0, 0); }
Type *slice_of_s(Type *t, int c, int hs, int64_t sent) { return derived(TY_SLICE, t, c, 0, hs, hs ? sent : 0); }
Type *array_of(Type *t, int64_t n, int hs, int64_t s) { return derived(TY_ARRAY, t, 0, n, hs, s); }
Type *vec_of(Type *t, int64_t n) { return derived(TY_ARRAY, t, 2, n, 0, 0); }
Type *opt_of(Type *t) { return derived(TY_OPT, t, 0, 0, 0, 0); }
Type *erru_of(Type *t) { return erru_of2(t, NULL); }
Type *erru_of2(Type *t, Type *es) {
  if (es == t_errset) es = NULL;
  for (int i = 0; i < types.n; i++) { Type *x = types.a[i]; if (x->k == TY_ERRU && x->elem == t && x->ret == es) return x; }
  Type *n = mkt(TY_ERRU); n->elem = t; n->ret = es; return n;
}
Type *eset_of(Type *eu) { return eu && eu->k == TY_ERRU && eu->ret ? eu->ret : t_errset; }
static Type *errset_new(void) { Type *t = mkt(TY_ERRSET); Container *c = xalloc(sizeof *c); c->type = t; c->laid = 1; t->ct = c; return t; }
static int eset_has(Container *c, const char *nm) { for (int i = 0; i < c->fields.n; i++) if (!strcmp(((Field *)c->fields.a[i])->name, nm)) return 1; return 0; }
static void eset_push(Container *c, char *nm) { if (eset_has(c, nm)) return; Field *f = xalloc(sizeof *f); f->name = nm; f->val = err_id(nm); f->t = c->type; vpush(&c->fields, f); }
Type *errset_named(char **names, int n) {
  for (int i = 0; i < types.n; i++) { Type *x = types.a[i]; if (x->k != TY_ERRSET || !x->ct || x->ct->infer_d || x->ct->infer_fi) continue;
    Container *c = x->ct; int uniq = 0; for (int j = 0; j < n; j++) { int dup = 0; for (int k = 0; k < j; k++) if (!strcmp(names[j], names[k])) dup = 1; if (!dup) uniq++; }
    if (c->fields.n != uniq) continue; int ok = 1; for (int j = 0; ok && j < n; j++) if (!eset_has(c, names[j])) ok = 0; if (ok) return x; }
  Type *t = errset_new(); for (int j = 0; j < n; j++) eset_push(t->ct, names[j]);
  { char *r = "error{"; for (int i = 0; i < t->ct->fields.n; i++) r = fmt("%s%s%s", r, i ? "," : "", ((Field *)t->ct->fields.a[i])->name); t->ct->name = fmt("%s}", r); } return t;
}
int is_inferred_eset(Type *t) { return t && t->k == TY_ERRSET && t->ct && (t->ct->infer_d || t->ct->infer_fi); }
Type *errset_merge(Type *a, Type *b) {
  if (is_inferred_eset(a)) eset_resolve(a); if (is_inferred_eset(b)) eset_resolve(b);
  if (!a->ct || !b->ct || a->ct->ianyerr || b->ct->ianyerr) return t_errset;
  Vec nm = {0}; for (int i = 0; i < a->ct->fields.n; i++) vpush(&nm, ((Field *)a->ct->fields.a[i])->name); for (int i = 0; i < b->ct->fields.n; i++) vpush(&nm, ((Field *)b->ct->fields.a[i])->name);
  return errset_named((char **)nm.a, nm.n);
}
typedef struct { char *name; Type *set; } IEnt;
Type *errset_infer(void) { return errset_new(); }
Type *decl_iset(Decl *d) { if (!d->iset) { d->iset = errset_infer(); d->iset->ct->infer_d = d; d->iset->ct->name = fmt("@typeInfo(@typeInfo(@TypeOf(%s.%s)).@\"fn\".return_type.?).error_union.error_set", d->ct->name, d->name); } return d->iset; }
void eset_add_name(Type *s, char *name) { Container *c = s->ct; for (int i = 0; i < c->ient.n; i++) { IEnt *e = c->ient.a[i]; if (e->name && !strcmp(e->name, name)) return; } IEnt *e = xalloc(sizeof *e); e->name = name; vpush(&c->ient, e); }
void eset_add_set(Type *s, Type *o) { if (o == s) return; Container *c = s->ct; for (int i = 0; i < c->ient.n; i++) { IEnt *e = c->ient.a[i]; if (e->set == o) return; } IEnt *e = xalloc(sizeof *e); e->set = o; vpush(&c->ient, e); }
void eset_flatten(Type *s) { /* called by gen after the owning fn is generated */
  Container *c = s->ct;
  for (int i = 0; i < c->ient.n; i++) { IEnt *e = c->ient.a[i];
    if (e->name) { eset_push(c, e->name); continue; }
    Type *o = e->set; if (o == t_errset || !o->ct) { c->ianyerr = 1; continue; }
    if (is_inferred_eset(o)) eset_resolve(o);
    if (o->ct->ianyerr) c->ianyerr = 1; for (int j = 0; j < o->ct->fields.n; j++) eset_push(c, ((Field *)o->ct->fields.a[j])->name); }
}
Type *fn_type(Vec *params, Type *ret, int va) {
  for (int i = 0; i < types.n; i++) {
    Type *t = types.a[i];
    if (t->k != TY_FN || t->ret != ret || t->varargs != va || t->params.n != params->n) continue;
    int ok = 1; for (int j = 0; j < params->n; j++) if (t->params.a[j] != params->a[j]) ok = 0;
    if (ok) return t;
  }
  Type *t = mkt(TY_FN); for (int j = 0; j < params->n; j++) vpush(&t->params, params->a[j]); t->ret = ret; t->varargs = va; return t;
}
int is_int(Type *t) { return t->k == TY_INT || t->k == TY_CINT; }
int opt_is_ptr(Type *t) { return t->k == TY_OPT && (t->elem->k == TY_PTR || t->elem->k == TY_MPTR || t->elem->k == TY_FN); }
int is_scalar(Type *t) {
  switch (t->k) { case TY_BOOL: case TY_INT: case TY_ENUM: case TY_PTR: case TY_MPTR: case TY_ERRSET: case TY_FN: case TY_FLOAT: return 1;
  case TY_OPT: return opt_is_ptr(t); default: return 0; }
}
int is_aggr(Type *t) {
  switch (t->k) { case TY_SLICE: case TY_ARRAY: case TY_STRUCT: case TY_UNION: case TY_ERRU: case TY_TUPLE: return 1;
  case TY_INT: return t->bits > 64;
  case TY_FLOAT: return t->bits > 64; /* f80/f128 live in 16-byte memory (real format) */
  case TY_OPT: return !opt_is_ptr(t); default: return 0; }
}
static int alup(int x, int a) { return a ? (x + a - 1) / a * a : x; }
static void sz(Type *t) {
  if (t->size >= 0) return;
  switch (t->k) {
  case TY_BOOL: t->size = t->align = 1; break;
  case TY_INT: { int b = (t->bits + 7) / 8; int s = b <= 1 ? 1 : b <= 2 ? 2 : b <= 4 ? 4 : b <= 8 ? 8 : (b + 15) / 16 * 16; if (t->bits == 0) s = 0; t->size = s; t->align = s > 16 ? 16 : s ? s : 1; break; }
  case TY_PTR: case TY_MPTR: case TY_FN: t->size = t->align = 8; break;
  case TY_FLOAT: t->size = t->align = t->bits == 16 ? 2 : t->bits == 32 ? 4 : t->bits == 64 ? 8 : 16; break;
  case TY_SLICE: t->size = 16; t->align = 8; break;
  case TY_ARRAY: t->size = (int)(tsize(t->elem) * (t->len + t->hassent)); t->align = talign(t->elem); break;
  case TY_ERRSET: t->size = t->align = 2; break;
  case TY_OPT:
    if (opt_is_ptr(t)) { t->size = t->align = 8; break; }
    t->align = talign(t->elem); t->size = alup(tsize(t->elem) + 1, t->align); break;
  case TY_ERRU: { int a = talign(t->elem); if (a < 2) a = 2; t->align = a; t->size = alup(alup(2, a) + tsize(t->elem), a); break; }
  case TY_STRUCT: case TY_UNION: case TY_ENUM: case TY_TUPLE: layout(t->ct); break;
  default: t->size = 0; t->align = 1;
  }
}
int tsize(Type *t) { sz(t); return t->size; }
int talign(Type *t) { sz(t); return t->align; }
int erru_off(Type *t) { int a = talign(t->elem); return alup(2, a < 2 ? 2 : a); }
int same_type(Type *a, Type *b) { return a == b; }
char *tname(Type *t) {
  switch (t->k) {
  case TY_VOID: return "void"; case TY_BOOL: return "bool"; case TY_NORET: return "noreturn";
  case TY_INT: return fmt("%c%d", t->sign ? 'i' : 'u', t->bits); case TY_CINT: return "comptime_int";
  case TY_FLOAT: return fmt("f%d", t->bits); case TY_CFLOAT: return "comptime_float";
  case TY_PTR: return fmt("*%s%s", t->isconst ? "const " : "", tname(t->elem));
  case TY_MPTR: return fmt("[*]%s%s", t->isconst ? "const " : "", tname(t->elem));
  case TY_SLICE: return t->hassent ? fmt("[:%lld]%s%s", (long long)t->sent, t->isconst ? "const " : "", tname(t->elem)) : fmt("[]%s%s", t->isconst ? "const " : "", tname(t->elem));
  case TY_ARRAY: if (is_vec(t)) return fmt("@Vector(%lld, %s)", (long long)t->len, tname(t->elem));
    if (t->hassent) return fmt("[%lld:%lld]%s", (long long)t->len, (long long)t->sent, tname(t->elem));
    return fmt("[%lld]%s", (long long)t->len, tname(t->elem));
  case TY_OPT: return fmt("?%s", tname(t->elem)); case TY_ERRU: return fmt("%s!%s", tname(eset_of(t)), tname(t->elem));
  case TY_ERRSET: if (!t->ct) return "anyerror"; if (t->ct->name) return t->ct->name;
    if (t->ct->infer_d || t->ct->infer_fi) { Decl *d = t->ct->infer_d ? t->ct->infer_d : ((FnInst *)t->ct->infer_fi)->d; return fmt("@typeInfo(@typeInfo(@TypeOf(%s.%s)).@\"fn\".return_type.?).error_union.error_set", d->ct->name, d->name); }
    { char *r = "error{"; for (int i = 0; i < t->ct->fields.n; i++) r = fmt("%s%s%s", r, i ? "," : "", ((Field *)t->ct->fields.a[i])->name); return fmt("%s}", r); } case TY_TYPE: return "type"; case TY_FN: return "fn";
  case TY_NULL: return "@TypeOf(null)"; case TY_UNDEF: return "@TypeOf(undefined)"; case TY_ENUMLIT: return "@TypeOf(.enum_literal)";
  default: return t->ct && t->ct->name ? t->ct->name : "anon";
  }
}

/* ---------- scopes, containers, decls ---------- */
Scope *new_scope(Scope *up, Container *ct) { Scope *s = xalloc(sizeof *s); s->up = up; s->ct = ct; return s; }
void bind_cval(Scope *s, char *name, CVal v) { Sym *y = xalloc(sizeof *y); y->name = name; y->k = S_CVAL; y->cv = v; vpush(&s->syms, y); }
Sym *lookup_local(Scope *s, const char *name) {
  for (; s; s = s->up) { for (int i = s->syms.n - 1; i >= 0; i--) { Sym *y = s->syms.a[i]; if (!strcmp(y->name, name)) return y; } if (s->ct) return NULL; }
  return NULL;
}
Decl *find_decl(Container *c, const char *name) {
  for (int i = 0; i < c->decls.n; i++) { Decl *d = c->decls.a[i]; if (!strcmp(d->name, name)) return d; }
  return NULL;
}
/* full lookup: syms then container decls walking outward */
int lookup(Scope *s, const char *name, Sym **sy, Decl **dl) {
  *sy = NULL; *dl = NULL;
  for (; s; s = s->up) {
    for (int i = s->syms.n - 1; i >= 0; i--) { Sym *y = s->syms.a[i]; if (!strcmp(y->name, name)) { *sy = y; return 1; } }
    if (s->ct) { Decl *d = find_decl(s->ct, name); if (d) { *dl = d; return 1; } }
  }
  return 0;
}
Decl *lookup_decl_scope(Scope *s, const char *name) { Sym *y; Decl *d; lookup(s, name, &y, &d); return d; }

typedef struct { Node *n; Scope *s; Container *c; } CMemo;
static Vec cmemo;
static int anon_ct;
static int cv_same(CVal *a, CVal *b) {
  if (a->k != b->k) return 0;
  switch (a->k) {
  case CV_TYPE: return a->t == b->t;
  case CV_INT: case CV_BOOL: return a->i == b->i && a->t == b->t && a->big == b->big && a->ih == b->ih;
  case CV_ENUMLIT: return !strcmp(a->s, b->s);
  case CV_FN: return a->fn == b->fn;
  case CV_VOID: case CV_NULL: return 1;
  default: return 0;
  }
}
/* two scopes bind the same comptime values up to the enclosing container: a container
   expression evaluated in either yields the same type (e.g. inline param types) */
static Sym *scope_find_ct(Scope *s, const char *nm) {
  for (; s && !s->ct; s = s->up) for (int i = s->syms.n - 1; i >= 0; i--) { Sym *y = s->syms.a[i]; if (!strcmp(y->name, nm)) return y; }
  return NULL;
}
static void collect_ids(Node *n, Vec *out, int depth) {
  if (!n || depth > 2000) return;
  if (n->k == N_IDENT && n->s) { for (int i = 0; i < out->n; i++) if (!strcmp(out->a[i], n->s)) goto kids; vpush(out, n->s); }
kids:
  collect_ids(n->a, out, depth + 1); collect_ids(n->b, out, depth + 1); collect_ids(n->c, out, depth + 1); collect_ids(n->d, out, depth + 1);
  for (int i = 0; i < n->list.n; i++) collect_ids(n->list.a[i], out, depth + 1);
  for (int i = 0; i < n->list2.n; i++) collect_ids(n->list2.a[i], out, depth + 1);
}
static Vec idmemo_n, idmemo_v;
static Vec *container_ids(Node *n) {
  for (int i = 0; i < idmemo_n.n; i++) if (idmemo_n.a[i] == n) return idmemo_v.a[i];
  Vec *v = xalloc(sizeof *v); collect_ids(n, v, 0); vpush(&idmemo_n, n); vpush(&idmemo_v, v); return v;
}
/* a container expression evaluated in two scopes yields the same type if every identifier it references
   resolves to the same thing (same comptime value) in both, below the shared enclosing container */
static int scope_equiv(Node *n, Scope *a, Scope *b) {
  Scope *ca = a, *cb = b; while (ca && !ca->ct) ca = ca->up; while (cb && !cb->ct) cb = cb->up;
  if (ca != cb) return 0;
  Vec *ids = container_ids(n);
  for (int i = 0; i < ids->n; i++) {
    Sym *x = scope_find_ct(a, ids->a[i]), *y = scope_find_ct(b, ids->a[i]);
    if (!x && !y) continue;
    if (!x || !y) return 0;
    if (x == y) continue;
    if (x->k != S_CVAL || y->k != S_CVAL || !cv_same(&x->cv, &y->cv)) return 0;
  }
  return 1;
}
Container *container_from(Node *n, Scope *s, char *name) {
  for (int i = 0; i < cmemo.n; i++) { CMemo *m = cmemo.a[i]; if (m->n == n && (m->s == s || scope_equiv(n, m->s, s))) return m->c; }
  Container *c = xalloc(sizeof *c); c->node = n; c->scope = new_scope(s, c);
  c->name = name ? name : fmt("anon%d", ++anon_ct);
  int k = !strcmp(n->s, "enum") ? TY_ENUM : !strcmp(n->s, "union") ? TY_UNION : !strcmp(n->s, "opaque") ? TY_OPAQUE : TY_STRUCT;
  Type *t = mkt(k); t->ct = c; c->type = t;
  if (k == TY_UNION && (n->flags & F_TAGGED)) c->tagged = 1;
  for (int i = 0; i < n->list2.n; i++) {
    Node *d = n->list2.a[i]; Decl *dl = xalloc(sizeof *dl); dl->name = d->s; dl->node = d; dl->ct = c; vpush(&c->decls, dl);
  }
  CMemo *m = xalloc(sizeof *m); m->n = n; m->s = s; m->c = c; vpush(&cmemo, m);
  return c;
}
Field *find_field(Container *c, const char *name) {
  layout(c);
  for (int i = 0; i < c->fields.n; i++) { Field *f = c->fields.a[i]; if (!strcmp(f->name, name)) return f; }
  return NULL;
}
static int bits_for(int64_t n) { int b = 0; while ((1LL << b) < n) b++; return b; }
static int ty_bits(Type *t) {
  if (t->k == TY_INT) return t->bits; if (t->k == TY_BOOL) return 1;
  if (t->k == TY_ENUM) { layout(t->ct); return t->ct->tag->bits; }
  if (t->k == TY_STRUCT) { layout(t->ct); if (t->ct->layout_kind == 2) return t->ct->packed; }
  if (t->k == TY_UNION && t->ct && t->ct->node && (t->ct->node->flags & F_PACKED)) { layout(t->ct); int m = 0; for (int i = 0; i < t->ct->fields.n; i++) { Field *f = t->ct->fields.a[i]; int b = ty_bits(f->t); if (b > m) m = b; } return m; }
  if (t->k == TY_FLOAT) return t->bits;
  if (t->k == TY_VOID) return 0;
  return tsize(t) * 8;
}
static Type *synth_tag(Container *c) {
  Container *ec = xalloc(sizeof *ec); ec->name = fmt("@typeInfo(%s).tag", c->name); Type *et = mkt(TY_ENUM); et->ct = ec; ec->type = et;
  for (int i = 0; i < c->fields.n; i++) { Field *f = c->fields.a[i]; Field *ef = xalloc(sizeof *ef); ef->name = f->name; ef->val = i; vpush(&ec->fields, ef); }
  ec->tag = int_type(bits_for(c->fields.n), 0);
  for (int i = 0; i < ec->fields.n; i++) ((Field *)ec->fields.a[i])->t = ec->tag;
  et->size = tsize(ec->tag); et->align = talign(ec->tag); ec->laid = 1; return et;
}
static void layout_inner(Container *c);
void layout(Container *c) {
  if (c->laid) return;
  { static int depth; if (++depth > 2000) die("layout recursion too deep at %s (%s:%d)", c->name, c->node && c->node->tok ? c->node->tok->file : "?", c->node && c->node->tok ? c->node->tok->line : 0); layout_inner(c); depth--; return; }
}
static void layout_inner(Container *c) {
  Type *t = c->type; Node *n = c->node;
  if (c->laying) { if (t->size >= 0) return; die("type %s depends on itself", c->name); }
  c->laying = 1;
  if (t->k == TY_OPAQUE) { t->size = 0; t->align = 1; c->laid = 1; return; }
  if (t->k == TY_ENUM) {
    int64_t next = 0; Type *et0 = n->a ? eval_type(n->a, c->scope) : NULL;
    for (int i = 0; i < n->list.n; i++) {
      Node *fd = n->list.a[i]; if (!strcmp(fd->s, "_") && !(fd->tok && fd->tok->k == TK_ID && fd->tok->ival)) { c->nonexh = 1; continue; }
      Field *f = xalloc(sizeof *f); f->name = fd->s;
      if (fd->b) { CVal v; if (!(et0 ? ceval_rt(fd->b, c->scope, et0, &v) : ceval_force(fd->b, c->scope, &v))) die("%s:%d: enum value not comptime (at %s)", fd->tok->file, fd->tok->line, ct_fail_loc()); next = (int64_t)v.i; }
      f->val = next++; vpush(&c->fields, f);
    }
    c->tag = n->a ? eval_type(n->a, c->scope) : int_type(bits_for(c->fields.n), 0);
    for (int i = 0; i < c->fields.n; i++) ((Field *)c->fields.a[i])->t = c->tag;
    t->size = tsize(c->tag); t->align = talign(c->tag); c->laid = 1; return;
  }
  if (n) {
    if (n->flags & F_EXTERN) c->layout_kind = 1;
    if (n->flags & F_PACKED) c->layout_kind = 2;
    /* collect fields first (types resolved below) */
    for (int i = 0; i < n->list.n; i++) {
      Node *fd = n->list.a[i]; Field *f = xalloc(sizeof *f); f->name = fd->s; f->def = fd->b; vpush(&c->fields, f);
      if (fd->flags & F_ANYTYPE) c->is_tuple = 1;
    }
    for (int i = 0; i < n->list.n; i++) { Node *fd = n->list.a[i]; Field *f = c->fields.a[i]; f->t = fd->a ? eval_type(fd->a, c->scope) : t_void;
      if (fd->c) { CVal av; if (ceval_force(fd->c, c->scope, &av) && av.k == CV_INT && av.i > 0) f->align = (int)av.i; } }
  }
  if (t->k == TY_STRUCT && (c->layout_kind == 2 || c->packed)) {
    /* packed struct: fields are bit ranges of a backing integer */
    int bits = 0;
    for (int i = 0; i < c->fields.n; i++) { Field *f = c->fields.a[i]; f->bitoff = bits; f->off = 0; bits += ty_bits(f->t); }
    if (n && n->a) bits = eval_type(n->a, c->scope)->bits;
    else if (c->packed > 0) bits = c->packed;
    c->packed = bits; c->layout_kind = 2;
    if (!bits) { t->size = 0; t->align = 1; } else { Type *bt = int_type(bits, 0); t->size = tsize(bt); t->align = talign(bt); }
    c->laid = 1; return;
  }
  int off = 0, al = 1, maxs = 0;
  for (int i = 0; i < c->fields.n; i++) {
    Field *f = c->fields.a[i];
    int fs = tsize(f->t), fa = f->align ? f->align : talign(f->t);
    if (type_is_ctonly(f->t)) fs = 0, fa = 1;
    if (fa > al) al = fa;
    if (t->k == TY_UNION) { f->off = 0; if (fs > maxs) maxs = fs; f->val = i; }
    else { off = alup(off, fa); f->off = off; off += fs; }
  }
  if (t->k == TY_UNION) {
    if (n && (n->flags & F_TAGGED)) c->tagged = 1;
    if (c->tagged) {
      if (n && n->a && !(n->flags & F_ALLOWZERO)) c->tag = eval_type(n->a, c->scope);
      else if (!c->tag) { c->tag = synth_tag(c); if (n && n->a) { Type *it = eval_type(n->a, c->scope); c->tag->ct->tag = it; for (int i = 0; i < c->tag->ct->fields.n; i++) ((Field *)c->tag->ct->fields.a[i])->t = it; c->tag->size = tsize(it); c->tag->align = talign(it);
          int64_t next = 0; for (int i = 0; i < c->fields.n; i++) { Field *f = c->fields.a[i]; Field *ef = c->tag->ct->fields.a[i]; if (f->def) { CVal v; if (!ceval_rt(f->def, c->scope, it, &v)) die("union tag value not comptime"); next = (int64_t)v.i; f->def = NULL; } ef->val = next++; } } }
      if (!c->tag->ct) die("%s:%d: union tag of %s is not an enum (%s)", n->tok->file, n->tok->line, c->name, tname(c->tag));
      for (int i = 0; i < c->fields.n; i++) { Field *f = c->fields.a[i]; Field *ef = find_field(c->tag->ct, f->name); if (ef) f->val = ef->val; }
      int ta = talign(c->tag); if (ta > al) al = ta;
      off = alup(maxs, ta) + tsize(c->tag);
    } else off = maxs;
  }
  t->align = al; t->size = alup(off, al); c->laid = 1;
}
int union_tag_off(Type *t) { layout(t->ct); int maxs = 0; for (int i = 0; i < t->ct->fields.n; i++) { Field *f = t->ct->fields.a[i]; if (tsize(f->t) > maxs) maxs = tsize(f->t); } return alup(maxs, talign(t->ct->tag)); }

int err_id(const char *name) {
  for (int i = 0; i < errnames.n; i++) if (!strcmp(errnames.a[i], name)) return i + 1;
  vpush(&errnames, (void *)name); return errnames.n;
}

/* ---------- imports ---------- */
typedef struct { char *path; Container *c; } Imp;
static Vec imports;
extern const char *lib_dir;
Container *import_file(const char *path) {
  char *rp = realpath(path, NULL); if (!rp) die("cannot import %s", path);
  for (int i = 0; i < imports.n; i++) { Imp *m = imports.a[i]; if (!strcmp(m->path, rp)) return m->c; }
  Node *n = parse_file(rp);
  const char *b = strrchr(rp, '/'); char *nm = xstrndup(b + 1, strlen(b + 1) - 4);
  for (char *q = nm; *q; q++) if (!isalnum((unsigned char)*q) && *q != '_') *q = '_';
  if (isdigit((unsigned char)nm[0])) nm = fmt("m%s", nm);
  Container *c = container_from(n, NULL, nm);
  Imp *m = xalloc(sizeof *m); m->path = rp; m->c = c; vpush(&imports, m);
  return c;
}
static char *dir_of(const char *f) { const char *s = strrchr(f, '/'); return s ? xstrndup(f, s - f) : "."; }
const char *std_file, *std_builtin_file, *builtin_file; int using_real_std;
static Vec mod_names, mod_paths;
void add_module(const char *name, const char *path) {
  char *rp = realpath(path, NULL); if (!rp) die("-M%s: cannot open %s", name, path);
  vpush(&mod_names, (void *)name); vpush(&mod_paths, rp);
}
Container *do_import(Node *n, const char *name) {
  for (int i = 0; i < mod_names.n; i++) if (!strcmp(mod_names.a[i], name)) return import_file(mod_paths.a[i]);
  if (!std_file) std_file = fmt("%s/std.zig", lib_dir);
  if (!std_builtin_file) std_builtin_file = fmt("%s/std/builtin.zig", lib_dir);
  if (!builtin_file) builtin_file = fmt("%s/builtin.zig", lib_dir);
  if (!strcmp(name, "std")) return import_file(std_file);
  if (!strcmp(name, "builtin")) return import_file(builtin_file);
  if (!strcmp(name, "root")) return import_file(root_dir);
  return import_file(fmt("%s/%s", dir_of(n->tok->file), name));
}

/* ---------- decl resolution ---------- */
Type *prim_type(const char *s) {
  if ((s[0] == 'u' || s[0] == 'i') && s[1] && isdigit((unsigned char)s[1])) {
    for (const char *p = s + 1; *p; p++) if (!isdigit((unsigned char)*p)) return NULL;
    return int_type(atoi(s + 1), s[0] == 'i');
  }
  static const struct { const char *n; int b, s; } m[] = { {"usize",64,0},{"isize",64,1},{"c_int",32,1},{"c_uint",32,0},
    {"c_long",64,1},{"c_ulong",64,0},{"c_longlong",64,1},{"c_ulonglong",64,0},{"c_short",16,1},{"c_ushort",16,0},{"c_char",8,1},{0} };
  for (int i = 0; m[i].n; i++) if (!strcmp(s, m[i].n)) return int_type(m[i].b, m[i].s);
  if (!strcmp(s, "bool")) return t_bool; if (!strcmp(s, "void")) return t_void; if (!strcmp(s, "noreturn")) return t_noret;
  if (!strcmp(s, "type")) return t_type; if (!strcmp(s, "comptime_int")) return t_cint;
  if (!strcmp(s, "comptime_float")) return t_cfloat; if (!strcmp(s, "f16")) return t_f16; if (!strcmp(s, "f32")) return t_f32; if (!strcmp(s, "f64")) return t_f64;
  if (!strcmp(s, "f80") || !strcmp(s, "c_longdouble")) return t_f80; if (!strcmp(s, "f128")) return t_f128; if (!strcmp(s, "anyerror")) return t_errset;
  if (!strcmp(s, "anyopaque")) { static Type *ao; if (!ao) { ao = mkt(TY_OPAQUE); ao->size = 0; ao->align = 1; } return ao; }
  if (!strcmp(s, "anytype")) return t_anytype;
  return NULL;
}
int fn_is_generic(Node *f) {
  for (int i = 0; i < f->list.n; i++) { Node *p = f->list.a[i]; if (p->flags & (F_COMPTIME | F_ANYTYPE)) return 1; if (p->a && p->a->k == N_IDENT && !strcmp(p->a->s, "type")) return 1; }
  return 0;
}
void resolve_decl(Decl *d) {
  if (d->state == 2) return;
  if (d->state == 1) { if (d->kind) return; die("%s:%d: dependency loop on '%s'", d->node->tok->file, d->node->tok->line, d->name); }
  d->state = 1;
  Node *n = d->node; Scope *s = d->ct->scope;
  if (n->k == N_FN) { d->kind = D_FN; d->cv.k = CV_FN; d->cv.fn = d; d->state = 2; return; }
  if (n->flags & F_EXTERN) { d->kind = D_VAR; d->t = eval_type(n->a, s); d->sym = d->name; d->state = 2; return; }
  Type *t = n->a ? eval_type(n->a, s) : NULL;
  if ((n->flags & F_CONST) && n->b) {
    CVal v;
    if (n->b->k == N_CONTAINER) { /* name the container */
      Container *c = container_from(n->b, s, fmt("%s.%s", d->ct->name, d->name));
      v = cv_ty(c->type); d->kind = D_CONST; d->cv = v; d->state = 2; return;
    }
    if (ceval_rt(n->b, s, t, &v)) {
      if (t) v = ccoerce(v, t);
      d->kind = D_CONST; d->cv = v; d->t = t; d->state = 2; return;
    }
    if (!t && !typeof_hook) die("%s:%d: global const '%s' is not comptime-known", n->tok->file, n->tok->line, d->name);
  }
  d->kind = D_VAR; d->sym = d->xname ? d->xname : mangle(fmt("%s.%s", d->ct->name, d->name));
  d->t = t ? t : typeof_hook(n->b, s);
  if (d->t->k == TY_CINT) d->t = t_i64;
  if (n->b) {
    CVal v;
    if (ceval_rt(n->b, s, d->t, &v)) { d->cv = ccoerce(v, d->t); d->has_init = 1; }
    else die("%s:%d: global initializer of '%s' is not comptime-known (at %s)", n->tok->file, n->tok->line, d->name, ct_fail_loc());
  }
  d->state = 2;
  gen_global(d);
}

/* ---------- comptime helpers ---------- */
i128 wrap_int(i128 v, Type *t) {
  if (!t || t->k != TY_INT || t->bits >= 128) return v;
  if (t->bits == 0) return 0;
  unsigned __int128 m = (((unsigned __int128)1) << t->bits) - 1; unsigned __int128 u = (unsigned __int128)v & m;
  if (t->sign && ((u >> (t->bits - 1)) & 1)) u |= ~m;
  return (i128)u;
}
Container *this_container(Scope *s) { for (; s; s = s->up) if (s->ct) return s->ct; return NULL; }
int enum_val(Type *et, const char *name, int64_t *out) {
  Container *c = et->ct; if (et->k == TY_UNION) { layout(c); c = c->tag->ct; }
  layout(c);
  for (int i = 0; i < c->fields.n; i++) { Field *f = c->fields.a[i]; if (!strcmp(f->name, name)) { *out = f->val; return 1; } }
  return 0;
}
void bind_placeholder(Scope *s, char *name, Type *t) { Sym *y = xalloc(sizeof *y); y->name = name; y->k = S_LOCAL; y->t = t; vpush(&s->syms, y); }
static int mangle_n;
/* unique symbol names: sanitize and disambiguate */
static char **symtab; static int symcap, symcnt;
static unsigned shash(const char *s) { unsigned h = 2166136261u; for (; *s; s++) h = (h ^ (unsigned char)*s) * 16777619u; return h; }
static int sym_add(char *s) {
  if (symcnt * 2 >= symcap) {
    int nc = symcap ? symcap * 2 : 1024; char **nt = xalloc(sizeof(char *) * nc);
    for (int i = 0; i < symcap; i++) if (symtab[i]) { unsigned h = shash(symtab[i]) & (nc - 1); while (nt[h]) h = (h + 1) & (nc - 1); nt[h] = symtab[i]; }
    symtab = nt; symcap = nc;
  }
  unsigned h = shash(s) & (symcap - 1);
  while (symtab[h]) { if (!strcmp(symtab[h], s)) return 0; h = (h + 1) & (symcap - 1); }
  symtab[h] = s; symcnt++; return 1;
}
char *mangle(const char *s) {
  size_t n = strlen(s);
  char *r = xalloc(n + 24); size_t j = 0;
  for (size_t i = 0; i < n; i++) { char c = s[i]; r[j++] = (isalnum((unsigned char)c) || c == '_' || c == '.') ? c : '_'; }
  r[j] = 0;
  if (j > 64) { /* QBE identifiers are limited to 80 chars: keep head and tail */ memmove(r + 32, r + j - 30, 31); r[30] = '_'; r[31] = '_'; }
  if (sym_add(r)) return r;
  for (;;) { char *q = fmt("%s__%d", r, ++mangle_n); if (sym_add(q)) return q; }
}
FnInst *fn_instance(Decl *d, Vec *cargs) {
  for (int i = 0; i < d->insts.n; i++) {
    FnInst *fi = d->insts.a[i]; int ok = fi->cargs.n == cargs->n;
    for (int j = 0; ok && j < cargs->n; j++) if (!cval_eq(fi->cargs.a[j], cargs->a[j])) ok = 0;
    if (ok) return fi;
  }
  Node *f = d->node;
  FnInst *fi = xalloc(sizeof *fi); fi->d = d; fi->node = f; fi->scope = new_scope(d->ct->scope, NULL);
  for (int j = 0; j < cargs->n; j++) vpush(&fi->cargs, cargs->a[j]);
  vpush(&d->insts, fi);
  { extern FnInst *gen_cur_fi; extern Node *gen_cur_pub(void); fi->from = gen_cur_fi; fi->from_node = gen_cur_pub(); }
  if (getenv("ZB_INST_STAT") && (d->insts.n & (d->insts.n - 1)) == 0 && d->insts.n >= 64) fprintf(stderr, "insts %s: %d (%s:%d)\n", d->name, d->insts.n, f->tok->file, f->tok->line);
  int generic = 0;
  for (int i = 0; i < f->list.n; i++) {
    Node *p = f->list.a[i]; CVal *cv = i < cargs->n ? cargs->a[i] : NULL;
    if (p->flags & F_VARARGS) { vpush(&fi->ptypes, NULL); continue; }
    int ct = (p->flags & F_COMPTIME) || (p->a && p->a->k == N_IDENT && !strcmp(p->a->s, "type"));
    if (cv && !ct && (p->flags & F_ANYTYPE) && cv->k == CV_TYPE && cv->slen == -1) { vpush(&fi->ptypes, cv->t); if (p->s) bind_placeholder(fi->scope, p->s, cv->t); generic = 1; continue; }
    if (cv) {
      CVal v = *cv;
      if (p->a && !(p->flags & F_ANYTYPE)) v = ccoerce(v, eval_type(p->a, fi->scope));
      if (p->s) bind_cval(fi->scope, p->s, v); vpush(&fi->ptypes, NULL); generic = 1; continue;
    }
    Type *pt = eval_type(p->a, fi->scope);
    if (p->s) bind_placeholder(fi->scope, p->s, pt);
    vpush(&fi->ptypes, pt);
  }
  Type *r = eval_type(f->a, fi->scope);
  if (f->flags & F_INFERR) { Type *is; if (generic) { is = errset_infer(); is->ct->infer_fi = fi; is->ct->name = fmt("@typeInfo(@typeInfo(@TypeOf(%s.%s)).@\"fn\".return_type.?).error_union.error_set", d->ct->name, d->name); } else { is = decl_iset(d); is->ct->infer_fi = fi; } r = erru_of2(r, is); }
  fi->ret = r;
  if (f->flags & F_EXTERN) fi->sym = d->name;
  else if (f->flags & F_EXPORT) fi->sym = d->name;
  else if (generic) fi->sym = mangle(fmt("%s.%s__%d", d->ct->name, d->name, ++mangle_n));
  else fi->sym = mangle(fmt("%s.%s", d->ct->name, d->name));
  if (!(f->flags & (F_EXTERN | F_INLINE)) && !(r && type_is_ctonly(r))) queue_fn(fi); /* comptime-only results: always evaluated at comptime */
  return fi;
}
