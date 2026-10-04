#include "ct_int.h"

Type *bt_type_pub(const char *path) {
  return bt_type(path);
}
CVal cv_null_pub(void) {
  return cv_null();
}
Type *bt_type(const char *path) {
  Container *c = import_file(std_builtin_file);
  char buf[128];
  snprintf(buf, sizeof buf, "%s", path);
  char *sv;
  Type *t = NULL;
  for (char *p = strtok_r(buf, ".", &sv); p; p = strtok_r(NULL, ".", &sv)) {
    Decl *d = find_decl(c, p);
    if (!d) die("std.builtin.%s not found", path);
    resolve_decl(d);
    if (d->cv.k != CV_TYPE) die("std.builtin.%s is not a type", path);
    t = d->cv.t;
    c = t->ct;
  }
  return t;
}
Type *ftype(Type *st, const char *name) {
  int i = field_index(st, name);
  if (i < 0) die("no field %s in %s", name, tname(st));
  return field_at(st, i)->t;
}
void setf(CVal *a, const char *name, CVal v) {
  int i = field_index(a->t, name);
  if (i < 0) die("no field %s in %s", name, tname(a->t));
  *a->el[i] = ccoerce(v, field_at(a->t, i)->t);
}
CVal mk_struct(Type *t) {
  CVal a = agg_new(t);
  for (int i = 0; i < a.n; i++) *a.el[i] = default_of(t, field_at(t, i));
  return a;
}
CVal slice_val(Type *st, CVal *items, int n) {
  Type *et = st->elem;
  CVal arr = agg_new(array_of(et, n, 0, 0));
  for (int i = 0; i < n; i++) *arr.el[i] = ccoerce(items[i], et);
  CVal r = {0};
  r.k = CV_SLICE;
  r.base = box(arr);
  r.idx = 0;
  r.slen = n;
  r.t = st;
  return r;
}
CVal enum_lit_val(Type *et, const char *name) {
  int64_t v;
  if (!enum_val(et, name, &v)) die("no field %s in %s", name, tname(et));
  return cv_int(v, et);
}
CVal zstr(const char *s) {
  return cv_str(s, (int)strlen(s));
}
CVal ptr_to_val(CVal v) {
  CVal p = {0};
  p.k = CV_PTR;
  p.base = box(v);
  p.idx = -1;
  p.t = ptr_to(cv_typeof(&v), 1);
  return p;
}
CVal decls_val(Type *st, Container *c) {
  Type *dt = ftype(st, "decls");
  Vec items = {0};
  if (c)
    for (int i = 0; i < c->decls.n; i++) {
      Decl *d = c->decls.a[i];
      if (!(d->node->flags & F_PUB)) continue;
      CVal *e = xalloc(sizeof *e);
      *e = mk_struct(dt->elem);
      setf(e, "name", zstr(d->name));
      vpush(&items, e);
    }
  CVal *arr = xalloc(sizeof(CVal) * (items.n + 1));
  for (int i = 0; i < items.n; i++) arr[i] = *(CVal *)items.a[i];
  return slice_val(dt, arr, items.n);
}

int ti17(void) {
  static int v = -1;
  if (v < 0) v = field_index(bt_type("Type.Struct"), "field_names") >= 0;
  return v;
}
CVal names_val(Type *st, const char *fname, Container *c,
                      int decls) { /* []const [:0]const u8 of field or pub decl names */
  Type *dt = ftype(st, fname);
  Vec items = {0};
  if (c) {
    if (decls) {
      for (int i = 0; i < c->decls.n; i++) {
        Decl *d = c->decls.a[i];
        if (d->node->flags & F_PUB) vpush(&items, (void *)d->name);
      }
    } else
      for (int i = 0; i < c->fields.n; i++) vpush(&items, (void *)((Field *)c->fields.a[i])->name);
  }
  CVal *arr = xalloc(sizeof(CVal) * (items.n + 1));
  for (int i = 0; i < items.n; i++) arr[i] = zstr(items.a[i]);
  return slice_val(dt, arr, items.n);
}
CVal type_info17(Type *T, const char **tagp) {
  CVal pay = cv_void();
  const char *tag = NULL;
  switch (T->k) {
  case TY_PTR:
  case TY_MPTR:
  case TY_SLICE: {
    tag = "pointer";
    Type *pt = bt_type("Type.Pointer");
    pay = mk_struct(pt);
    setf(&pay, "size",
         enum_lit_val(bt_type("Type.Pointer.Size"), T->k == TY_PTR    ? "one"
                                                    : T->k == TY_MPTR ? "many"
                                                                      : "slice"));
    CVal at = mk_struct(ftype(pt, "attrs"));
    setf(&at, "const", cv_bool(T->isconst));
    setf(&pay, "attrs", at);
    setf(&pay, "child", cv_ty(T->elem));
    setf(&pay, "sentinel_ptr", T->hassent ? ptr_to_val(cv_int(T->sent, T->elem)) : cv_null());
    break;
  }
  case TY_STRUCT:
  case TY_TUPLE: {
    tag = "struct";
    Type *st = bt_type("Type.Struct");
    pay = mk_struct(st);
    layout(T->ct);
    setf(&pay, "layout",
         enum_lit_val(bt_type("Type.ContainerLayout"), T->ct->packed             ? "packed"
                                                       : T->ct->layout_kind == 1 ? "extern"
                                                                                 : "auto"));
    setf(&pay, "backing_integer", T->ct->packed ? cv_ty(int_type(T->ct->packed, 0)) : cv_null());
    int n = T->ct->fields.n;
    CVal *ts = xalloc(sizeof(CVal) * (n + 1)), *as = xalloc(sizeof(CVal) * (n + 1));
    Type *ft = ftype(st, "field_attrs");
    for (int i = 0; i < n; i++) {
      Field *f = T->ct->fields.a[i];
      ts[i] = cv_ty(f->t);
      as[i] = mk_struct(ft->elem);
      CVal dv = (f->def || f->defcv) ? default_of(T, f) : cv_undef(NULL);
      setf(&as[i], "default_value_ptr", dv.k != CV_UNDEF ? ptr_to_val(dv) : cv_null());
      setf(&as[i], "comptime", cv_bool((type_is_ctonly(f->t) && T->ct->is_tuple) || f->is_ct));
    }
    setf(&pay, "field_names", names_val(st, "field_names", T->ct, 0));
    setf(&pay, "field_types", slice_val(ftype(st, "field_types"), ts, n));
    setf(&pay, "field_attrs", slice_val(ft, as, n));
    setf(&pay, "decl_names", names_val(st, "decl_names", T->ct, 1));
    setf(&pay, "is_tuple", cv_bool(T->ct->is_tuple));
    break;
  }
  case TY_ENUM: {
    tag = "enum";
    Type *st = bt_type("Type.Enum");
    pay = mk_struct(st);
    layout(T->ct);
    setf(&pay, "tag_type", cv_ty(T->ct->tag));
    int n = T->ct->fields.n;
    CVal *vs = xalloc(sizeof(CVal) * (n + 1));
    for (int i = 0; i < n; i++) vs[i] = cv_int(((Field *)T->ct->fields.a[i])->val, t_cint);
    setf(&pay, "field_names", names_val(st, "field_names", T->ct, 0));
    setf(&pay, "field_values", slice_val(ftype(st, "field_values"), vs, n));
    setf(&pay, "decl_names", names_val(st, "decl_names", T->ct, 1));
    setf(&pay, "mode", enum_lit_val(bt_type("Type.Enum.Mode"), T->ct->nonexh ? "nonexhaustive" : "exhaustive"));
    break;
  }
  case TY_UNION: {
    tag = "union";
    Type *st = bt_type("Type.Union");
    pay = mk_struct(st);
    layout(T->ct);
    setf(&pay, "layout",
         enum_lit_val(bt_type("Type.ContainerLayout"), T->ct->layout_kind == 1   ? "extern"
                                                       : T->ct->layout_kind == 2 ? "packed"
                                                                                 : "auto"));
    setf(&pay, "tag_type", T->ct->tagged ? cv_ty(T->ct->tag) : cv_null());
    setf(&pay, "backing_integer", T->ct->layout_kind == 2 ? cv_ty(int_type(bits_of(T), 0)) : cv_null());
    int n = T->ct->fields.n;
    CVal *ts = xalloc(sizeof(CVal) * (n + 1)), *as = xalloc(sizeof(CVal) * (n + 1));
    Type *ft = ftype(st, "field_attrs");
    for (int i = 0; i < n; i++) {
      ts[i] = cv_ty(((Field *)T->ct->fields.a[i])->t);
      as[i] = mk_struct(ft->elem);
    }
    setf(&pay, "field_names", names_val(st, "field_names", T->ct, 0));
    setf(&pay, "field_types", slice_val(ftype(st, "field_types"), ts, n));
    setf(&pay, "field_attrs", slice_val(ft, as, n));
    setf(&pay, "decl_names", names_val(st, "decl_names", T->ct, 1));
    break;
  }
  case TY_ERRSET: {
    tag = "error_set";
    Type *st = bt_type("Type.ErrorSet");
    pay = mk_struct(st);
    if (is_inferred_eset(T)) eset_resolve(T);
    if (!T->ct || T->ct->ianyerr) {
      setf(&pay, "error_names", cv_null());
      break;
    }
    Type *ot = ftype(st, "error_names"), *slt = ot->k == TY_OPT ? ot->elem : ot;
    int n = T->ct->fields.n;
    CVal *arr = xalloc(sizeof(CVal) * (n + 1));
    for (int i = 0; i < n; i++) arr[i] = zstr(((Field *)T->ct->fields.a[i])->name);
    setf(&pay, "error_names", slice_val(slt, arr, n));
    break;
  }
  case TY_OPAQUE: {
    tag = "opaque";
    Type *st = bt_type("Type.Opaque");
    pay = mk_struct(st);
    setf(&pay, "decl_names", names_val(st, "decl_names", T->ct, 1));
    break;
  }
  case TY_FN:
  case TY_ANYTYPE: {
    tag = "fn";
    Type *st = bt_type("Type.Fn");
    pay = mk_struct(st);
    int gen = T->k == TY_ANYTYPE;
    CVal at = mk_struct(ftype(st, "attrs"));
    if (!gen) setf(&at, "varargs", cv_bool(T->varargs));
    setf(&pay, "attrs", at);
    setf(&pay, "is_generic", cv_bool(gen));
    setf(&pay, "return_type", !gen && T->ret ? cv_ty(T->ret) : cv_null());
    int n = gen ? 0 : T->params.n;
    CVal *ps = xalloc(sizeof(CVal) * (n + 1)), *as = xalloc(sizeof(CVal) * (n + 1));
    Type *pa = ftype(st, "param_attrs");
    for (int i = 0; i < n; i++) {
      ps[i] = cv_ty(T->params.a[i]);
      as[i] = mk_struct(pa->elem);
    }
    setf(&pay, "param_types", slice_val(ftype(st, "param_types"), ps, n));
    setf(&pay, "param_attrs", slice_val(pa, as, n));
    break;
  }
  default: return pay;
  }
  *tagp = tag;
  return pay;
}
CVal type_info(Type *T) {
  Type *TI = bt_type("Type");
  const char *tag = NULL;
  CVal pay = cv_void();
  if (ti17()) {
    pay = type_info17(T, &tag);
    if (tag) return mk_union(TI, tag, pay);
  }
  switch (T->k) {
  case TY_TYPE: tag = "type"; break;
  case TY_VOID: tag = "void"; break;
  case TY_BOOL: tag = "bool"; break;
  case TY_NORET: tag = "noreturn"; break;
  case TY_CINT: tag = "comptime_int"; break;
  case TY_CFLOAT: tag = "comptime_float"; break;
  case TY_FLOAT:
    tag = "float";
    pay = mk_struct(bt_type("Type.Float"));
    setf(&pay, "bits", cv_int(T->bits, t_u16));
    break;
  case TY_NULL: tag = "null"; break;
  case TY_UNDEF: tag = "undefined"; break;
  case TY_ENUMLIT: tag = "enum_literal"; break;
  case TY_INT: {
    tag = "int";
    Type *it = bt_type("Type.Int");
    pay = mk_struct(it);
    setf(&pay, "signedness", enum_lit_val(bt_type("Signedness"), T->sign ? "signed" : "unsigned"));
    setf(&pay, "bits", cv_int(T->bits, t_u16));
    break;
  }
  case TY_PTR:
  case TY_MPTR:
  case TY_SLICE: {
    tag = "pointer";
    Type *pt = bt_type("Type.Pointer");
    pay = mk_struct(pt);
    setf(&pay, "size",
         enum_lit_val(bt_type("Type.Pointer.Size"), T->k == TY_PTR    ? "one"
                                                    : T->k == TY_MPTR ? "many"
                                                                      : "slice"));
    setf(&pay, "is_const", cv_bool(T->isconst));
    setf(&pay, "is_volatile", cv_bool(0));
    setf(&pay, "alignment", cv_null());
    setf(&pay, "address_space", enum_lit_val(bt_type("AddressSpace"), "generic"));
    setf(&pay, "child", cv_ty(T->elem));
    setf(&pay, "is_allowzero", cv_bool(0));
    setf(&pay, "sentinel_ptr", T->hassent ? ptr_to_val(cv_int(T->sent, T->elem)) : cv_null());
    break;
  }
  case TY_ARRAY:
    if (is_vec(T)) {
      tag = "vector";
      pay = mk_struct(bt_type("Type.Vector"));
      setf(&pay, "len", cv_int(T->len, t_cint));
      setf(&pay, "child", cv_ty(T->elem));
      break;
    }
    tag = "array";
    pay = mk_struct(bt_type("Type.Array"));
    setf(&pay, "len", cv_int(T->len, t_cint));
    setf(&pay, "child", cv_ty(T->elem));
    setf(&pay, "sentinel_ptr", T->hassent ? ptr_to_val(cv_int(T->sent, T->elem)) : cv_null());
    break;
  case TY_STRUCT:
  case TY_TUPLE: {
    tag = "struct";
    Type *st = bt_type("Type.Struct");
    pay = mk_struct(st);
    layout(T->ct);
    setf(&pay, "layout",
         enum_lit_val(bt_type("Type.ContainerLayout"), T->ct->packed             ? "packed"
                                                       : T->ct->layout_kind == 1 ? "extern"
                                                                                 : "auto"));
    setf(&pay, "backing_integer", T->ct->packed ? cv_ty(int_type(T->ct->packed, 0)) : cv_null());
    Type *ft = ftype(st, "fields");
    int n = T->ct->fields.n;
    CVal *fs = xalloc(sizeof(CVal) * (n + 1));
    for (int i = 0; i < n; i++) {
      Field *f = T->ct->fields.a[i];
      fs[i] = mk_struct(ft->elem);
      setf(&fs[i], "name", zstr(f->name));
      setf(&fs[i], "type", cv_ty(f->t));
      CVal dv = (f->def || f->defcv) ? default_of(T, f) : cv_undef(NULL);
      setf(&fs[i], "default_value_ptr", dv.k != CV_UNDEF ? ptr_to_val(dv) : cv_null());
      setf(&fs[i], "is_comptime", cv_bool((type_is_ctonly(f->t) && T->ct->is_tuple) || f->is_ct));
      setf(&fs[i], "alignment", cv_null());
    }
    setf(&pay, "fields", slice_val(ft, fs, n));
    setf(&pay, "decls", decls_val(st, T->ct));
    setf(&pay, "is_tuple", cv_bool(T->ct->is_tuple));
    break;
  }
  case TY_ENUM: {
    tag = "enum";
    Type *st = bt_type("Type.Enum");
    pay = mk_struct(st);
    layout(T->ct);
    setf(&pay, "tag_type", cv_ty(T->ct->tag));
    Type *ft = ftype(st, "fields");
    int n = T->ct->fields.n;
    CVal *fs = xalloc(sizeof(CVal) * (n + 1));
    for (int i = 0; i < n; i++) {
      Field *f = T->ct->fields.a[i];
      fs[i] = mk_struct(ft->elem);
      setf(&fs[i], "name", zstr(f->name));
      setf(&fs[i], "value", cv_int(f->val, t_cint));
    }
    setf(&pay, "fields", slice_val(ft, fs, n));
    setf(&pay, "decls", decls_val(st, T->ct));
    setf(&pay, "is_exhaustive", cv_bool(!T->ct->nonexh));
    break;
  }
  case TY_UNION: {
    tag = "union";
    Type *st = bt_type("Type.Union");
    pay = mk_struct(st);
    layout(T->ct);
    setf(&pay, "layout",
         enum_lit_val(bt_type("Type.ContainerLayout"), T->ct->layout_kind == 1   ? "extern"
                                                       : T->ct->layout_kind == 2 ? "packed"
                                                                                 : "auto"));
    setf(&pay, "tag_type", T->ct->tagged ? cv_ty(T->ct->tag) : cv_null());
    Type *ft = ftype(st, "fields");
    int n = T->ct->fields.n;
    CVal *fs = xalloc(sizeof(CVal) * (n + 1));
    for (int i = 0; i < n; i++) {
      Field *f = T->ct->fields.a[i];
      fs[i] = mk_struct(ft->elem);
      setf(&fs[i], "name", zstr(f->name));
      setf(&fs[i], "type", cv_ty(f->t));
      setf(&fs[i], "alignment", cv_null());
    }
    setf(&pay, "fields", slice_val(ft, fs, n));
    setf(&pay, "decls", decls_val(st, T->ct));
    break;
  }
  case TY_OPT:
    tag = "optional";
    pay = mk_struct(bt_type("Type.Optional"));
    setf(&pay, "child", cv_ty(T->elem));
    break;
  case TY_ERRU:
    tag = "error_union";
    pay = mk_struct(bt_type("Type.ErrorUnion"));
    setf(&pay, "error_set", cv_ty(eset_of(T)));
    setf(&pay, "payload", cv_ty(T->elem));
    break;
  case TY_ERRSET:
    tag = "error_set";
    if (is_inferred_eset(T)) eset_resolve(T);
    if (!T->ct || T->ct->ianyerr) {
      pay = cv_null();
      break;
    }
    {
      Type *ot = bt_type("Type.ErrorSet"), *slt = ot->k == TY_OPT ? ot->elem : ot;
      int n = T->ct->fields.n;
      CVal *fs = xalloc(sizeof(CVal) * (n + 1));
      for (int i = 0; i < n; i++) {
        fs[i] = mk_struct(slt->elem);
        setf(&fs[i], "name", zstr(((Field *)T->ct->fields.a[i])->name));
      }
      pay = slice_val(slt, fs, n);
    }
    break;
  case TY_OPAQUE:
    tag = "opaque";
    {
      Type *st = bt_type("Type.Opaque");
      pay = mk_struct(st);
      setf(&pay, "decls", decls_val(st, T->ct));
    }
    break;
  case TY_FN: {
    tag = "fn";
    Type *st = bt_type("Type.Fn");
    pay = mk_struct(st);
    setf(&pay, "calling_convention", enum_lit_val(bt_type("CallingConvention"), "auto"));
    setf(&pay, "is_generic", cv_bool(0));
    setf(&pay, "is_var_args", cv_bool(T->varargs));
    setf(&pay, "return_type", T->ret ? cv_ty(T->ret) : cv_null());
    Type *ft = ftype(st, "params");
    int n = T->params.n;
    CVal *ps = xalloc(sizeof(CVal) * (n + 1));
    for (int i = 0; i < n; i++) {
      ps[i] = mk_struct(ft->elem);
      setf(&ps[i], "is_generic", cv_bool(0));
      setf(&ps[i], "is_noalias", cv_bool(0));
      setf(&ps[i], "type", cv_ty(T->params.a[i]));
    }
    setf(&pay, "params", slice_val(ft, ps, n));
    break;
  }
  case TY_ANYTYPE: { /* type of a generic function */
    tag = "fn";
    Type *st = bt_type("Type.Fn");
    pay = mk_struct(st);
    setf(&pay, "calling_convention", enum_lit_val(bt_type("CallingConvention"), "auto"));
    setf(&pay, "is_generic", cv_bool(1));
    setf(&pay, "is_var_args", cv_bool(0));
    setf(&pay, "return_type", cv_null());
    Type *ft = ftype(st, "params");
    setf(&pay, "params", slice_val(ft, NULL, 0));
    break;
  }
  default: die("@typeInfo: unsupported type %s (kind %d)", tname(T), T->k);
  }
  return mk_union(TI, tag, pay);
}

/* ---------- builtins ---------- */
char *cv_cstr(CVal *v, int *lenp) {
  if (v->k == CV_STR) {
    if (lenp) *lenp = v->slen;
    return xstrndup(v->s, v->slen);
  }
  int64_t n;
  if (!cv_len(v, &n)) {
    Type *t = cv_typeof(v);
    if (v->k == CV_PTR && t->k == TY_PTR && t->elem->k == TY_ARRAY)
      n = t->elem->len;
    else
      return NULL;
  }
  char *r = xalloc(n + 1);
  for (int64_t i = 0; i < n; i++) r[i] = (char)cv_elem(v, i).i;
  if (lenp) *lenp = (int)n;
  return r;
}
CVal seq_at(CVal *v, int64_t i) {
  /* element i of a sequence, where @splat values (and pointers to them) repeat */
  CVal *x = v;
  if (x->k == CV_PTR && x->base && x->idx < 0 && x->base->k == CV_AGG && x->base->t == t_splat) x = x->base;
  if (x->k == CV_AGG && x->t == t_splat) return *x->el[0];
  return cv_elem(v, i);
}
int agg_get(CVal *a, const char *name, CVal *out) {
  if (a->k != CV_AGG || !is_struct_like(a->t)) return 0;
  int fi = field_index(a->t, name);
  if (fi < 0) return 0;
  *out = *a->el[fi];
  return 1;
}
Container *mk_container(int k, const char *name) {
  Container *c = xalloc(sizeof *c);
  c->name = (char *)name;
  Type *t = xalloc(sizeof *t);
  t->k = k;
  t->ct = c;
  t->size = -1;
  c->type = t;
  return c;
}
