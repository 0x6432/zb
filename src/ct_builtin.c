#include "ct_int.h"
#define B(nm) (!strcmp(b0, nm))
#define TY(node, var)                                                                                                  \
  do {                                                                                                                 \
    CVal tv_;                                                                                                          \
    ct_force++;                                                                                                        \
    int r_ = ev(node, s, &tv_);                                                                                        \
    ct_force--;                                                                                                        \
    if (r_ != R_OK) return r_;                                                                                         \
    if (tv_.k != CV_TYPE) return R_FAIL;                                                                               \
    var = tv_.t;                                                                                                       \
  } while (0)

int ev_builtin(Node *n, Scope *s, CVal *out) {
  const char *b0 = n->s;
  Type *rt = brt;
  brt = NULL;
  int na = n->list.n;
  Node *x = na > 0 ? n->list.a[0] : NULL, *y = na > 1 ? n->list.a[1] : NULL, *z = na > 2 ? n->list.a[2] : NULL;
  CVal a, b, c;
  Type *T;
  Type *urt = unwrap_rt(rt);
  if (B("backingInt")) { /* 0.17: enums / tagged unions -> tag int; bitpacks -> backing int */
    EV(x, s, &a);
    Type *at = cv_typeof(&a);
    if (at->k == TY_ENUM || at->k == TY_UNION && at->ct->tagged || at->k == TY_CINT || at->k == TY_INT)
      b0 = "intFromEnum";
    else {
      b0 = "bitCast";
      urt = int_type(bits_of(at), 0);
    }
  } else if (B("fromBackingInt")) {
    if (!urt) return R_FAIL;
    b0 = urt->k == TY_ENUM ? "enumFromInt" : "bitCast";
  }
  if (B("divCeil")) {
    EV(x, s, &a);
    EV(y, s, &b);
    if (a.k != CV_INT || b.k != CV_INT || !b.i) return R_FAIL;
    Type *t = peer_int(&a, &b);
    i128 p = a.i, q = b.i, r = p / q;
    if ((p % q != 0) && ((p < 0) == (q < 0))) r++;
    *out = cv_int(wrap_int(r, t), t);
    return R_OK;
  }
  if (B("This")) {
    *out = cv_ty(this_container(s)->type);
    return R_OK;
  }
  if (B("import")) {
    EV(x, s, &a);
    if (a.k != CV_STR) return R_FAIL;
    if (a.slen > 4 &&
        !memcmp(a.s + a.slen - 4, ".zon", 4)) { /* ZON: evaluate the file's expression with the result type */
      static Vec zp, zn;
      const char *f = n->tok->file, *sl = strrchr(f, '/');
      char *path = fmt("%s/%.*s", sl ? xstrndup(f, sl - f) : ".", a.slen, a.s);
      Node *e = NULL;
      for (int i = 0; i < zp.n; i++)
        if (!strcmp(zp.a[i], path)) e = zn.a[i];
      if (!e) {
        e = parse_zon(path);
        vpush(&zp, path);
        vpush(&zn, e);
      }
      ct_force++;
      int r = ev_rt(e, s, urt, out);
      ct_force--;
      if (r == R_OK && urt) *out = ccoerce(*out, urt);
      return r;
    }
    *out = cv_ty(do_import(n, xstrndup(a.s, a.slen))->type);
    return R_OK;
  }
  if (B("embedFile")) {
    EV(x, s, &a);
    const char *f = n->tok->file;
    const char *sl = strrchr(f, '/');
    char *dir = sl ? xstrndup(f, sl - f) : ".";
    long len;
    char *d = read_file(fmt("%s/%.*s", dir, a.slen, a.s), &len);
    if (!d) die("@embedFile: cannot read %.*s", a.slen, a.s);
    *out = cv_str(d, (int)len);
    return R_OK;
  }
  if (B("TypeOf")) {
    int sf = ct_force;
    ct_force = 0;
    int sxs = xs;
    Node *sfn = fail_node;
    Type *res = NULL;
    for (int i = 0; i < na; i++) {
      CVal v;
      int r = ev(n->list.a[i], s, &v);
      xs = sxs;
      Type *t;
      if (r == R_OK && v.k == CV_FN && !v.t && !fn_is_generic(v.fn->node)) {
        Node *f = v.fn->node;
        Vec ps = {0};
        Scope *fs = v.fn->ct->scope;
        for (int j = 0; j < f->list.n; j++) {
          Node *p = f->list.a[j];
          if (p->flags & F_VARARGS) continue;
          vpush(&ps, eval_type(p->a, fs));
        }
        Type *rr = eval_type(f->a, fs);
        if (f->flags & F_INFERR) rr = erru_of2(rr, decl_iset(v.fn));
        t = fn_type(&ps, rr, !!(f->flags & F_VARARGS));
      } else if (r == R_OK && v.k != CV_UNDEF)
        t = cv_typeof(&v);
      else {
        ct_force = sf;
        t = typeof_hook(n->list.a[i], s);
        ct_force = 0;
      }
      if (!res || res->k == TY_CINT || res->k == TY_NULL) {
        if (res && res->k == TY_NULL && t->k != TY_NULL && t->k != TY_OPT) t = opt_of(t);
        res = t;
      } else if (t->k == TY_NULL && res->k != TY_OPT)
        res = opt_of(res);
    }
    ct_force = sf;
    fail_node = sfn;
    *out = cv_ty(res);
    return R_OK;
  }
  if (B("sizeOf")) {
    TY(x, T);
    *out = cv_int(type_is_ctonly(T) ? 0 : tsize(T), t_cint);
    return R_OK;
  }
  if (B("alignOf")) {
    TY(x, T);
    *out = cv_int(talign(T), t_cint);
    return R_OK;
  }
  if (B("bitSizeOf")) {
    TY(x, T);
    *out = cv_int(bits_of(T), t_cint);
    return R_OK;
  }
  if (B("offsetOf") || B("bitOffsetOf")) {
    TY(x, T);
    EV(y, s, &b);
    Field *f = find_field(T->ct, cv_cstr(&b, NULL));
    if (!f) return R_FAIL;
    *out = cv_int(B("offsetOf") ? (is_packed(T) ? f->bitoff / 8 : f->off) : (is_packed(T) ? f->bitoff : f->off * 8),
                  t_cint);
    return R_OK;
  }
  if (B("FieldType")) {
    TY(x, T);
    EV(y, s, &b);
    Field *f = find_field(T->ct, cv_cstr(&b, NULL));
    if (!f) die("@FieldType: no field");
    *out = cv_ty(f->t);
    return R_OK;
  }
  if (B("export")) {
    EV(y, s, &b);
    {
      Type *ot0 = cv_typeof(&b);
      int fi0 = field_index(ot0, "name");
      Node *xx = x;
      if (xx->k == N_UN && xx->s && !strcmp(xx->s, "&")) xx = xx->a;
      Decl *dd = NULL;
      if (fi0 >= 0 && xx->k == N_IDENT)
        for (Scope *sc = s; sc && !dd; sc = sc->up)
          if (sc->ct) dd = find_decl(sc->ct, xx->s);
      if (dd && dd->node->k == N_VAR && !(dd->node->flags & F_CONST) && dd->state == 0) {
        dd->xname = cv_cstr(b.el[fi0], NULL);
        dd->node->flags |= F_EXPORT;
        resolve_decl(dd);
      }
    }
    EV(x, s, &a);
    ExportReq *er = xalloc(sizeof *er);
    er->v = a;
    er->node = x;
    er->scope = s;
    Type *ot = cv_typeof(&b);
    int fi = field_index(ot, "name");
    if (fi < 0) return R_FAIL;
    er->name = cv_cstr(b.el[fi], NULL);
    fi = field_index(ot, "linkage");
    if (fi >= 0 && b.el[fi]->k == CV_INT) {
      Type *lt = cv_typeof(b.el[fi]);
      if (lt && lt->ct)
        for (int i = 0; i < lt->ct->fields.n; i++) {
          Field *f = lt->ct->fields.a[i];
          if (f->val == (int64_t)b.el[fi]->i && !strcmp(f->name, "weak")) er->weak = 1;
        }
    }
    vpush(&zb_exports, er);
    *out = cv_void();
    return R_OK;
  }
  if (B("hasDecl")) {
    TY(x, T);
    EV(y, s, &b);
    char *nm = cv_cstr(&b, NULL);
    Decl *hd = T->ct ? find_decl(T->ct, nm) : NULL;
    *out = cv_bool(hd && (!zig17 || (hd->node->flags & F_PUB)));
    return R_OK;
  }
  if (B("hasField")) {
    TY(x, T);
    EV(y, s, &b);
    char *nm = cv_cstr(&b, NULL);
    if (T->k == TY_PTR) T = T->elem;
    *out = cv_bool(T->ct && T->k != TY_OPAQUE && find_field(T->ct, nm) != NULL);
    return R_OK;
  }
  if (B("typeName")) {
    TY(x, T);
    *out = zstr(tname(T));
    return R_OK;
  }
  if (B("field")) {
    EV(y, s, &b);
    char *nm = cv_cstr(&b, NULL);
    if (!nm) return R_FAIL;
    Type *at;
    if (!strcmp(nm, "len") && is_local_array(s, x, &at)) {
      *out = cv_int(at->len, t_usize);
      return R_OK;
    }
    EV(x, s, &a);
    if (ceval_member(a, nm, out)) return R_OK;
    return R_FAIL;
  }
  if (B("as")) {
    TY(x, T);
    CVal v;
    EVR(y, s, T, &v);
    *out = ccoerce(v, T);
    return R_OK;
  }
  if (B("intCast") || B("truncate")) {
    EV(x, s, &a);
    if (a.k != CV_INT) return R_FAIL;
    if (!urt || (urt->k != TY_INT && urt->k != TY_CINT)) {
      *out = a;
      return R_OK;
    }
    if (B("intCast") && urt->k == TY_INT) {
      i128 lo = urt->sign ? -((i128)1 << (urt->bits - 1)) : 0,
           hi = urt->sign ? ((i128)1 << (urt->bits - 1)) - 1 : umask(urt->bits);
      if (urt->bits < 127 && (a.i < lo || a.i > hi) && ct_force)
        die("%s:%d: @intCast: value %lld does not fit in %s", n->tok->file, n->tok->line, (long long)a.i, tname(urt));
    }
    *out = cv_int(wrap_int(a.i, urt), urt);
    return R_OK;
  }
  if (B("bitCast")) {
    EV(x, s, &a);
    if (!urt) return R_FAIL;
    if (urt->ct && (urt->k == TY_STRUCT || urt->k == TY_UNION)) layout(urt->ct);
    if (a.k == CV_UNDEF) {
      *out = cv_undef(urt);
      return R_OK;
    }
    Type *ft = cv_typeof(&a);
    if (ft && ft->ct && (ft->k == TY_STRUCT || ft->k == TY_UNION)) layout(ft->ct);
    if (packed_type(urt) && (packed_type(ft) || a.k == CV_INT || a.k == CV_FLOAT)) {
      i128 v = pack_val(&a);
      if (ft->k == TY_INT || ft->k == TY_ENUM || ft->k == TY_FLOAT || is_packed(ft)) v &= umask(bits_of(ft));
      *out = unpack_val(v, urt);
      return R_OK;
    }
    if ((urt->k == TY_ARRAY || ft->k == TY_ARRAY) && a.k != CV_UNDEF && (a.k == CV_AGG || ft->k != TY_ARRAY) &&
        cleaf_ok(urt) && cleaf_ok(ft) && clbits(urt) <= 128 && clbits(ft) == clbits(urt)) {
      i128 acc = 0;
      int off = 0;
      cflat(&a, ft, &acc, &off);
      off = 0;
      *out = cunflat(urt, acc, &off);
      return R_OK;
    }
    if (urt->k == TY_ARRAY && ft->k == TY_ARRAY && urt->len == ft->len) {
      *out = ccoerce(a, urt);
      return R_OK;
    }
    if (urt->k == TY_ARRAY && (ft->k == TY_INT) && urt->elem->k == TY_INT) {
      CVal r = agg_new(urt);
      int eb = urt->elem->bits;
      for (int i = 0; i < r.n; i++) *r.el[i] = cv_int(wrap_int((a.i >> (eb * i)) & umask(eb), urt->elem), urt->elem);
      *out = r;
      return R_OK;
    }
    if (urt->k == TY_INT && ft->k == TY_ARRAY && ft->elem->k == TY_INT && a.k == CV_AGG) {
      i128 v = 0;
      int eb = ft->elem->bits;
      for (int i = 0; i < a.n; i++) v |= (a.el[i]->i & umask(eb)) << (eb * i);
      *out = cv_int(wrap_int(v, urt), urt);
      return R_OK;
    }
    return R_FAIL;
  }
  if (B("enumFromInt")) {
    EV(x, s, &a);
    if (a.k != CV_INT || !urt || urt->k != TY_ENUM) return R_FAIL;
    *out = cv_int(a.i, urt);
    return R_OK;
  }
  if (B("intFromEnum")) {
    EV(x, s, &a);
    if (a.k == CV_AGG && a.t->k == TY_UNION && a.t->ct->tagged) {
      Field *f = field_at(a.t, (int)a.i);
      *out = cv_int(f->val, a.t->ct->tag->ct->tag);
      return R_OK;
    }
    if (a.k != CV_INT) return R_FAIL;
    Type *t = cv_typeof(&a);
    *out = cv_int(a.i, t->k == TY_ENUM ? (layout(t->ct), t->ct->tag) : t);
    return R_OK;
  }
  if (B("intFromBool")) {
    EV(x, s, &a);
    if (a.k != CV_BOOL) return R_FAIL;
    *out = cv_int(a.i, t_u1);
    return R_OK;
  }
  if (B("min") || B("max")) {
    EV(x, s, &a);
    for (int i = 1; i < na; i++) {
      EV(n->list.a[i], s, &b);
      if (a.k == CV_AGG && b.k == CV_AGG) {
        CVal r = agg_new(a.t);
        for (int j = 0; j < a.n; j++) {
          CVal p = *a.el[j], q = *b.el[j];
          *r.el[j] = (B("min") ? p.i < q.i : p.i > q.i) ? p : q;
        }
        a = r;
        continue;
      }
      if ((a.k == CV_FLOAT || b.k == CV_FLOAT) && (a.k == CV_FLOAT || a.k == CV_INT) &&
          (b.k == CV_FLOAT || b.k == CV_INT)) {
        Type *ta = cv_typeof(&a), *tb = cv_typeof(&b);
        Type *t = ta->k == TY_FLOAT ? ta : tb->k == TY_FLOAT ? tb : t_cfloat;
        f128 p = a.k == CV_FLOAT ? a.f : (f128)a.i, q = b.k == CV_FLOAT ? b.f : (f128)b.i;
        a = cv_float(p != p ? q : q != q ? p : B("min") ? (p < q ? p : q) : (p > q ? p : q), t);
        continue;
      }
      if (a.k != CV_INT || b.k != CV_INT) return R_FAIL;
      Type *t = peer_int(&a, &b);
      CVal m = (B("min") ? a.i <= b.i : a.i >= b.i) ? a : b;
      a = cv_int(m.i, t);
    }
    *out = a;
    return R_OK;
  }
  if (B("compileError")) {
    EV(x, s, &a);
    int l;
    char *m = cv_cstr(&a, &l);
    die("%s:%d: error: %s", n->tok->file, n->tok->line, m ? m : "@compileError");
  }
  if (B("compileLog")) {
    fprintf(stderr, "%s:%d: @compileLog:", n->tok->file, n->tok->line);
    for (int i = 0; i < na; i++) {
      CVal v;
      if (ev(n->list.a[i], s, &v) == R_OK)
        fprintf(stderr, " %s", cv_name(&v));
      else
        fprintf(stderr, " (runtime)");
    }
    fprintf(stderr, "\n");
    *out = cv_void();
    return R_OK;
  }
  if (B("panic")) {
    if (!ct_force) return R_FAIL;
    EV(x, s, &a);
    die("%s:%d: panic at comptime: %s", n->tok->file, n->tok->line, cv_cstr(&a, NULL));
  }
  if (B("inComptime")) {
    *out = cv_bool(ct_force > 0);
    return R_OK;
  }
  if (B("setEvalBranchQuota") || B("setRuntimeSafety") || B("branchHint") || B("setFloatMode") ||
      B("disableInstrumentation") || B("disableIntrinsics")) {
    *out = cv_void();
    return R_OK;
  }
  if (B("errorReturnTrace")) {
    *out = cv_null();
    return R_OK;
  }
  if (B("typeInfo")) {
    TY(x, T);
    if (T->tinfo) {
      *out = *(CVal *)T->tinfo;
      return R_OK;
    }
    *out = type_info(T);
    if (!T->ct || (T->ct->laid && !T->ct->laying)) {
      CVal *c = xalloc(sizeof *c);
      *c = *out;
      T->tinfo = c;
    }
    return R_OK;
  }
  if (B("Int")) {
    CVal sg;
    EVR(x, s, bt_type("Signedness"), &sg);
    EV(y, s, &b);
    if (b.k != CV_INT || sg.k != CV_INT) return R_FAIL;
    int64_t sv;
    enum_val(bt_type("Signedness"), "signed", &sv);
    *out = cv_ty(int_type((int)b.i, sg.i == sv));
    return R_OK;
  }
  if (B("Vector")) {
    EV(x, s, &a);
    TY(y, T);
    if (a.k != CV_INT) return R_FAIL;
    *out = cv_ty(vec_of(T, (int64_t)a.i));
    return R_OK;
  }
  if (B("EnumLiteral")) {
    *out = cv_ty(t_enumlit);
    return R_OK;
  }
  if (B("Tuple")) {
    EV(x, s, &a);
    int64_t len;
    if (!cv_len(&a, &len)) return R_FAIL;
    Vec names = {0}, types = {0};
    for (int64_t i = 0; i < len; i++) {
      CVal e = cv_elem(&a, i);
      if (e.k != CV_TYPE) return R_FAIL;
      vpush(&names, fmt("%d", (int)i));
      vpush(&types, e.t);
    }
    *out = cv_ty(mk_anon_struct(&names, &types, 1));
    return R_OK;
  }
  if (B("Pointer")) {
    CVal sz;
    EVR(x, s, bt_type("Type.Pointer.Size"), &sz);
    CVal at;
    EVR(y, s, bt_type("Type.Pointer.Attributes"), &at);
    TY(z, T);
    CVal sn = cv_null();
    if (na > 3) EVR(n->list.a[3], s, opt_of(T), &sn);
    CVal cf;
    int isc = agg_get(&at, "const", &cf) && cf.i;
    int64_t one, many, slc;
    Type *st = bt_type("Type.Pointer.Size");
    enum_val(st, "one", &one);
    enum_val(st, "many", &many);
    enum_val(st, "slice", &slc);
    int hs = sn.k != CV_NULL && sn.k != CV_UNDEF;
    if (sz.i == one)
      *out = cv_ty(ptr_to(T, isc));
    else if (sz.i == slc)
      *out = cv_ty(slice_of(T, isc));
    else
      *out = cv_ty(mptr_to(T, isc, hs, hs ? (int64_t)sn.i : 0));
    return R_OK;
  }
  if (B("Struct") || B("Union")) {
    int isu = B("Union");
    CVal lay;
    EVR(x, s, bt_type("Type.ContainerLayout"), &lay);
    CVal bk;
    EV(y, s, &bk);
    CVal names;
    EV(z, s, &names);
    CVal types;
    EV(n->list.a[3], s, &types);
    CVal attrs;
    EV(n->list.a[4], s, &attrs);
    int64_t len;
    if (!cv_len(&names, &len)) return R_FAIL;
    Container *ct = mk_container(isu ? TY_UNION : TY_STRUCT, isu ? "union" : "struct");
    int64_t lk_ext, lk_pk;
    enum_val(bt_type("Type.ContainerLayout"), "extern", &lk_ext);
    enum_val(bt_type("Type.ContainerLayout"), "packed", &lk_pk);
    ct->layout_kind = lay.i == lk_ext ? 1 : lay.i == lk_pk ? 2 : 0;
    if (!isu && ct->layout_kind == 2) ct->packed = -1;
    if (isu && bk.k == CV_TYPE) {
      ct->tagged = 1;
      ct->tag = bk.t;
    }
    if (!isu && bk.k == CV_TYPE) ct->packed = bk.t->bits;
    for (int64_t i = 0; i < len; i++) {
      CVal nm = cv_elem(&names, i);
      CVal ty = seq_at(&types, i);
      CVal at = seq_at(&attrs, i);
      Field *f = xalloc(sizeof *f);
      f->name = cv_cstr(&nm, NULL);
      if (ty.k != CV_TYPE) return R_FAIL;
      f->t = ty.t;
      CVal dp;
      if (agg_get(&at, "default_value_ptr", &dp) && dp.k == CV_PTR) {
        CVal *dc = deref_cell(&dp);
        if (dc) f->defcv = box(ccoerce(*dc, f->t));
      }
      vpush(&ct->fields, f);
    }
    if (isu && ct->tagged) {
      for (int i = 0; i < ct->fields.n; i++) {
        Field *f = ct->fields.a[i];
        int64_t v;
        if (enum_val(ct->tag, f->name, &v)) f->val = v;
      }
    }
    *out = cv_ty(ct->type);
    return R_OK;
  }
  if (B("Enum")) {
    TY(x, T);
    CVal mode;
    EVR(y, s, bt_type("Type.Enum.Mode"), &mode);
    CVal names;
    EV(z, s, &names);
    CVal vals;
    EV(n->list.a[3], s, &vals);
    int64_t len;
    if (!cv_len(&names, &len)) return R_FAIL;
    Container *ct = mk_container(TY_ENUM, "enum");
    ct->tag = T;
    int64_t nx;
    enum_val(bt_type("Type.Enum.Mode"), "nonexhaustive", &nx);
    ct->nonexh = mode.i == nx;
    for (int64_t i = 0; i < len; i++) {
      CVal nm = cv_elem(&names, i);
      CVal v = seq_at(&vals, i);
      Field *f = xalloc(sizeof *f);
      f->name = cv_cstr(&nm, NULL);
      f->val = (int64_t)v.i;
      f->t = T;
      vpush(&ct->fields, f);
    }
    ct->type->size = tsize(T);
    ct->type->align = talign(T);
    ct->laid = 1;
    *out = cv_ty(ct->type);
    return R_OK;
  }
  if (B("splat")) {
    EV(x, s, &a);
    if (urt && urt->k == TY_ARRAY) {
      CVal r = agg_new(urt);
      for (int i = 0; i < r.n; i++) *r.el[i] = ccoerce(cv_copy(a), urt->elem);
      *out = r;
      return R_OK;
    }
    *out = mk_splat(a);
    return R_OK;
  }
  if (B("tagName")) {
    EV(x, s, &a);
    if (a.k == CV_ENUMLIT) {
      *out = zstr(a.s);
      return R_OK;
    }
    if (a.k == CV_AGG && a.t->k == TY_UNION) {
      *out = zstr(field_at(a.t, (int)a.i)->name);
      return R_OK;
    }
    if (a.k != CV_INT) return R_FAIL;
    Type *t = cv_typeof(&a);
    if (t->k != TY_ENUM) return R_FAIL;
    layout(t->ct);
    for (int i = 0; i < t->ct->fields.n; i++) {
      Field *f = t->ct->fields.a[i];
      if (f->val == (int64_t)a.i) {
        *out = zstr(f->name);
        return R_OK;
      }
    }
    die("@tagName: invalid enum value");
  }
  if (B("errorName")) {
    EV(x, s, &a);
    if (a.k != CV_ERR) return R_FAIL;
    *out = zstr(errnames.a[a.i - 1]);
    return R_OK;
  }
  if (B("intFromError")) {
    EV(x, s, &a);
    if (a.k != CV_ERR) return R_FAIL;
    *out = cv_int(a.i, t_u16);
    return R_OK;
  }
  if (B("errorFromInt")) {
    EV(x, s, &a);
    CVal e = {0};
    e.k = CV_ERR;
    e.i = a.i;
    e.t = t_errset;
    *out = e;
    return R_OK;
  }
  if (B("errorCast")) return ev(x, s, out);
  if (B("unionInit")) {
    TY(x, T);
    EV(y, s, &b);
    char *nm = cv_cstr(&b, NULL);
    int fi = field_index(T, nm);
    if (fi < 0) return R_FAIL;
    CVal v;
    EVR(z, s, field_at(T, fi)->t, &v);
    *out = mk_union(T, nm, v);
    return R_OK;
  }
  if (B("ptrCast") || B("alignCast") || B("constCast") || B("volatileCast") || B("addrSpaceCast")) {
    CVal v;
    brt = rt;
    int r = ev_rt(x, s, NULL, &v);
    if (r != R_OK) return r;
    if (x->k == N_BUILTIN) { /* nested cast: re-evaluate with the result type */
    }
    if (v.k == CV_PTR || v.k == CV_SLICE || v.k == CV_NULL || v.k == CV_FN || v.k == CV_STR) {
      if (urt && (urt->k == TY_PTR || urt->k == TY_MPTR || urt->k == TY_SLICE || urt->k == TY_FN)) {
        if (v.k == CV_STR) {
          CVal p = {0};
          p.k = CV_PTR;
          p.base = box(v);
          p.idx = 0;
          p.t = urt;
          *out = p;
          return R_OK;
        }
        v.t = urt;
      }
      *out = v;
      return R_OK;
    }
    if (v.k == CV_INT && urt) {
      v.t = urt;
      *out = v;
      return R_OK;
    }
    return R_FAIL;
  }
  if (B("ptrFromInt")) {
    EV(x, s, &a);
    if (a.k != CV_INT || !urt) return R_FAIL;
    a.t = urt;
    *out = a;
    return R_OK;
  }
  if (B("intFromPtr")) {
    EV(x, s, &a);
    if (a.k == CV_INT) {
      *out = cv_int(a.i, t_usize);
      return R_OK;
    }
    return R_FAIL;
  }
  if (B("call")) {
    EV(y, s, &b);
    EV(z, s, &c);
    int64_t len;
    if (b.k != CV_FN || !cv_len(&c, &len)) return R_FAIL;
    if (!ct_force && !fn_returns_ctonly(b.fn)) return R_FAIL;
    CVal *args = xalloc(sizeof(CVal) * (len + 1));
    for (int64_t i = 0; i < len; i++) args[i] = cv_elem(&c, i);
    return ct_call(b.fn, args, (int)len, out);
  }
  if (B("memcpy") || B("memmove")) {
    if (!ct_force) return R_FAIL;
    EV(x, s, &a);
    EV(y, s, &b);
    int64_t len;
    if (!cv_len(&b, &len)) {
      if (!cv_len(&a, &len)) {
        Type *t = cv_typeof(&a);
        if (t->k == TY_PTR && t->elem->k == TY_ARRAY)
          len = t->elem->len;
        else
          return R_FAIL;
      }
    }
    CVal *tmp = xalloc(sizeof(CVal) * (len + 1));
    for (int64_t i = 0; i < len; i++) tmp[i] = cv_elem(&b, i);
    for (int64_t i = 0; i < len; i++) {
      CVal *cl = elem_cell(&a, i);
      if (!cl) return R_FAIL;
      assign(cl, tmp[i]);
    }
    *out = cv_void();
    return R_OK;
  }
  if (B("memset")) {
    if (!ct_force) return R_FAIL;
    EV(x, s, &a);
    EV(y, s, &b);
    int64_t len;
    if (!cv_len(&a, &len)) {
      Type *t = cv_typeof(&a);
      if (t->k == TY_PTR && t->elem->k == TY_ARRAY)
        len = t->elem->len;
      else
        return R_FAIL;
    }
    for (int64_t i = 0; i < len; i++) {
      CVal *cl = elem_cell(&a, i);
      if (!cl) return R_FAIL;
      assign(cl, b);
    }
    *out = cv_void();
    return R_OK;
  }
  if (B("divTrunc") || B("divFloor") || B("divExact") || B("mod") || B("rem") || B("shlExact") || B("shrExact")) {
    EV(x, s, &a);
    EV(y, s, &b);
    if (a.k != CV_INT || b.k != CV_INT) return R_FAIL;
    Type *t = peer_int(&a, &b);
    i128 p = a.i, q = b.i, r;
    if (B("shlExact"))
      r = p << q;
    else if (B("shrExact"))
      r = p >> q;
    else {
      if (!q) return R_FAIL;
      r = p / q;
      if (B("divFloor") && (p % q != 0) && ((p < 0) != (q < 0))) r--;
      if (B("mod")) {
        r = p % q;
        if (r != 0 && ((r < 0) != (q < 0))) r += q;
      }
      if (B("rem")) r = p % q;
    }
    *out = cv_int(wrap_int(r, t), t);
    return R_OK;
  }
  if (B("addWithOverflow") || B("subWithOverflow") || B("mulWithOverflow") || B("shlWithOverflow")) {
    EV(x, s, &a);
    EV(y, s, &b);
    if (a.k != CV_INT || b.k != CV_INT) return R_FAIL;
    Type *t = cv_typeof(&a);
    if (t->k == TY_CINT) t = cv_typeof(&b);
    i128 r = b0[0] == 'a'                   ? a.i + b.i
             : b0[0] == 's' && b0[1] == 'u' ? a.i - b.i
             : b0[0] == 'm'                 ? a.i * b.i
                                            : (b.i >= 127 ? 0 : a.i << b.i);
    *out = ovf_tuple(r, t);
    return R_OK;
  }
  if (B("floatFromInt")) {
    EV(x, s, &a);
    if (a.k != CV_INT && a.k != CV_FLOAT) return R_FAIL;
    Type *t = urt && is_float(urt) ? urt : t_cfloat;
    *out = cv_float(fround(a.k == CV_INT ? (f128)a.i : a.f, t), t);
    return R_OK;
  }
  if (B("intFromFloat")) {
    EV(x, s, &a);
    if (a.k != CV_FLOAT && a.k != CV_INT) return R_FAIL;
    Type *t = urt && is_int(urt) ? urt : t_cint;
    if (a.k == CV_INT) {
      *out = cv_int(a.i, t);
      return R_OK;
    }
    if (f128_isnan(a.f) || f128_isinf(a.f)) {
      if (ct_force) die("%s:%d: @intFromFloat of non-finite value", n->tok->file, n->tok->line);
      return R_FAIL;
    }
    *out = cv_int(wrap_int((i128)a.f, t), t);
    return R_OK;
  }
  if (B("floatCast")) {
    EV(x, s, &a);
    if (a.k != CV_FLOAT && a.k != CV_INT) return R_FAIL;
    Type *t = urt && is_float(urt) ? urt : cv_typeof(&a);
    *out = cv_float(fround(a.k == CV_INT ? (f128)a.i : a.f, t), t);
    return R_OK;
  }
  if (B("sqrt") || B("sin") || B("cos") || B("tan") || B("exp") || B("exp2") || B("exp10") || B("log") || B("log2") ||
      B("log10") || B("floor") || B("ceil") || B("trunc") || B("round") || (B("abs") && 0)) {
    EV(x, s, &a);
    if (a.k == CV_AGG && a.t->k == TY_ARRAY) return R_FAIL;
    if (a.k != CV_FLOAT) return R_FAIL;
    f128 f = a.f, r;
    long double lf = (long double)f;
    if (B("sqrt"))
      r = f128_sqrt(f);
    else if (B("sin"))
      r = sinl(lf);
    else if (B("cos"))
      r = cosl(lf);
    else if (B("tan"))
      r = tanl(lf);
    else if (B("exp"))
      r = expl(lf);
    else if (B("exp2"))
      r = exp2l(lf);
    else if (B("exp10"))
      r = powl(10, lf);
    else if (B("log"))
      r = logl(lf);
    else if (B("log2"))
      r = log2l(lf);
    else if (B("log10"))
      r = log10l(lf);
    else if (B("floor"))
      r = f128_floor(f);
    else if (B("ceil"))
      r = f128_ceil(f);
    else if (B("trunc"))
      r = f128_trunc(f);
    else
      r = f128_round(f);
    Type *t = cv_typeof(&a);
    *out = cv_float(fround(r, t), t);
    return R_OK;
  }
  if (B("mulAdd")) {
    TY(x, T);
    CVal c3;
    EVR(y, s, T, &a);
    EVR(n->list.a[2], s, T, &b);
    EVR(n->list.a[3], s, T, &c3);
    if (a.k != CV_FLOAT || b.k != CV_FLOAT || c3.k != CV_FLOAT) return R_FAIL;
    *out = cv_float(fround(a.f * b.f + c3.f, T), T);
    return R_OK;
  }
  if (B("abs") && x) {
    EV(x, s, &a);
    if (a.k == CV_FLOAT) {
      *out = cv_float(a.f < 0 || (a.f == 0 && signbit((double)a.f)) ? -a.f : a.f, cv_typeof(&a));
      return R_OK;
    }
  }
  if (B("abs")) {
    EV(x, s, &a);
    if (a.k != CV_INT) return R_FAIL;
    Type *t = cv_typeof(&a);
    Type *ut = t->k == TY_INT && t->sign ? int_type(t->bits, 0) : t;
    *out = cv_int(a.i < 0 ? -a.i : a.i, ut);
    return R_OK;
  }
  if (B("clz") || B("ctz") || B("popCount") || B("byteSwap") || B("bitReverse")) {
    EV(x, s, &a);
    if (a.k == CV_AGG) return R_FAIL;
    if (a.k != CV_INT) return R_FAIL;
    Type *t = cv_typeof(&a);
    if (t->k != TY_INT) return R_FAIL;
    int bits = t->bits;
    i128 u = a.i & umask(bits);
    i128 r = 0;
    if (B("clz")) {
      r = bits;
      for (int i = bits - 1; i >= 0; i--)
        if ((u >> i) & 1) {
          r = bits - 1 - i;
          break;
        }
      *out = cv_int(r, int_type(log2_bits(bits), 0));
      return R_OK;
    }
    if (B("ctz")) {
      r = bits;
      for (int i = 0; i < bits; i++)
        if ((u >> i) & 1) {
          r = i;
          break;
        }
      *out = cv_int(r, int_type(log2_bits(bits), 0));
      return R_OK;
    }
    if (B("popCount")) {
      for (int i = 0; i < bits; i++) r += (u >> i) & 1;
      *out = cv_int(r, int_type(log2_bits(bits), 0));
      return R_OK;
    }
    if (B("byteSwap")) {
      for (int i = 0; i < bits / 8; i++) r |= ((u >> (8 * i)) & 0xff) << (8 * (bits / 8 - 1 - i));
    } else
      for (int i = 0; i < bits; i++)
        if ((u >> i) & 1) r |= (i128)1 << (bits - 1 - i);
    *out = cv_int(wrap_int(r, t), t);
    return R_OK;
  }
  if (B("reduce")) {
    CVal op;
    EVR(x, s, bt_type("ReduceOp"), &op);
    EV(y, s, &b);
    if (b.k != CV_AGG || op.k != CV_INT) return R_FAIL;
    Container *rc = bt_type("ReduceOp")->ct;
    layout(rc);
    const char *on = NULL;
    for (int i = 0; i < rc->fields.n; i++) {
      Field *f = rc->fields.a[i];
      if (f->val == (int64_t)op.i) on = f->name;
    }
    CVal acc = *b.el[0];
    for (int i = 1; i < b.n; i++) {
      CVal e = *b.el[i];
      const char *bop = !strcmp(on, "And")   ? "&"
                        : !strcmp(on, "Or")  ? "|"
                        : !strcmp(on, "Xor") ? "^"
                        : !strcmp(on, "Add") ? "+%"
                        : !strcmp(on, "Mul") ? "*%"
                                             : NULL;
      if (bop) {
        if (acc.k == CV_BOOL) {
          if (bop[0] == '&')
            acc.i &= e.i;
          else if (bop[0] == '|')
            acc.i |= e.i;
          else
            acc.i ^= e.i;
        } else if (ev_bin(bop, acc, e, &acc) != R_OK)
          return R_FAIL;
      } else if (!strcmp(on, "Min")) {
        if (e.i < acc.i) acc = e;
      } else if (e.i > acc.i)
        acc = e;
    }
    *out = acc;
    return R_OK;
  }
  if (B("select")) {
    TY(x, T);
    CVal pr;
    EV(y, s, &pr);
    EV(z, s, &a);
    EV(n->list.a[3], s, &b);
    if (pr.k != CV_AGG) return R_FAIL;
    CVal r = agg_new(vec_of(T, pr.n));
    for (int i = 0; i < pr.n; i++) *r.el[i] = pr.el[i]->i ? seq_at(&a, i) : seq_at(&b, i);
    *out = r;
    return R_OK;
  }
  if (B("shuffle")) {
    TY(x, T);
    EV(y, s, &a);
    EV(z, s, &b);
    CVal mk;
    EV(n->list.a[3], s, &mk);
    int64_t ml;
    if (!cv_len(&mk, &ml)) return R_FAIL;
    CVal r = agg_new(vec_of(T, ml));
    for (int64_t i = 0; i < ml; i++) {
      CVal m = cv_elem(&mk, i);
      if (m.k == CV_UNDEF) {
        *r.el[i] = cv_undef(T);
        continue;
      }
      int64_t k = (int64_t)m.i;
      *r.el[i] = k >= 0 ? seq_at(&a, k) : seq_at(&b, ~k);
    }
    *out = r;
    return R_OK;
  }
  if (B("src")) {
    Type *st = bt_type("SourceLocation");
    CVal v = mk_struct(st);
    setf(&v, "module", zstr("root"));
    setf(&v, "file", zstr(n->tok->file));
    setf(&v, "fn_name", zstr("?"));
    setf(&v, "line", cv_int(n->tok->line, t_u32));
    setf(&v, "column", cv_int(1, t_u32));
    *out = v;
    return R_OK;
  }
  return R_FAIL;
}
