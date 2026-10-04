#include "gen_int.h"

int is_bigf(Type *t) {
  return t->k == TY_FLOAT && t->bits > 64;
}
Val bigf_conv(Val v, Type *f, Type *to) {
  char *o = opnd(v);
  if (f->k == TY_BOOL) {
    v = coerce(v, t_u8);
    f = t_u8;
    o = opnd(v);
  }
  if (is_bigf(f) && is_bigf(to)) {
    if (f->bits == to->bits) return V(to, o);
    char *sl = slot(to);
    emit("call $zb_fconv(w %d, l %s, w %d, l %s)", to->bits, sl, f->bits, o);
    return V(to, sl);
  }
  if (is_bigf(f) && to->k == TY_FLOAT) {
    char *r = tmp();
    emit("%s =%c call $zb_fto%d(w %d, l %s)", r, qc(to), qc(to) == 's' ? 32 : 64, f->bits, o);
    return V(to, r);
  }
  if (f->k == TY_FLOAT && is_bigf(to)) {
    char *x = o;
    if (qc(f) == 's') {
      x = tmp();
      emit("%s =d exts %s", x, o);
    }
    char *sl = slot(to);
    emit("call $zb_fext(w %d, l %s, d %s)", to->bits, sl, x);
    return V(to, sl);
  }
  if (is_bigf(f) && to->k == TY_INT) {
    if (is_wide(to)) {
      if (to->bits > 128) die("f%d -> %s unsupported", f->bits, tname(to));
      char *sl = slot(to);
      emit("call $zb_toi128(w %d, l %s, l %s, w %d)", f->bits, sl, o, to->sign);
      return V(to, sl);
    }
    char *r = tmp();
    emit("%s =l call $zb_toi(w %d, l %s, w %d)", r, f->bits, o, to->sign);
    if (qc(to) == 'w') {
      char *r2 = tmp();
      emit("%s =w copy %s", r2, r);
      return V(to, norm(r2, to));
    }
    return V(to, r);
  }
  if (f->k == TY_INT && is_bigf(to)) {
    char *sl = slot(to);
    if (is_wide(f)) {
      if (f->bits > 128) die("%s -> f%d unsupported", tname(f), to->bits);
      emit("call $zb_fromi128(w %d, l %s, l %s, w %d)", to->bits, sl, o, f->sign);
      return V(to, sl);
    }
    char *x = o;
    if (qc(f) == 'w') {
      x = tmp();
      emit("%s =l ext%sw %s", x, f->sign ? "s" : "u", o);
    }
    emit("call $zb_fromi(w %d, l %s, l %s, w %d)", to->bits, sl, x, f->sign);
    return V(to, sl);
  }
  die("bad float conversion %s -> %s", tname(f), tname(to));
}
char *bigf_op(int op, Type *t, char *a, char *b) {
  char *sl = slot(t);
  emit("call $zb_fop(w %d, w %d, l %s, l %s, l %s)", t->bits, op, sl, a, b ? b : "0");
  return sl;
}
Val float_conv(Val v, Type *to) { /* float -> float, int -> float, float -> int at runtime */
  v = rv(v);
  Type *f = v.t;
  if (v.ck) {
    CVal c = v.cv;
    if (c.k == CV_INT && is_float(to)) c = cv_float((f128)c.i, to);
    if (c.k == CV_FLOAT && is_float(to)) return CK(cv_float(fround(c.f, to), to));
    if (c.k == CV_FLOAT && to->k == TY_INT) return CK(cv_int(wrap_int((i128)c.f, to), to));
    if (c.k == CV_INT && to->k == TY_INT) return CK(cv_int(wrap_int(c.i, to), to));
    if (f->k == TY_CINT) {
      v = coerce(v, t_i64);
      f = t_i64;
    } else if (f->k == TY_CFLOAT) {
      v = coerce(v, t_f64);
      f = t_f64;
    }
  }
  if (is_bigf(f) || is_bigf(to)) return bigf_conv(v, f, to);
  char *o = opnd(v), *r = tmp();
  if (f->k == TY_FLOAT && to->k == TY_FLOAT) {
    if (qc(f) == qc(to)) return V(to, o);
    emit("%s =%c %s %s", r, qc(to), qc(to) == 'd' ? "exts" : "truncd", o);
    return V(to, r);
  }
  if (f->k == TY_FLOAT && to->k == TY_INT) {
    if (is_wide(to)) {
      char *q = tmp();
      int s4 = qc(f) == 's';
      emit("%s =:zbw call $%s(%c %s)", q,
           to->sign ? (s4 ? "__fixsfti" : "__fixdfti") : (s4 ? "__fixunssfti" : "__fixunsdfti"), qc(f), o);
      return w_from_parts(to, load(t_u64, q), load(t_u64, addp(q, 8)));
    }
    int u = !to->sign;
    char c = qc(to);
    if (to->bits < 32 || (u && to->bits == 32)) {
      char *t2 = tmp();
      emit("%s =l %ctosi %s", t2, qc(f), o);
      if (c == 'w') {
        emit("%s =w copy %s", r, t2);
        return V(to, norm(r, to));
      }
      return V(to, t2);
    }
    emit("%s =%c %cto%ci %s", r, c, qc(f), u ? 'u' : 's', o);
    return V(to, r);
  }
  if ((f->k == TY_INT || f->k == TY_BOOL) && to->k == TY_FLOAT) {
    if (is_wide(f)) {
      int s4 = qc(to) == 's';
      emit("%s =%c call $%s(l %s, l %s)", r, qc(to),
           f->sign ? (s4 ? "__floattisf" : "__floattidf") : (s4 ? "__floatuntisf" : "__floatuntidf"), wlo(v), whi(v));
      return V(to, r);
    }
    if (f->k == TY_BOOL) f = t_u8;
    int u = !f->sign;
    if (qc(f) == 'w' && f->bits < 32) {
      emit("%s =%c %s %s", r, qc(to), "swtof", o);
      return V(to, r);
    }
    emit("%s =%c %c%ctof %s", r, qc(to), u ? 'u' : 's', qc(f), o);
    return V(to, r);
  }
  die("bad float conversion %s -> %s", tname(f), tname(to));
}

/* 0.17 @bitCast: logical bit representation for arrays/vectors with padded elements */
int lbits(Type *t) {
  if (t->k == TY_ARRAY) return (int)(lbits(t->elem) * t->len);
  return bits_of(t);
}
int lpadded(Type *t) {
  if (t->k != TY_ARRAY) return 0;
  return lpadded(t->elem) || bits_of(t->elem) != 8 * tsize(t->elem) || t->elem->k == TY_ARRAY;
}
void lwalk(Type *t, char *addr, char *buf, int64_t *off, int put) {
  if (t->k == TY_ARRAY) {
    for (int64_t i = 0; i < t->len; i++) lwalk(t->elem, addp(addr, i * tsize(t->elem)), buf, off, put);
    return;
  }
  int nb = bits_of(t), sz = tsize(t), sg = t->k == TY_INT && t->sign;
  for (int c = 0; c * 64 < nb; c++) {
    int n = nb - c * 64 > 64 ? 64 : nb - c * 64, bytes = sz - c * 8 >= 8 ? 8 : sz - c * 8;
    char *a = addp(addr, c * 8);
    if (put) {
      char *r = tmp(), *v = tmp();
      emit("%s =l %s %s", r, bytes == 8 ? "loadl" : bytes >= 4 ? "loaduw" : bytes == 2 ? "loaduh" : "loadub", a);
      if (bytes == 4 || bytes == 2 || bytes == 1)
        emit("%s =l copy %s", v, r);
      else
        v = r;
      emit("call $zb_bitput(l %s, l %lld, l %s, w %d)", buf, (long long)*off, v, n);
    } else {
      char *r = tmp();
      emit("%s =l call $zb_bitget(l %s, l %lld, w %d)", r, buf, (long long)*off, n);
      if (sg && n < 64 && c * 64 + n == nb) {
        char *q = tmp(), *w = tmp();
        emit("%s =l shl %s, %d", q, r, 64 - n);
        emit("%s =l sar %s, %d", w, q, 64 - n);
        r = w;
      }
      if (bytes == 8)
        emit("storel %s, %s", r, a);
      else if (bytes >= 4)
        emit("storew %s, %s", r, a);
      else if (bytes == 2)
        emit("storeh %s, %s", r, a);
      else
        emit("storeb %s, %s", r, a);
    }
    *off += n;
  }
}
Val lbitcast(Val v, Type *ex) {
  char *src;
  if (is_aggr(v.t))
    src = addr_of(v);
  else {
    src = slot(v.t);
    store(v.t, opnd(v), src);
  }
  int64_t nb = lbits(ex), bb = (nb + 7) / 8 + 8;
  char *buf = tmp();
  emit("%s =l alloc8 %lld", buf, (long long)((bb + 7) & ~7));
  int64_t off = 0;
  lwalk(v.t, src, buf, &off, 1);
  char *sl = slot(ex);
  emit("call $memset(l %s, w 0, l %d)", sl, tsize(ex));
  off = 0;
  lwalk(ex, sl, buf, &off, 0);
  return is_aggr(ex) ? V(ex, sl) : V(ex, load(ex, sl));
}
void note_err(Type *S, Val v) {
  if (!v.t) return;
  if (v.ck && v.cv.k == CV_ERR && v.cv.t && v.cv.t->k == TY_ERRSET && v.cv.t->ct) {
    eset_add_set(S, v.cv.t);
    return;
  }
  if (v.ck && v.cv.k == CV_ERR) {
    if (v.cv.i > 0 && v.cv.i <= errnames.n) eset_add_name(S, errnames.a[v.cv.i - 1]);
    return;
  }
  if (v.t->k == TY_ERRSET)
    eset_add_set(S, v.t);
  else if (v.t->k == TY_ERRU)
    eset_add_set(S, eset_of(v.t));
}
Val coerce(Val v, Type *to) {
  if (!to || v.t == to) return v;
  if (!v.ck && v.t && v.t->k == TY_ARRAY && to->k == TY_ARRAY && v.t->len == to->len && v.t->elem != to->elem &&
      (is_vec(v.t) || is_vec(to)) && (v.t->elem->k == TY_INT || v.t->elem->k == TY_FLOAT) &&
      (to->elem->k == TY_INT || to->elem->k == TY_FLOAT)) { /* elementwise vector widening */
    v = rv(v);
    char *sl = slot(to), *pa = addr_of(v);
    for (int64_t i = 0; i < to->len; i++) {
      Val e = rv(LV(v.t->elem, addp(pa, i * tsize(v.t->elem))));
      put(coerce(e, to->elem), to->elem, addp(sl, i * tsize(to->elem)));
    }
    return V(to, sl);
  }
  if (to->k == TY_ERRU && is_inferred_eset(to->ret))
    note_err(to->ret, v);
  else if (is_inferred_eset(to))
    note_err(to, v);
  if (v.ck && v.cv.k == CV_SLICE && v.t && v.t->k == TY_SLICE && to->k == TY_PTR && to->elem->k == TY_ARRAY &&
      to->elem->len == v.cv.slen && to->elem->elem == v.t->elem) {
    int64_t off;
    char *sym = ptr_parts(&v.cv, &off);
    if (sym) return V(to, addp(sym, off));
  } /* 0.17: comptime-length slice -> *[N]T */
  if (v.ck && v.cv.k == CV_AGG && is_tuple_type(v.t) &&
      (to->k == TY_STRUCT || to->k == TY_TUPLE || to->k == TY_ARRAY) && !is_packed(to)) {
    int any = 0;
    if (is_tuple_type(to)) {
      layout(to->ct);
      for (int i = 0; i < to->ct->fields.n; i++)
        if (((Field *)to->ct->fields.a[i])->t->k == TY_ANYTYPE) any = 1;
    }
    if (!any) {
      CVal c = ccoerce(v.cv, to);
      if (c.k == CV_AGG && c.t == to) {
        Val r = CK(c);
        r.t = to;
        return r;
      }
    }
  }
  if (is_tuple_type(to) && is_tuple_type(v.t) &&
      v.t->k != TY_NORET) { /* partially typed tuple hint: anytype fields take the value's types */
    layout(to->ct);
    int any = 0;
    for (int i = 0; i < to->ct->fields.n; i++)
      if (((Field *)to->ct->fields.a[i])->t->k == TY_ANYTYPE) any = 1;
    if (any) {
      layout(v.t->ct);
      if (v.t->ct->fields.n != to->ct->fields.n) return v;
      Vec nm = {0}, ty = {0};
      for (int i = 0; i < to->ct->fields.n; i++) {
        Type *tt = ((Field *)to->ct->fields.a[i])->t;
        Type *ft = ((Field *)v.t->ct->fields.a[i])->t;
        vpush(&nm, fmt("%d", i));
        vpush(&ty, tt->k == TY_ANYTYPE ? (ft->k == TY_CINT ? t_i64 : ft->k == TY_CFLOAT ? t_f64 : ft) : tt);
      }
      to = mk_anon_struct(&nm, &ty, 1);
      if (v.t == to) return v;
    }
  }
  if (!v.ck && v.t->k == TY_SLICE && to->k == TY_PTR && to->elem->k == TY_ARRAY && to->elem->elem == v.t->elem)
    return V(to, load(t_u64, addr_of(v)));
  if (!v.ck && v.t->k == TY_ARRAY && to->k == TY_ARRAY && (is_vec(v.t) || is_vec(to)) && v.t->len == to->len &&
      v.t->elem == to->elem) {
    v = rv(v);
    v.t = to;
    return v;
  }
  Type *f = v.t;
  if (f->k == TY_NORET || to->k == TY_ANYTYPE) return v;
  if (v.ck) {
    CVal r = ccoerce(v.cv, to);
    if (ck_ok(&r, to)) {
      Val o = CK(r);
      o.t = to;
      if (r.k == CV_VOID) {
        o.ck = 0;
        o.op = "0";
      }
      return o;
    }
  }
  if (v.ck) {
    CVal c = v.cv;
    switch (c.k) {
    case CV_UNDEF: {
      Val r = v;
      r.t = to;
      return r;
    }
    case CV_INT:
      if (to->k == TY_INT || to->k == TY_CINT) {
        c.t = to;
        c.i = wrap_int(c.i, to);
        return CK(c);
      }
      if (to->k == TY_ENUM && f->k == TY_ENUM) {
        c.t = to;
        return CK(c);
      }
      break;
    case CV_ENUMLIT:
      if (to->k == TY_ENUM) {
        int64_t x;
        if (!enum_val(to, c.s, &x)) die("no field .%s in %s", c.s, tname(to));
        CVal r = {0};
        r.k = CV_INT;
        r.i = x;
        r.t = to;
        return CK(r);
      }
      if (to->k == TY_UNION && to->ct->tagged) {
        int64_t x;
        enum_val(to, c.s, &x);
        char *sl = slot(to);
        char tv[32];
        snprintf(tv, 32, "%lld", (long long)x);
        store(to->ct->tag, tv, addp(sl, union_tag_off(to)));
        return V(to, sl);
      }
      break;
    case CV_NULL:
      if (to->k == TY_OPT) {
        if (opt_is_ptr(to)) {
          Val r = v;
          r.t = to;
          return r;
        }
        Val r = v;
        r.t = to;
        return V(to, addr_of(r));
      }
      break;
    case CV_ERR:
      if (to->k == TY_ERRSET) {
        Val r = v;
        r.t = to;
        return r;
      }
      if (to->k == TY_ERRU) {
        char *sl = slot(to);
        store(t_u16, mat(v), sl);
        return V(to, sl);
      }
      break;
    case CV_STR: {
      char *p = mat(v);
      if (to->k == TY_SLICE) {
        char *sl = slot(to);
        store(t_u64, p, sl);
        store(t_u64, fmt("%d", c.slen), addp(sl, 8));
        return V(to, sl);
      }
      if (to->k == TY_MPTR || to->k == TY_PTR || to->k == TY_ARRAY) return V(to, p);
      if (to->k == TY_OPT) break;
      break;
    }
    case CV_FN:
      if (to->k == TY_FN || to->k == TY_PTR) return V(to, mat(v));
      break;
    case CV_BOOL:
      if (to->k == TY_BOOL) return v;
      break;
    case CV_TYPE:
      if (to->k == TY_TYPE) return v;
      break;
    }
  }
  if (to->k == TY_OPT) {
    if (f->k == TY_OPT && opt_is_ptr(f) == opt_is_ptr(to)) {
      v.t = to;
      return v;
    }
    if (f->k == TY_NULL) {
      CVal c = {0};
      c.k = CV_NULL;
      return coerce(CK(c), to);
    }
    Val pv = coerce(v, to->elem);
    if (opt_is_ptr(to)) return retype(pv, to);
    char *sl = slot(to);
    put(pv, to->elem, sl);
    store(t_u8, "1", addp(sl, tsize(to->elem)));
    return V(to, sl);
  }
  if (to->k == TY_ERRU) {
    if (f->k == TY_ERRU) {
      v.t = to;
      return v;
    }
    if (f->k == TY_ERRSET) {
      char *sl = slot(to);
      store(t_u16, opnd(v), sl);
      return V(to, sl);
    }
    Val pv = coerce(v, to->elem);
    char *sl = slot(to);
    store(t_u16, "0", sl);
    if (to->elem != t_void) put(pv, to->elem, addp(sl, erru_off(to)));
    return V(to, sl);
  }
  if (to->k == TY_INT && f->k == TY_INT && (is_wide(f) || is_wide(to))) return wconv(v, to);
  if (to->k == TY_INT && f->k == TY_INT) {
    char *o = opnd(v);
    if (qc(f) == 'w' && qc(to) == 'l') {
      char *r = tmp();
      emit("%s =l %s %s", r, f->sign ? "extsw" : "extuw", o);
      return V(to, r);
    }
    if (qc(f) == 'l' && qc(to) == 'w') {
      char *r = tmp();
      emit("%s =w copy %s", r, o);
      return V(to, norm(r, to));
    }
    if (to->bits < f->bits) return V(to, norm(o, to));
    return V(to, o);
  }
  if (to->k == TY_INT && f->k == TY_BOOL) return retype(v, to);
  if (to->k == TY_FLOAT && f->k == TY_FLOAT) return float_conv(v, to);
  if (to->k == TY_SLICE && f->k == TY_PTR && f->elem->k == TY_ARRAY) {
    char *p = opnd(v), *sl = slot(to);
    store(t_u64, p, sl);
    store(t_u64, fmt("%lld", (long long)f->elem->len), addp(sl, 8));
    return V(to, sl);
  }
  if (to->k == TY_SLICE && f->k == TY_SLICE) {
    v.t = to;
    return v;
  }
  if (to->k == TY_MPTR && f->k == TY_SLICE) return V(to, load(t_u64, addr_of(v)));
  if (is_ptrish(to) && is_ptrish(f)) return retype(v, to);
  if (to->k == TY_ERRSET && f->k == TY_ERRSET) return retype(v, to);
  if (to->k == TY_ENUM && f->k == TY_UNION && f->ct->tagged) return V(to, load(to, addp(addr_of(v), union_tag_off(f))));
  if (to->k == TY_UNION && f->k == TY_ENUM) {
    char *sl = slot(to);
    store(to->ct->tag, opnd(v), addp(sl, union_tag_off(to)));
    return V(to, sl);
  }
  if (to->k == TY_ARRAY && f->k == TY_ARRAY && to->len == f->len) {
    v.t = to;
    return v;
  }
  if (to->k == TY_ARRAY && f->k == TY_PTR && f->elem->k == TY_ARRAY) return V(to, opnd(v));
  if (to->k == TY_ENUM && f->k == TY_ENUM) return retype(v, to);
  if (f->k == TY_UNDEF) {
    v.t = to;
    return v;
  }
  if ((f->k == TY_STRUCT || f->k == TY_TUPLE) && (to->k == TY_STRUCT || to->k == TY_TUPLE || to->k == TY_ARRAY) &&
      (is_anon(f) || is_tuple_type(f))) {
    /* anonymous struct / tuple -> struct, tuple or array, field by field */
    layout(f->ct);
    if (to->ct) layout(to->ct);
    char *src = addr_of(v), *sl = slot(to);
    int tup = is_tuple_type(f);
    char *set = xalloc((to->k == TY_ARRAY ? to->len : to->ct->fields.n) + 1);
    for (int i = 0; i < f->ct->fields.n; i++) {
      Field *ff = f->ct->fields.a[i];
      Type *tt;
      int off;
      if (to->k == TY_ARRAY) {
        tt = to->elem;
        off = i * tsize(tt);
        set[i] = 1;
      } else {
        Field *tf = tup && is_tuple_type(to) ? (i < to->ct->fields.n ? to->ct->fields.a[i] : NULL)
                                             : find_field(to->ct, ff->name);
        if (!tf) continue;
        tt = tf->t;
        off = tf->off;
        for (int j = 0; j < to->ct->fields.n; j++)
          if (to->ct->fields.a[j] == tf) set[j] = 1;
      }
      Val e = coerce(ff->is_ct ? CK(*(CVal *)ff->defcv) : rv(LV(ff->t, addp(src, ff->off))), tt);
      put(e, tt, addp(sl, off));
    }
    if (to->k != TY_ARRAY)
      for (int j = 0; j < to->ct->fields.n; j++) {
        Field *tf = to->ct->fields.a[j];
        if (!set[j] && (tf->def || tf->defcv)) {
          CVal dv;
          if (tf->defcv)
            dv = *(CVal *)tf->defcv;
          else if (!ceval_ex(tf->def, to->ct->scope, tf->t, &dv))
            continue;
          put(coerce(CK(dv), tf->t), tf->t, addp(sl, tf->off));
        }
      }
    return V(to, sl);
  }
  if ((to->k == TY_SLICE || (to->k == TY_PTR && to->elem->k == TY_ARRAY)) && f->k == TY_PTR &&
      is_tuple_type(f->elem)) { /* &tuple -> slice / *[n]T */
    layout(f->elem->ct);
    int64_t nn = f->elem->ct->fields.n;
    Type *at = to->k == TY_SLICE ? array_of(to->elem, nn, 0, 0) : to->elem;
    Val av = coerce(rv(LV(f->elem, opnd(v))), at);
    char *p = addr_of(av);
    if (to->k == TY_PTR) return V(to, p);
    char *sl = slot(to);
    store(t_u64, p, sl);
    store(t_u64, fmt("%lld", (long long)nn), addp(sl, 8));
    return V(to, sl);
  }
  if (f->k == TY_ARRAY && is_tuple_type(to)) { /* array -> tuple, element-wise */
    layout(to->ct);
    char *src = addr_of(v), *sl = slot(to);
    for (int i = 0; i < to->ct->fields.n && i < f->len; i++) {
      Field *tf = to->ct->fields.a[i];
      Val e = coerce(rv(LV(f->elem, addp(src, (int64_t)i * tsize(f->elem)))), tf->t);
      put(e, tf->t, addp(sl, tf->off));
    }
    return V(to, sl);
  }
  if (to->k == TY_SLICE && f->k == TY_ARRAY && to->isconst) { /* array rvalue -> const slice of a temporary */
    char *p = addr_of(v), *sl = slot(to);
    store(t_u64, p, sl);
    store(t_u64, fmt("%lld", (long long)f->len), addp(sl, 8));
    return V(to, sl);
  }
  {
    extern Node *gen_cur_pub(void);
    Node *cn = gen_cur_pub();
    die("%s:%d: cannot coerce %s to %s", cn ? cn->tok->file : "?", cn ? cn->tok->line : 0, tname(f), tname(to));
  }
}
Type *peer(Val a, Val b) {
  if (a.t->k == TY_CINT && a.ck) return b.t;
  if (b.t->k == TY_CINT && b.ck) return a.t;
  if (a.t->k == TY_ENUMLIT) return b.t;
  if (b.t->k == TY_ENUMLIT) return a.t;
  if (a.t == b.t) return a.t;
  if (a.t->k == TY_INT && b.t->k == TY_INT) return a.t->bits >= b.t->bits ? a.t : b.t;
  if (a.t->k == TY_CFLOAT && a.ck) return b.t->k == TY_INT ? a.t : b.t;
  if (b.t->k == TY_CFLOAT && b.ck) return a.t->k == TY_INT ? b.t : a.t;
  if (a.t->k == TY_FLOAT && b.t->k == TY_FLOAT) return a.t->bits >= b.t->bits ? a.t : b.t;
  if (a.t->k == TY_NULL) return b.t;
  if (b.t->k == TY_NULL) return a.t;
  if (b.t->k == TY_OPT && a.t->k != TY_OPT) return b.t;
  return a.t;
}
int ptr_to_empty(Type *t) {
  return t->k == TY_PTR && ((t->elem->k == TY_ARRAY && t->elem->len == 0) ||
                            (is_tuple_type(t->elem) && (layout(t->elem->ct), t->elem->ct->fields.n == 0)));
}
Type *peer_eset(Type *a, Type *b) {
  if (a == b) return a;
  if (a == t_errset || b == t_errset || is_inferred_eset(a) || is_inferred_eset(b) || !a->ct || !b->ct) return t_errset;
  return errset_merge(a, b);
}
Type *peer_t(Type *a, Type *b) {
  if (!a) return b;
  if (!b) return a;
  if (a == b) return a;
  if (ptr_to_empty(a) && b->k == TY_SLICE) return b;
  if (ptr_to_empty(b) && a->k == TY_SLICE) return a;
  if (a->k == TY_NORET) return b;
  if (b->k == TY_NORET) return a;
  if (a->k == TY_ENUMLIT && b->k == TY_ENUMLIT) return a;
  if (a->k == TY_ENUMLIT &&
      (b->k == TY_ENUM || b->k == TY_UNION || (b->k == TY_OPT && (b->elem->k == TY_ENUM || b->elem->k == TY_UNION))))
    return b;
  if (b->k == TY_ENUMLIT &&
      (a->k == TY_ENUM || a->k == TY_UNION || (a->k == TY_OPT && (a->elem->k == TY_ENUM || a->elem->k == TY_UNION))))
    return a;
  if (a->k == TY_ERRSET && b->k == TY_ERRSET) return a;
  if (a->k == TY_ERRSET && b->k == TY_ERRSET) return peer_eset(a, b);
  if (a->k == TY_ERRSET) return b->k == TY_ERRU ? erru_of2(b->elem, peer_eset(a, eset_of(b))) : erru_of2(b, a);
  if (b->k == TY_ERRSET) return a->k == TY_ERRU ? erru_of2(a->elem, peer_eset(b, eset_of(a))) : erru_of2(a, b);
  if (a->k == TY_ERRU || b->k == TY_ERRU) {
    Type *e = peer_t(a->k == TY_ERRU ? a->elem : a, b->k == TY_ERRU ? b->elem : b);
    Type *es =
        a->k == TY_ERRU && b->k == TY_ERRU ? peer_eset(eset_of(a), eset_of(b)) : eset_of(a->k == TY_ERRU ? a : b);
    return e ? erru_of2(e, es) : NULL;
  }
  if (a->k == TY_CINT && (b->k == TY_INT)) return b;
  if (b->k == TY_CINT && a->k == TY_INT) return a;
  if (a->k == TY_INT && b->k == TY_INT) {
    if (a->sign == b->sign) return a->bits >= b->bits ? a : b;
    Type *sg = a->sign ? a : b, *us = a->sign ? b : a;
    return sg->bits > us->bits ? sg : int_type(us->bits + 1, 1);
  }
  if (a->k == TY_NULL) return b->k == TY_OPT ? b : opt_of(b);
  if (b->k == TY_NULL) return a->k == TY_OPT ? a : opt_of(a);
  if (a->k == TY_OPT && a->elem == b) return a;
  if (b->k == TY_OPT && b->elem == a) return b;
  if (a->k == TY_ERRU && a->elem == b) return a;
  if (b->k == TY_ERRU && b->elem == a) return b;
  if (a->k == TY_CFLOAT && b->k == TY_FLOAT) return b;
  if (b->k == TY_CFLOAT && a->k == TY_FLOAT) return a;
  if (a->k == TY_CINT && is_float(b)) return b;
  if (b->k == TY_CINT && is_float(a)) return a;
  if (a->k == TY_FLOAT && b->k == TY_FLOAT) return a->bits >= b->bits ? a : b;
  if (a->k == TY_UNDEF) return b;
  if (b->k == TY_UNDEF) return a;
  { /* pointers to arrays of differing lengths / slices with the same element type -> slice */
    int pa = a->k == TY_PTR && a->elem->k == TY_ARRAY, pb = b->k == TY_PTR && b->elem->k == TY_ARRAY;
    Type *ea = pa                 ? a->elem->elem
               : a->k == TY_SLICE ? a->elem
                                  : NULL,
         *eb = pb                 ? b->elem->elem
               : b->k == TY_SLICE ? b->elem
                                  : NULL;
    if (ea && ea == eb && (pa || pb || (!a->hassent && !b->hassent))) return slice_of(ea, a->isconst || b->isconst);
  }
  if (a->k == TY_OPT && b->k == TY_OPT) {
    Type *e = peer_t(a->elem, b->elem);
    return e ? opt_of(e) : NULL;
  }
  if (a->k == TY_OPT) {
    Type *e = peer_t(a->elem, b);
    return e ? opt_of(e) : NULL;
  }
  if (b->k == TY_OPT) {
    Type *e = peer_t(a, b->elem);
    return e ? opt_of(e) : NULL;
  }
  if (is_tuple_type(a) && is_tuple_type(b) && (is_anon(a) || a->k == TY_TUPLE || is_anon(b) || b->k == TY_TUPLE)) {
    layout(a->ct);
    layout(b->ct);
    if (a->ct->fields.n != b->ct->fields.n) return NULL;
    Vec names = {0}, types = {0};
    for (int i = 0; i < a->ct->fields.n; i++) {
      Type *e = peer_t(((Field *)a->ct->fields.a[i])->t, ((Field *)b->ct->fields.a[i])->t);
      if (!e) return NULL;
      vpush(&names, fmt("%d", i));
      vpush(&types, e);
    }
    return mk_anon_struct(&names, &types, 1);
  }
  return NULL;
}
