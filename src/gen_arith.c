#include "gen_int.h"

/* ---------- wide integers (65..128 bits): 16-byte memory values {lo, hi} ---------- */
int is_wide(Type *t) {
  return t && t->k == TY_INT && t->bits > 64;
}
void wnorm(Type *t, char *sl) { /* canonicalize the high word for widths < 128 */
  if (t->bits >= 128) return;
  int hb = t->bits - 64;
  char *h = load(t_u64, addp(sl, 8)), *r = tmp();
  if (t->sign) {
    char *q = tmp();
    emit("%s =l shl %s, %d", q, h, 64 - hb);
    emit("%s =l sar %s, %d", r, q, 64 - hb);
  } else
    emit("%s =l and %s, %llu", r, h, (unsigned long long)((1ULL << hb) - 1));
  store(t_u64, r, addp(sl, 8));
}
Val w_from_parts(Type *t, char *lo, char *hi) {
  char *sl = slot(t);
  store(t_u64, lo, sl);
  store(t_u64, hi, addp(sl, 8));
  wnorm(t, sl);
  return V(t, sl);
}
char *wlo(Val v) {
  return load(t_u64, addr_of(v));
}
char *whi(Val v) {
  return load(t_u64, addp(addr_of(v), 8));
}
Val wconv(Val v, Type *to) { /* any int <-> any int where one side is wide */
  Type *f = v.t;
  if (f->k == TY_BOOL) f = t_u1;
  if (f->k == TY_ENUM) f = f->ct->tag;
  if (is_wide(f) && is_wide(to)) {
    char *a = addr_of(v);
    return w_from_parts(to, load(t_u64, a), load(t_u64, addp(a, 8)));
  }
  if (is_wide(f)) {
    char *lo = wlo(v);
    if (qc(to) == 'w') {
      char *r = tmp();
      emit("%s =w copy %s", r, lo);
      return V(to, norm(r, to));
    }
    return V(to, norm(lo, to));
  }
  char *o = opnd(v), *lo = o;
  if (qc(f) == 'w') {
    lo = tmp();
    emit("%s =l %s %s", lo, f->sign ? "extsw" : "extuw", o);
  }
  char *hi = "0";
  if (f->sign) {
    hi = tmp();
    emit("%s =l sar %s, 63", hi, lo);
  }
  return w_from_parts(to, lo, hi);
}
Val wcall(const char *fn, Type *t, Val a, Val b, int bshift) {
  char *r = tmp();
  if (bshift) {
    Val bb = coerce(rv(b), t_u32);
    emit("%s =:zbw call $%s(l %s, l %s, w %s)", r, fn, wlo(a), whi(a), opnd(bb));
  } else
    emit("%s =:zbw call $%s(l %s, l %s, l %s, l %s)", r, fn, wlo(a), whi(a), wlo(b), whi(b));
  return w_from_parts(t, load(t_u64, r), load(t_u64, addp(r, 8)));
}
Val w_arith(const char *op, Type *t, Val a, Val b) {
  int sg = t->sign;
  if (op[0] == '<' || op[0] == '>') {
    if (b.ck) b = coerce(b, t_u32);
    return wcall(op[0] == '<' ? "__ashlti3" : sg ? "__ashrti3" : "__lshrti3", t, a, b, 1);
  }
  a = coerce(a, t);
  b = coerce(b, t);
  char *al = wlo(a), *ah = whi(a), *bl = wlo(b), *bh = whi(b), *lo = tmp(), *hi = tmp();
  if (op[0] == '+') {
    char *c = tmp(), *cl = tmp(), *h1 = tmp();
    emit("%s =l add %s, %s", lo, al, bl);
    emit("%s =w cultl %s, %s", c, lo, al);
    emit("%s =l extuw %s", cl, c);
    emit("%s =l add %s, %s", h1, ah, bh);
    emit("%s =l add %s, %s", hi, h1, cl);
  } else if (op[0] == '-') {
    char *c = tmp(), *cl = tmp(), *h1 = tmp();
    emit("%s =l sub %s, %s", lo, al, bl);
    emit("%s =w cultl %s, %s", c, al, bl);
    emit("%s =l extuw %s", cl, c);
    emit("%s =l sub %s, %s", h1, ah, bh);
    emit("%s =l sub %s, %s", hi, h1, cl);
  } else if (op[0] == '&' || op[0] == '|' || op[0] == '^') {
    const char *ins = op[0] == '&' ? "and" : op[0] == '|' ? "or" : "xor";
    emit("%s =l %s %s, %s", lo, ins, al, bl);
    emit("%s =l %s %s, %s", hi, ins, ah, bh);
  } else if (op[0] == '*')
    return wcall("__multi3", t, a, b, 0);
  else if (op[0] == '/')
    return wcall(sg ? "__divti3" : "__udivti3", t, a, b, 0);
  else if (op[0] == '%')
    return wcall(sg ? "__modti3" : "__umodti3", t, a, b, 0);
  else
    die("unsupported operator %s on %s", op, tname(t));
  return w_from_parts(t, lo, hi);
}
Val w_cmp(const char *op, Type *t, Val a, Val b) {
  a = coerce(a, t);
  b = coerce(b, t);
  char *al = wlo(a), *ah = whi(a), *bl = wlo(b), *bh = whi(b), *r = tmp();
  int eq = !strcmp(op, "=="), ne = !strcmp(op, "!=");
  if (eq || ne) {
    char *x = tmp(), *y = tmp(), *z = tmp();
    emit("%s =l xor %s, %s", x, al, bl);
    emit("%s =l xor %s, %s", y, ah, bh);
    emit("%s =l or %s, %s", z, x, y);
    emit("%s =w %s %s, 0", r, eq ? "ceql" : "cnel", z);
    return V(t_bool, r);
  }
  int sg = t->sign;
  const char *hs, *ls; /* strict compare on hi, then lo (unsigned) */
  if (op[0] == '<') {
    hs = sg ? "csltl" : "cultl";
    ls = op[1] == '=' ? "culel" : "cultl";
  } else {
    hs = sg ? "csgtl" : "cugtl";
    ls = op[1] == '=' ? "cugel" : "cugtl";
  }
  char *h1 = tmp(), *he = tmp(), *l1 = tmp(), *t2 = tmp();
  emit("%s =w %s %s, %s", h1, hs, ah, bh);
  emit("%s =w ceql %s, %s", he, ah, bh);
  emit("%s =w %s %s, %s", l1, ls, al, bl);
  emit("%s =w and %s, %s", t2, he, l1);
  emit("%s =w or %s, %s", r, h1, t2);
  return V(t_bool, r);
}
Val vel(Val v, int64_t i) {
  Type *et = v.t->elem;
  return rv(LV(et, addp(addr_of(v), i * tsize(et))));
}
Val vec_bin(const char *op, Val a, Val b, int cmp) {
  Type *vt = is_vec(a.t) ? a.t : b.t;
  if (is_vec(a.t) && is_vec(b.t) && a.t->elem != b.t->elem) {
    Type *pe = peer_t(a.t->elem, b.t->elem);
    if (pe) vt = vec_of(pe, a.t->len);
    a = coerce(a, vt);
    b = coerce(b, vt);
  }
  if (!is_vec(a.t)) a = coerce(a, vt);
  if (!is_vec(b.t)) b = coerce(b, vt);
  Type *rt = cmp ? vec_of(t_bool, vt->len) : vt;
  char *sl = slot(rt);
  char *pa = addr_of(a), *pb = addr_of(b);
  a = V(a.t, pa);
  b = V(b.t, pb);
  for (int64_t i = 0; i < vt->len; i++) {
    Val r = cmp ? gen_cmp(op, vel(a, i), vel(b, i)) : gen_arith(op, vel(a, i), vel(b, i));
    r = coerce(r, rt->elem);
    put(r, rt->elem, addp(sl, i * tsize(rt->elem)));
  }
  return V(rt, sl);
}
Val vec_splat(Val x, Type *vt) {
  char *sl = slot(vt);
  x = coerce(rv(x), vt->elem);
  char *o = is_aggr(vt->elem) ? NULL : opnd(x);
  for (int64_t i = 0; i < vt->len; i++) {
    if (o)
      store(vt->elem, o, addp(sl, i * tsize(vt->elem)));
    else
      put(x, vt->elem, addp(sl, i * tsize(vt->elem)));
  }
  return V(vt, sl);
}
Val sel2(Val c, Val a, Val b, Type *t) { /* c ? a : b */
  char *sl = slot(t), *l1 = newl(), *l2 = newl(), *le = newl();
  br(opnd(c), l1, l2);
  label(l1);
  put(coerce(a, t), t, sl);
  jmp(le);
  label(l2);
  put(coerce(b, t), t, sl);
  jmp(le);
  label(le);
  return rv(LV(t, sl));
}
Val vec_reduce(const char *on, Val v) {
  Type *et = v.t->elem;
  v = V(v.t, addr_of(v));
  Val acc = vel(v, 0);
  for (int64_t i = 1; i < v.t->len; i++) {
    Val e = vel(v, i);
    if (!strcmp(on, "Min") || !strcmp(on, "Max")) {
      Val c = gen_cmp(on[1] == 'i' ? "<" : ">", e, acc);
      acc = sel2(c, e, acc, et);
      continue;
    }
    const char *bop = !strcmp(on, "And")   ? "&"
                      : !strcmp(on, "Or")  ? "|"
                      : !strcmp(on, "Xor") ? "^"
                      : !strcmp(on, "Add") ? (et->k == TY_INT ? "+%" : "+")
                                           : "*%";
    if (et->k == TY_BOOL) {
      char *r = tmp();
      emit("%s =w %s %s, %s", r, bop[0] == '&' ? "and" : bop[0] == '|' ? "or" : "xor", opnd(acc), opnd(e));
      acc = V(t_bool, r);
    } else
      acc = coerce(gen_arith(bop, acc, e), et);
  }
  return acc;
}
Val vec_un(const char *op, Val v) {
  Type *vt = v.t;
  char *sl = slot(vt);
  v = V(vt, addr_of(v));
  for (int64_t i = 0; i < vt->len; i++) {
    Val e = vel(v, i);
    char *r = tmp();
    Type *et = vt->elem;
    if (op[0] == '!')
      emit("%s =w ceqw %s, 0", r, opnd(e));
    else if (op[0] == '~') {
      emit("%s =%c xor %s, -1", r, qc(et), opnd(e));
      r = norm(r, et);
    } else {
      emit("%s =%c neg %s", r, qc(et), opnd(e));
      r = norm(r, et);
    }
    store(et, r, addp(sl, i * tsize(et)));
  }
  return V(vt, sl);
}
Val fold_bin(const char *op, Val a, Val b) {
  CVal r;
  if (!cv_binop(op, a.cv, b.cv, &r)) die("cannot fold comptime operation %s", op);
  return CK(r);
}

/* saturating integer arithmetic (+| -| *| <<|) for ints up to 64 bits */
char *sat_l(Val v, Type *t) {
  char *x = opnd(v);
  if (qc(t) == 'w') {
    char *r = tmp();
    emit("%s =l %s %s", r, t->sign ? "extsw" : "extuw", x);
    return r;
  }
  return x;
}
char *sat_sel(char *cw, char *th, char *el) { /* cw ? th : el (all l except cw) */
  char *c = tmp(), *m = tmp(), *d = tmp(), *e = tmp(), *r = tmp();
  emit("%s =l extuw %s", c, cw);
  emit("%s =l sub 0, %s", m, c);
  emit("%s =l xor %s, %s", d, th, el);
  emit("%s =l and %s, %s", e, d, m);
  emit("%s =l xor %s, %s", r, el, e);
  return r;
}
Val sat_arith(const char *op, Type *t, Val a, Val b) {
  int bits = t->bits, sg = t->sign;
  char *mx = fmt("%lld", sg           ? (long long)((1ULL << (bits - 1)) - 1)
                         : bits == 64 ? -1LL
                                      : (long long)((1ULL << bits) - 1));
  char *mn = fmt("%lld", sg ? (long long)(-(1ULL << (bits - 1))) : 0LL);
  char *X = sat_l(a, t), *r = tmp(), *c1 = tmp(), *c2 = tmp();
  if (op[0] == '<') { /* <<| */
    char *Y = opnd(coerce(b, t_u64));
    if (qc(b.t) == 'w' && !b.ck) {
      char *e = tmp();
      emit("%s =l extuw %s", e, Y);
      Y = e;
    }
    char *sh = tmp(), *bk = tmp();
    emit("%s =l shl %s, %s", sh, X, Y);
    char *tr = sh;
    if (bits < 64) {
      tr = tmp();
      emit("%s =l shl %s, %d", tr, sh, 64 - bits);
      char *t2 = tmp();
      emit("%s =l %s %s, %d", t2, sg ? "sar" : "shr", tr, 64 - bits);
      tr = t2;
    }
    emit("%s =l %s %s, %s", bk, sg ? "sar" : "shr", tr, Y);
    emit("%s =w cnel %s, %s", c1, bk, X);
    char *big = tmp();
    emit("%s =w cugel %s, %d", big, Y, bits);
    char *nz = tmp();
    emit("%s =w cnel %s, 0", nz, X);
    char *bz = tmp();
    emit("%s =w and %s, %s", bz, big, nz);
    char *ov = tmp();
    emit("%s =w or %s, %s", ov, c1, bz);
    char *satv = mx;
    if (sg) {
      char *ng = tmp();
      emit("%s =w csltl %s, 0", ng, X);
      satv = sat_sel(ng, mn, mx);
    }
    r = sat_sel(ov, satv, tr);
  } else {
    b = coerce(b, t);
    char *Y = sat_l(b, t);
    const char *ins = op[0] == '+' ? "add" : op[0] == '-' ? "sub" : "mul";
    emit("%s =l %s %s, %s", r, ins, X, Y);
    if (op[0] == '*' && bits > 32) { /* overflow of the 64-bit product */
      char *nz = tmp(), *dv = tmp(), *q = tmp(), *ov = tmp(), *nzl = tmp(), *inv = tmp();
      emit("%s =w cnel %s, 0", nz, X);
      emit("%s =l extuw %s", nzl, nz);
      emit("%s =l xor %s, 1", inv, nzl);
      emit("%s =l add %s, %s", dv, X, inv);
      emit("%s =l %s %s, %s", q, sg ? "div" : "udiv", r, dv);
      char *ne = tmp();
      emit("%s =w cnel %s, %s", ne, q, Y);
      emit("%s =w and %s, %s", ov, ne, nz);
      char *satv = mx;
      if (sg) {
        char *xy = tmp(), *ng = tmp();
        emit("%s =l xor %s, %s", xy, X, Y);
        emit("%s =w csltl %s, 0", ng, xy);
        satv = sat_sel(ng, mn, mx);
      }
      r = sat_sel(ov, satv, r);
      if (bits == 64) goto done;
    }
    if (bits == 64 && op[0] != '*') {
      char *ov = tmp();
      if (!sg) {
        if (op[0] == '+') {
          emit("%s =w cultl %s, %s", ov, r, X);
          r = sat_sel(ov, mx, r);
        } else {
          emit("%s =w cultl %s, %s", ov, X, Y);
          r = sat_sel(ov, "0", r);
        }
      } else {
        char *p1 = tmp(), *p2 = tmp(), *p3 = tmp(), *ng = tmp();
        if (op[0] == '+') {
          emit("%s =l xor %s, %s", p1, X, r);
          emit("%s =l xor %s, %s", p2, Y, r);
        } else {
          emit("%s =l xor %s, %s", p1, X, Y);
          emit("%s =l xor %s, %s", p2, X, r);
        }
        emit("%s =l and %s, %s", p3, p1, p2);
        emit("%s =w csltl %s, 0", ov, p3);
        emit("%s =w csltl %s, 0", ng, X);
        r = sat_sel(ov, sat_sel(ng, mn, mx), r);
      }
      goto done;
    }
    if (!sg) {
      if (op[0] == '-') {
        emit("%s =w csltl %s, 0", c1, r);
        r = sat_sel(c1, "0", r);
      } else {
        emit("%s =w cugtl %s, %s", c1, r, mx);
        r = sat_sel(c1, mx, r);
      }
    } else {
      emit("%s =w csgtl %s, %s", c1, r, mx);
      r = sat_sel(c1, mx, r);
      emit("%s =w csltl %s, %s", c2, r, mn);
      r = sat_sel(c2, mn, r);
    }
  }
done:
  if (qc(t) == 'w') {
    char *w = tmp();
    emit("%s =w copy %s", w, r);
    r = w;
  }
  return V(t, r);
}
Val gen_cmp(const char *op, Val a, Val b) {
  if ((is_vec(a.t) || is_vec(b.t)) && !(a.ck && b.ck)) return vec_bin(op, rv(a), rv(b), 1);
  if (!a.ck && b.ck && b.cv.k == CV_INT && b.cv.i == 0 && !b.cv.big && a.t->k == TY_INT &&
      !a.t->sign) { /* unsigned vs 0: comptime-known (as in Sema) */
    if (!strcmp(op, ">=")) return CK(cv_bool(1));
    if (!strcmp(op, "<")) return CK(cv_bool(0));
  }
  if (a.ck && !b.ck && a.cv.k == CV_INT && a.cv.i == 0 && !a.cv.big && b.t->k == TY_INT && !b.t->sign) {
    if (!strcmp(op, "<=")) return CK(cv_bool(1));
    if (!strcmp(op, ">")) return CK(cv_bool(0));
  }
  { /* runtime int vs comptime int outside its range: comptime-known result (as in Sema) */
    for (int sw = 0; sw < 2; sw++) {
      Val r = sw ? a : b, c = sw ? b : a; /* r: runtime side, c: constant side */
      if (r.ck || !c.ck || c.cv.k != CV_INT || c.cv.big || r.t->k != TY_INT || r.t->bits > 127) continue;
      int bits = r.t->bits;
      i128 lo = r.t->sign ? -((i128)1 << (bits - 1)) : 0,
           hi = r.t->sign ? ((i128)1 << (bits - 1)) - 1 : (((i128)1 << bits) - 1);
      i128 cv = c.cv.i;
      Type *ctt = cv_typeof(&c.cv);
      if (ctt && ctt->k == TY_INT && !ctt->sign && ctt->bits >= 128 && cv < 0) cv = hi + 1; /* huge u128 */
      int below = cv<lo, above = cv> hi;
      if (!below && !above) continue;
      /* rgt: runtime side always > constant; sw=1: runtime operand is on the left */
      int rgt = below;
      const char *o = op;
      int res;
      if (!strcmp(o, "=="))
        res = 0;
      else if (!strcmp(o, "!="))
        res = 1;
      else {
        int lt = !strcmp(o, "<") || !strcmp(o, "<="), gt = !strcmp(o, ">") || !strcmp(o, ">=");
        /* left side relation */
        int left_gt = sw ? rgt : !rgt;
        res = lt ? !left_gt : gt ? left_gt : 0;
      }
      return CK(cv_bool(res));
    }
  }
  int eq = !strcmp(op, "=="), ne = !strcmp(op, "!=");
  if ((eq || ne) && !(a.ck && b.ck) &&
      ((a.t->k == TY_STRUCT && is_packed(a.t)) || (b.t->k == TY_STRUCT && is_packed(b.t)))) {
    Type *pt = (a.t->k == TY_STRUCT && is_packed(a.t)) ? a.t : b.t, *h = int_type(tsize(pt) * 8, 0);
    a = coerce(a, pt);
    b = coerce(b, pt);
    a = V(h, a.ck ? fmt("%llu", (unsigned long long)cv_pack(&a.cv)) : load(h, addr_of(a)));
    b = V(h, b.ck ? fmt("%llu", (unsigned long long)cv_pack(&b.cv)) : load(h, addr_of(b)));
  }
  if ((eq || ne) && (a.t->k == TY_NULL || b.t->k == TY_NULL)) {
    Val o = a.t->k == TY_NULL ? b : a;
    char *h = opt_has(o), *r = tmp();
    emit("%s =w %s %s, 0", r, eq ? "ceqw" : "cnew", h);
    return V(t_bool, r);
  }
  if ((eq || ne) && !(a.ck && b.ck) &&
      ((a.t->k == TY_OPT && !opt_is_ptr(a.t)) || (b.t->k == TY_OPT && !opt_is_ptr(b.t)))) {
    char *r = tmp();
    if (a.t->k == TY_OPT && b.t->k == TY_OPT) {
      char *ha = opt_has(a), *hb = opt_has(b);
      Val c = gen_cmp("==", rv(opt_payload(a, NULL)), rv(opt_payload(b, NULL)));
      char *same = tmp(), *nh = tmp(), *t1 = tmp();
      emit("%s =w ceqw %s, %s", same, ha, hb);
      emit("%s =w ceqw %s, 0", nh, ha);
      emit("%s =w or %s, %s", t1, nh, opnd(c));
      emit("%s =w and %s, %s", r, same, t1);
    } else {
      Val o = a.t->k == TY_OPT ? a : b, x = a.t->k == TY_OPT ? b : a;
      char *h = opt_has(o);
      Val c = gen_cmp("==", rv(opt_payload(o, NULL)), x);
      emit("%s =w and %s, %s", r, h, opnd(c));
    }
    if (ne) {
      char *r2 = tmp();
      emit("%s =w xor %s, 1", r2, r);
      r = r2;
    }
    return V(t_bool, r);
  }
  if (a.t->k == TY_UNION && a.t->ct->tagged && b.t->k != TY_UNION) a = coerce(a, a.t->ct->tag);
  if (b.t->k == TY_UNION && b.t->ct->tagged && a.t->k != TY_UNION) b = coerce(b, b.t->ct->tag);
  Type *t = peer(a, b);
  a = coerce(a, t);
  b = coerce(b, t);
  if (is_wide(t) && !(a.ck && b.ck)) return w_cmp(op, t, a, b);
  if (a.ck && b.ck && (a.cv.k == CV_INT || a.cv.k == CV_BOOL || a.cv.k == CV_ERR) && a.cv.k == b.cv.k)
    return fold_bin(op, a, b);
  if (a.ck && b.ck && a.cv.k == CV_TYPE) {
    CVal r = {0};
    r.k = CV_BOOL;
    r.t = t_bool;
    r.i = (a.cv.t == b.cv.t) == eq;
    return CK(r);
  }
  if (a.ck && b.ck && (a.cv.k == CV_FLOAT || b.cv.k == CV_FLOAT)) return fold_bin(op, a, b);
  if (is_float(t)) {
    if (t->k == TY_CFLOAT) {
      t = t_f64;
      a = coerce(a, t);
      b = coerce(b, t);
    }
    if (is_bigf(t)) {
      int k = eq ? 0 : ne ? 1 : !strcmp(op, "<") ? 2 : !strcmp(op, "<=") ? 3 : !strcmp(op, ">") ? 4 : 5;
      char *x = opnd(a), *y = opnd(b), *r = tmp();
      emit("%s =w call $zb_fcmp(w %d, w %d, l %s, l %s)", r, t->bits, k, x, y);
      return V(t_bool, r);
    }
    const char *fc = eq                  ? "ceq"
                     : ne                ? "cne"
                     : !strcmp(op, "<")  ? "clt"
                     : !strcmp(op, ">")  ? "cgt"
                     : !strcmp(op, "<=") ? "cle"
                                         : "cge";
    char *x = opnd(a), *y = opnd(b), *r = tmp();
    emit("%s =w %s%c %s, %s", r, fc, qc(t), x, y);
    return V(t_bool, r);
  }
  int sg = (t->k == TY_INT && t->sign);
  const char *cc = eq                  ? "ceq"
                   : ne                ? "cne"
                   : !strcmp(op, "<")  ? (sg ? "cslt" : "cult")
                   : !strcmp(op, ">")  ? (sg ? "csgt" : "cugt")
                   : !strcmp(op, "<=") ? (sg ? "csle" : "cule")
                                       : (sg ? "csge" : "cuge");
  char *x = opnd(a), *y = opnd(b), *r = tmp();
  emit("%s =w %s%c %s, %s", r, cc, qc(t), x, y);
  return V(t_bool, r);
}
Val gen_arith(const char *op, Val a, Val b) {
  a = rv(a);
  b = rv(b);
  if ((is_vec(a.t) || is_vec(b.t)) && !(a.ck && b.ck)) return vec_bin(op, a, b, 0);
  if ((a.t->k == TY_MPTR || a.t->k == TY_PTR) && (b.t->k == TY_MPTR || b.t->k == TY_PTR) && op[0] == '-') {
    char *d = tmp(), *r = tmp();
    emit("%s =l sub %s, %s", d, opnd(a), opnd(b));
    emit("%s =l udiv %s, %d", r, d, tsize(a.t->elem) ? tsize(a.t->elem) : 1);
    return V(t_usize, r);
  }
  if (a.t->k == TY_MPTR && (op[0] == '+' || op[0] == '-') && b.t->k != TY_MPTR) {
    b = coerce(b, t_usize);
    char *o = tmp(), *r = tmp();
    emit("%s =l mul %s, %d", o, opnd(b), tsize(a.t->elem));
    emit("%s =l %s %s, %s", r, op[0] == '+' ? "add" : "sub", opnd(a), o);
    return V(a.t, r);
  }
  if (a.t->k == TY_MPTR && b.t->k == TY_MPTR) {
    char *d = tmp(), *r = tmp();
    emit("%s =l sub %s, %s", d, opnd(a), opnd(b));
    emit("%s =l udiv %s, %d", r, d, tsize(a.t->elem));
    return V(t_usize, r);
  }
  int shift = !strcmp(op, "<<") || !strcmp(op, ">>") || !strcmp(op, "<<|");
  Type *t = shift ? a.t : peer(a, b);
  if (a.ck && b.ck && (a.cv.k == CV_INT || a.cv.k == CV_BOOL || a.cv.k == CV_FLOAT))
    return fold_bin(op, coerce(a, t), b);
  if (t->k == TY_CINT) t = t_i64;
  if (t->k == TY_CFLOAT) t = t_f64;
  if (t->k == TY_FLOAT) {
    a = coerce(a, t);
    b = coerce(b, t);
    char c = qc(t), *x = opnd(a), *y = opnd(b), *r = tmp();
    if (is_bigf(t)) {
      int k = op[0] == '+' ? 0 : op[0] == '-' ? 1 : op[0] == '*' ? 2 : op[0] == '/' ? 3 : op[0] == '%' ? 4 : -1;
      if (k < 0) die("unsupported float operator %s", op);
      return V(t, bigf_op(k, t, x, y));
    }
    if (op[0] == '%') {
      emit("%s =%c call $%s(%c %s, %c %s)", r, c, c == 's' ? "fmodf" : "fmod", c, x, c, y);
      return V(t, r);
    }
    const char *ins = op[0] == '+' ? "add" : op[0] == '-' ? "sub" : op[0] == '*' ? "mul" : op[0] == '/' ? "div" : NULL;
    if (!ins) die("unsupported float operator %s", op);
    emit("%s =%c %s %s, %s", r, c, ins, x, y);
    return V(t, r);
  }
  if (t->k == TY_INT && !is_wide(t) &&
      (!strcmp(op, "+|") || !strcmp(op, "-|") || !strcmp(op, "*|") || !strcmp(op, "<<|")))
    return sat_arith(op, t, coerce(a, t), b);
  if (is_wide(t)) {
    const char *o2 = op;
    return w_arith(o2, t, shift ? a : a, b);
  }
  a = coerce(a, t);
  if (!shift) b = coerce(b, t);
  int sg = t->k == TY_INT && t->sign;
  char c = qc(t);
  const char *ins;
  if (op[0] == '+')
    ins = "add";
  else if (op[0] == '-')
    ins = "sub";
  else if (op[0] == '*')
    ins = "mul";
  else if (op[0] == '/')
    ins = sg ? "div" : "udiv";
  else if (op[0] == '%')
    ins = sg ? "rem" : "urem";
  else if (!strcmp(op, "&"))
    ins = "and";
  else if (!strcmp(op, "|"))
    ins = "or";
  else if (!strcmp(op, "^"))
    ins = "xor";
  else if (!strcmp(op, "<<") || !strcmp(op, "<<|"))
    ins = "shl";
  else if (!strcmp(op, ">>"))
    ins = sg ? "sar" : "shr";
  else
    die("unsupported operator %s", op);
  char *x = opnd(a), *y = opnd(b);
  if (shift) {
    if (b.ck)
      y = fmt("%lld", (long long)b.cv.i);
    else if (c == 'l' && qc(b.t) == 'w') {
      char *e = tmp();
      emit("%s =l extuw %s", e, y);
      y = e;
    }
  }
  char *r = tmp();
  emit("%s =%c %s %s, %s", r, c, ins, x, y);
  if (op[1] == '%' || op[1] == '|' || !strcmp(op, "<<") || op[0] == '+' || op[0] == '-' || op[0] == '*') r = norm(r, t);
  return V(t, r);
}
Val gen_logic(Node *n, Scope *s) {
  int isand = !strcmp(n->s, "and");
  Val a = coerce(gen(n->a, s, t_bool), t_bool);
  if (a.ck) {
    if (isand ? !a.cv.i : a.cv.i) return a;
    return coerce(gen(n->b, s, t_bool), t_bool);
  }
  char *sl = slot(t_bool), *lr = newl(), *le = newl();
  char *x = opnd(a);
  store(t_bool, x, sl);
  if (isand)
    br(x, lr, le);
  else
    br(x, le, lr);
  label(lr);
  Val b = coerce(gen(n->b, s, t_bool), t_bool);
  store(t_bool, opnd(b), sl);
  jmp(le);
  label(le);
  return V(t_bool, load(t_bool, sl));
}

/* ---------- builtins ---------- */
Val int_conv(Val v, Type *to, int trunc) {
  v = rv(v);
  if (v.ck) {
    CVal c = v.cv;
    c.t = to;
    if (trunc) c.i = wrap_int(c.i, to);
    return CK(c);
  }
  if (is_wide(v.t) || is_wide(to)) return wconv(v, to);
  Type *f = v.t;
  if (f->k == TY_BOOL) f = t_u1;
  if (f->k == TY_ENUM) f = f->ct->tag;
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
  if (to->k == TY_INT && f->k == TY_INT && (to->bits < f->bits || to->sign != f->sign)) return V(to, norm(o, to));
  return V(to, o);
}
Val gen_minmax(Node *n, Scope *s, Type *ex, int mn) {
  Val acc = rv(gen(n->list.a[0], s, NULL));
  for (int i = 1; i < n->list.n; i++) {
    Val b = rv(gen(n->list.a[i], s, NULL));
    Type *t = peer(acc, b);
    if (t->k == TY_CINT) t = ex && ex->k == TY_INT ? ex : t_i64;
    acc = coerce(acc, t);
    b = coerce(b, t);
    Val c = gen_cmp(mn ? "<" : ">", acc, b);
    char *sl = slot(t), *la = newl(), *lb = newl(), *le = newl();
    br(opnd(c), la, lb);
    label(la);
    store(t, opnd(acc), sl);
    jmp(le);
    label(lb);
    store(t, opnd(b), sl);
    jmp(le);
    label(le);
    acc = V(t, load(t, sl));
  }
  return acc;
}
