#include "ct_int.h"

/* ---------- operators ---------- */
int enum_of(CVal *lit, CVal *other) {
  /* resolve an enum literal against the type of the other operand */
  if (lit->k != CV_ENUMLIT) return 0;
  Type *t = cv_typeof(other);
  if (other->k == CV_INT && t && t->k == TY_ENUM) {
    int64_t v;
    if (!enum_val(t, lit->s, &v)) die("no enum field .%s in %s", lit->s, tname(t));
    *lit = cv_int(v, t);
    return 1;
  }
  return 0;
}
int union_tag_is(CVal *u, CVal *tag) {
  if (u->i < 0) return 0;
  Field *f = field_at(u->t, (int)u->i);
  if (tag->k == CV_ENUMLIT) return !strcmp(f->name, tag->s);
  if (tag->k == CV_INT) return f->val == (int64_t)tag->i;
  return 0;
}
CVal *as_cells(CVal *v, int64_t *len, Type **et) {
  /* view of a sequence (array/tuple/slice/string/pointer-to-array) as a list of values */
  if (!cv_len(v, len)) {
    if (v->k == CV_PTR && v->t && v->t->k == TY_PTR && v->t->elem->k == TY_ARRAY)
      *len = v->t->elem->len;
    else
      return NULL;
  }
  CVal *r = xalloc(sizeof(CVal) * (*len + 1));
  for (int64_t i = 0; i < *len; i++) r[i] = cv_elem(v, i);
  Type *t = cv_typeof(v);
  if (et) {
    *et = NULL;
    if (v->k == CV_STR)
      *et = t_u8;
    else if (t->k == TY_ARRAY || t->k == TY_SLICE || t->k == TY_MPTR)
      *et = t->elem;
    else if (t->k == TY_PTR && t->elem->k == TY_ARRAY)
      *et = t->elem->elem;
  }
  return r;
}
int seq_is_str(CVal *v) {
  return v->k == CV_STR || (v->k == CV_SLICE && v->base && v->base->k == CV_STR);
}
int ev_fbin(const char *op, CVal a, CVal b, CVal *out) {
  Type *ta = cv_typeof(&a), *tb = cv_typeof(&b);
  Type *t = ta->k == TY_FLOAT ? ta : tb->k == TY_FLOAT ? tb : t_cfloat;
  f128 x = a.k == CV_FLOAT ? a.f : (f128)a.i, y = b.k == CV_FLOAT ? b.f : (f128)b.i, r;
  if (!strcmp(op, "==")) {
    *out = cv_bool(x == y);
    return R_OK;
  }
  if (!strcmp(op, "!=")) {
    *out = cv_bool(x != y);
    return R_OK;
  }
  if (!strcmp(op, "<")) {
    *out = cv_bool(x < y);
    return R_OK;
  }
  if (!strcmp(op, ">")) {
    *out = cv_bool(x > y);
    return R_OK;
  }
  if (!strcmp(op, "<=")) {
    *out = cv_bool(x <= y);
    return R_OK;
  }
  if (!strcmp(op, ">=")) {
    *out = cv_bool(x >= y);
    return R_OK;
  }
  switch (op[0]) {
  case '+': r = x + y; break;
  case '-': r = x - y; break;
  case '*': r = x * y; break;
  case '/': r = x / y; break;
  case '%': r = (f128)fmodl((long double)x, (long double)y); break;
  default: return R_FAIL;
  }
  *out = cv_float(fround(r, t), t);
  return R_OK;
}
W to_w(CVal *v) {
  W w;
  w.lo = (u128)v->i;
  if (v->big)
    w.hi = v->ih;
  else {
    Type *t = cv_typeof(v);
    w.hi = (t->k == TY_INT && !t->sign && t->bits >= 128) ? 0 : (v->i < 0 ? -1 : 0);
  }
  return w;
}
CVal from_w(W w) {
  CVal r = cv_int((i128)w.lo, t_cint);
  i128 sx = (i128)w.lo < 0 ? -1 : 0;
  if (w.hi != sx) {
    r.big = 1;
    r.ih = w.hi;
  }
  return r;
}
W cw_add(W a, W b) {
  W r;
  r.lo = a.lo + b.lo;
  r.hi = (i128)((u128)a.hi + (u128)b.hi + (r.lo < a.lo));
  return r;
}
W cw_neg(W a) {
  W r;
  r.lo = ~a.lo + 1;
  r.hi = (i128)(~(u128)a.hi + (r.lo == 0));
  return r;
}
int cw_cmp(W a, W b) {
  if (a.hi != b.hi) return a.hi < b.hi ? -1 : 1;
  return a.lo < b.lo ? -1 : a.lo > b.lo;
}
W cw_shl(W a, int n) {
  W r;
  if (n <= 0) return a;
  if (n >= 256) {
    r.hi = 0;
    r.lo = 0;
    return r;
  }
  if (n >= 128) {
    r.hi = (i128)(a.lo << (n - 128));
    r.lo = 0;
    return r;
  }
  r.hi = (i128)(((u128)a.hi << n) | (a.lo >> (128 - n)));
  r.lo = a.lo << n;
  return r;
}
W cw_sar(W a, int n) {
  W r;
  if (n <= 0) return a;
  if (n >= 256) {
    r.hi = a.hi < 0 ? -1 : 0;
    r.lo = (u128)r.hi;
    return r;
  }
  if (n >= 128) {
    r.lo = (u128)(a.hi >> (n - 128));
    r.hi = a.hi < 0 ? -1 : 0;
    return r;
  }
  r.lo = (a.lo >> n) | ((u128)a.hi << (128 - n));
  r.hi = a.hi >> n;
  return r;
}
int cw_fits(W a) {
  return a.hi == ((i128)a.lo < 0 ? -1 : 0);
}
int ev_bin_wide(const char *op, CVal a, CVal b, CVal *out) {
  W x = to_w(&a), y = to_w(&b), r;
  if ((op[0] == '<' || op[0] == '>') && (!op[1] || (op[1] == '=' && !op[2]))) {
    int c = cw_cmp(x, y);
    int res = !strcmp(op, "<") ? c < 0 : !strcmp(op, ">") ? c > 0 : !strcmp(op, "<=") ? c <= 0 : c >= 0;
    *out = cv_bool(res);
    return R_OK;
  }
  if (!strcmp(op, "==") || !strcmp(op, "!=")) {
    int eq = !cw_cmp(x, y);
    *out = cv_bool(op[0] == '=' ? eq : !eq);
    return R_OK;
  }
  if (!strcmp(op, "+"))
    r = cw_add(x, y);
  else if (!strcmp(op, "-"))
    r = cw_add(x, cw_neg(y));
  else if (!strcmp(op, "&")) {
    r.hi = x.hi & y.hi;
    r.lo = x.lo & y.lo;
  } else if (!strcmp(op, "|")) {
    r.hi = x.hi | y.hi;
    r.lo = x.lo | y.lo;
  } else if (!strcmp(op, "^")) {
    r.hi = x.hi ^ y.hi;
    r.lo = x.lo ^ y.lo;
  } else if (!strcmp(op, "<<")) {
    if (!cw_fits(y) || (i128)y.lo < 0) return R_FAIL;
    r = cw_shl(x, (int)((i128)y.lo > 300 ? 300 : (i128)y.lo));
  } else if (!strcmp(op, ">>")) {
    if (!cw_fits(y) || (i128)y.lo < 0) return R_FAIL;
    r = cw_sar(x, (int)((i128)y.lo > 300 ? 300 : (i128)y.lo));
  } else if (!strcmp(op, "*")) {
    if (!cw_fits(x) || !cw_fits(y)) return R_FAIL;
    i128 p;
    if (!__builtin_mul_overflow((i128)x.lo, (i128)y.lo, &p)) {
      *out = cv_int(p, t_cint);
      return R_OK;
    }
    int neg = ((i128)x.lo < 0) != ((i128)y.lo < 0);
    u128 ma = (i128)x.lo < 0 ? -x.lo : x.lo, mb = (i128)y.lo < 0 ? -y.lo : y.lo;
    uint64_t a0 = (uint64_t)ma, a1 = (uint64_t)(ma >> 64), b0 = (uint64_t)mb, b1 = (uint64_t)(mb >> 64);
    u128 p00 = (u128)a0 * b0, p01 = (u128)a0 * b1, p10 = (u128)a1 * b0, p11 = (u128)a1 * b1;
    u128 mid = (p00 >> 64) + (uint64_t)p01 + (uint64_t)p10;
    r.lo = (p00 & (u128)UINT64_MAX) | (mid << 64);
    r.hi = (i128)(p11 + (p01 >> 64) + (p10 >> 64) + (mid >> 64));
    if (neg) r = cw_neg(r);
  } else if (!strcmp(op, "/") || !strcmp(op, "%")) {
    if (!cw_fits(y) || (i128)y.lo == 0) return R_FAIL;
    if (cw_fits(x)) return R_FAIL; /* handled by the narrow path */
    if (x.hi < 0 || (i128)y.lo < 0) return R_FAIL;
    /* non-negative wide / small positive: long division by bits */
    u128 d = y.lo;
    W q = {0, 0};
    W rem = {0, 0};
    for (int i = 255; i >= 0; i--) {
      rem = cw_shl(rem, 1);
      int bit = i >= 128 ? (int)(((u128)x.hi >> (i - 128)) & 1) : (int)((x.lo >> i) & 1);
      rem.lo |= (u128)bit;
      W dw = {0, d};
      if (cw_cmp(rem, dw) >= 0) {
        rem = cw_add(rem, cw_neg(dw));
        if (i >= 128)
          q.hi |= (i128)((u128)1 << (i - 128));
        else
          q.lo |= (u128)1 << i;
      }
    }
    r = op[0] == '/' ? q : rem;
  } else
    return R_FAIL;
  *out = from_w(r);
  return R_OK;
}
int ev_bin(const char *op, CVal a, CVal b, CVal *out) {
  if (a.k == CV_INT && b.k == CV_INT &&
      (a.big || b.big ||
       ((cv_typeof(&a)->k == TY_CINT && (cv_typeof(&b)->k == TY_CINT || !strcmp(op, "<<") || !strcmp(op, ">>"))) &&
        strcmp(op, "/") && strcmp(op, "%") && strcmp(op, "<<|") && strcmp(op, "+%") && strcmp(op, "-%") &&
        strcmp(op, "*%") && strcmp(op, "+|") && strcmp(op, "-|") && strcmp(op, "*|")))) {
    if (a.big || b.big) {
      Type *ta = cv_typeof(&a), *tb = cv_typeof(&b);
      if ((ta->k == TY_CINT || a.big) && (tb->k == TY_CINT || b.big || !strcmp(op, "<<") || !strcmp(op, ">>"))) {
        int r = ev_bin_wide(op, a, b, out);
        if (r == R_OK) return r;
      } else if (!strcmp(op, "<") || !strcmp(op, ">") || !strcmp(op, "<=") || !strcmp(op, ">=") || !strcmp(op, "==") ||
                 !strcmp(op, "!="))
        return ev_bin_wide(op, a, b, out);
    } else {
      int r = ev_bin_wide(op, a, b, out);
      if (r == R_OK) return r;
    }
  }
  enum_of(&a, &b);
  enum_of(&b, &a);
  if ((a.k == CV_FLOAT && (b.k == CV_FLOAT || b.k == CV_INT)) || (b.k == CV_FLOAT && a.k == CV_INT))
    return ev_fbin(op, a, b, out);
  if (!strcmp(op, "==") || !strcmp(op, "!=")) {
    int eq;
    if (a.k == CV_UNDEF || b.k == CV_UNDEF) return R_FAIL;
    if (a.k == CV_AGG && a.t->k == TY_UNION && (b.k == CV_ENUMLIT || b.k == CV_INT))
      eq = union_tag_is(&a, &b);
    else if (b.k == CV_AGG && b.t->k == TY_UNION && (a.k == CV_ENUMLIT || a.k == CV_INT))
      eq = union_tag_is(&b, &a);
    else if (a.k == CV_AGG && b.k == CV_AGG && a.t->k == TY_ARRAY) { /* vectors: elementwise */
      CVal r = agg_new(vec_of(t_bool, a.n));
      for (int i = 0; i < a.n; i++) {
        CVal e;
        if (ev_bin(op, *a.el[i], *b.el[i], &e) != R_OK) return R_FAIL;
        *r.el[i] = e;
      }
      *out = r;
      return R_OK;
    } else if (a.k != b.k) {
      if (a.k == CV_NULL || b.k == CV_NULL)
        eq = 0;
      else
        return R_FAIL;
    } else if (a.k == CV_TYPE)
      eq = a.t == b.t;
    else if (a.k == CV_INT || a.k == CV_BOOL || a.k == CV_ERR)
      eq = a.i == b.i;
    else if (a.k == CV_ENUMLIT)
      eq = !strcmp(a.s, b.s);
    else if (a.k == CV_NULL)
      eq = (a.slen > 0) == (b.slen > 0) && (a.slen <= 0 || a.slen == b.slen);
    else if (a.k == CV_VOID)
      eq = 1;
    else if (a.k == CV_FN)
      eq = a.fn == b.fn;
    else if (a.k == CV_PTR)
      eq = a.base == b.base && a.idx == b.idx && a.i == b.i;
    else
      return R_FAIL;
    *out = cv_bool(op[0] == '=' ? eq : !eq);
    return R_OK;
  }
  if (!strcmp(op, "++") || !strcmp(op, "**")) {
    int64_t la, lb = 0;
    Type *ea = NULL, *eb = NULL;
    CVal *xa = as_cells(&a, &la, &ea);
    if (!xa) return R_FAIL;
    if (op[1] == '*') {
      if (b.k != CV_INT) return R_FAIL;
      lb = (int64_t)b.i;
    }
    CVal *xb = op[1] == '+' ? as_cells(&b, &lb, &eb) : NULL;
    if (op[1] == '+' && !xb) return R_FAIL;
    int64_t n = op[1] == '+' ? la + lb : la * lb;
    if (seq_is_str(&a) && (op[1] == '*' || seq_is_str(&b))) {
      char *r = xalloc(n + 1);
      int64_t k = 0;
      if (op[1] == '+') {
        for (int64_t i = 0; i < la; i++) r[k++] = (char)xa[i].i;
        for (int64_t i = 0; i < lb; i++) r[k++] = (char)xb[i].i;
      } else
        for (int64_t j = 0; j < lb; j++)
          for (int64_t i = 0; i < la; i++) r[k++] = (char)xa[i].i;
      *out = cv_str(r, (int)n);
      return R_OK;
    }
    Type *at = cv_typeof(&a), *bt2 = cv_typeof(&b);
    int tup = (is_struct_like(at) && !ea) || (op[1] == '+' && is_struct_like(bt2) && !eb && !ea);
    Type *et = ea ? ea : eb;
    if (tup || !et) {
      Vec names = {0}, types = {0};
      CVal r = {0};
      for (int64_t i = 0; i < n; i++) {
        CVal e = op[1] == '+' ? (i < la ? xa[i] : xb[i - la]) : xa[i % la];
        vpush(&names, fmt("%d", (int)i));
        vpush(&types, cv_typeof(&e));
      }
      r = agg_new(mk_anon_struct(&names, &types, 1));
      for (int64_t i = 0; i < n; i++) *r.el[i] = op[1] == '+' ? (i < la ? xa[i] : xb[i - la]) : xa[i % la];
      *out = r;
      return R_OK;
    }
    Type *ft = cv_typeof(&a);
    int hs = 0;
    int64_t sv = 0;
    if (ft->k == TY_PTR && ft->elem->k == TY_ARRAY) ft = ft->elem;
    if (ft->k == TY_ARRAY && ft->hassent) {
      hs = 1;
      sv = ft->sent;
    }
    CVal r = agg_new(array_of(et, n, hs, sv));
    for (int64_t i = 0; i < n; i++) *r.el[i] = ccoerce(op[1] == '+' ? (i < la ? xa[i] : xb[i - la]) : xa[i % la], et);
    *out = r;
    return R_OK;
  }
  if (a.k == CV_AGG && a.t->k == TY_ARRAY &&
      (b.k == CV_AGG || b.k == CV_INT || b.k == CV_BOOL || b.k == CV_FLOAT)) { /* vector ops */
    CVal r = agg_new(a.t);
    int cmp = !strcmp(op, "<") || !strcmp(op, ">") || !strcmp(op, "<=") || !strcmp(op, ">=");
    if (cmp) r = agg_new(vec_of(t_bool, a.n));
    for (int i = 0; i < a.n; i++) {
      CVal e;
      if (ev_bin(op, *a.el[i], b.k == CV_AGG ? *b.el[i] : b, &e) != R_OK) return R_FAIL;
      *r.el[i] = e;
    }
    *out = r;
    return R_OK;
  }
  if (a.k == CV_BOOL && b.k == CV_BOOL) {
    if (!strcmp(op, "&")) {
      *out = cv_bool(a.i & b.i);
      return R_OK;
    }
    if (!strcmp(op, "|")) {
      *out = cv_bool(a.i | b.i);
      return R_OK;
    }
    if (!strcmp(op, "^")) {
      *out = cv_bool(a.i ^ b.i);
      return R_OK;
    }
    return R_FAIL;
  }
  if (a.k == CV_PTR && b.k == CV_INT && a.base && (op[0] == '+' || op[0] == '-')) {
    CVal r = a;
    if (r.idx < 0) r.idx = 0;
    r.idx += op[0] == '+' ? (int64_t)b.i : -(int64_t)b.i;
    *out = r;
    return R_OK;
  }
  if (a.k == CV_PTR && b.k == CV_PTR && op[0] == '-' && a.base == b.base) {
    *out = cv_int((a.idx < 0 ? 0 : a.idx) - (b.idx < 0 ? 0 : b.idx), t_usize);
    return R_OK;
  }
  if (a.k != CV_INT || b.k != CV_INT) return R_FAIL;
  int shift = !strcmp(op, "<<") || !strcmp(op, ">>") || !strcmp(op, "<<|");
  Type *t = shift ? cv_typeof(&a) : (cv_typeof(&a)->k == TY_CINT ? cv_typeof(&b) : cv_typeof(&a));
  if (t->k == TY_ENUM) t = t->ct->tag;
  int uns = t->k == TY_INT && !t->sign;
  i128 x = a.i, y = b.i, r;
  if (op[0] == '<' || op[0] == '>')
    if (!op[1] || (op[1] == '=' && !op[2])) {
      /* u128 values >= 2^127 are stored as negative i128 */
      Type *ta = cv_typeof(&a), *tb = cv_typeof(&b);
      int ha = ta->k == TY_INT && !ta->sign && ta->bits >= 128 && x < 0,
          hb = tb->k == TY_INT && !tb->sign && tb->bits >= 128 && y < 0;
      int c = (ha && hb)
                  ? (((unsigned __int128)x > (unsigned __int128)y) - ((unsigned __int128)x < (unsigned __int128)y))
              : ha ? 1
              : hb ? -1
                   : (x > y) - (x < y);
      int res = !strcmp(op, "<") ? c < 0 : !strcmp(op, ">") ? c > 0 : !strcmp(op, "<=") ? c <= 0 : c >= 0;
      *out = cv_bool(res);
      return R_OK;
    }
  int sat = op[1] == '|';
  if (op[0] == '+')
    r = x + y;
  else if (op[0] == '-')
    r = x - y;
  else if (op[0] == '*' && op[1] != '*')
    r = x * y;
  else if (!strcmp(op, "/")) {
    if (!y) return R_FAIL;
    r = x / y;
  } else if (!strcmp(op, "%")) {
    if (!y) return R_FAIL;
    r = x % y;
  } else if (!strcmp(op, "&"))
    r = x & y;
  else if (!strcmp(op, "|"))
    r = x | y;
  else if (!strcmp(op, "^"))
    r = x ^ y;
  else if (op[0] == '<' && op[1] == '<') {
    r = y >= 127 ? 0 : x * ((i128)1 << y);
    if (op[2] == '|') sat = 1;
  } else if (!strcmp(op, ">>")) {
    if (uns && t->bits >= 128)
      r = y >= 128 ? 0 : (i128)((unsigned __int128)x >> y);
    else
      r = y >= 127 ? (x < 0 ? -1 : 0) : x >> y;
  } else
    return R_FAIL;
  if (uns && t->bits >= 128 && (op[0] == '/' || op[0] == '%') && !op[1] && (x < 0 || y < 0)) {
    unsigned __int128 ux = x, uy = y;
    r = (i128)(op[0] == '/' ? ux / uy : ux % uy);
  }
  if (sat && t->k == TY_INT) {
    i128 lo = t->sign ? -((i128)1 << (t->bits - 1)) : 0,
         hi = t->sign ? ((i128)1 << (t->bits - 1)) - 1 : (((i128)1 << t->bits) - 1);
    if (r < lo) r = lo;
    if (r > hi) r = hi;
  }
  (void)uns;
  *out = cv_int(wrap_int(r, t), t);
  return R_OK;
}
int bits_of(Type *t) {
  if (t->k == TY_INT || t->k == TY_FLOAT) return t->bits;
  if (t->k == TY_BOOL) return 1;
  if (t->k == TY_ENUM) {
    layout(t->ct);
    return t->ct->tag->bits;
  }
  if (is_packed(t)) {
    layout(t->ct);
    return t->ct->packed;
  }
  if (t->k == TY_UNION && t->ct && t->ct->node && (t->ct->node->flags & F_PACKED)) {
    layout(t->ct);
    int m = 0;
    for (int i = 0; i < t->ct->fields.n; i++) {
      int b = bits_of(((Field *)t->ct->fields.a[i])->t);
      if (b > m) m = b;
    }
    return m;
  }
  if (t->k == TY_ARRAY && is_vec(t)) return (int)(bits_of(t->elem) * t->len);
  return tsize(t) * 8;
}
int log2_bits(int b) {
  int r = 0;
  while ((1 << r) <= b) r++;
  return r;
}
i128 umask(int bits) {
  return bits >= 127 ? ~(i128)0 : (((i128)1 << bits) - 1);
}
int is_packed_union(Type *t) {
  return t && t->k == TY_UNION && t->ct && t->ct->node && (t->ct->node->flags & F_PACKED);
}
int packed_type(Type *t) {
  return t && (is_packed(t) || is_packed_union(t) || t->k == TY_INT || t->k == TY_BOOL || t->k == TY_ENUM ||
               t->k == TY_FLOAT);
}
/* IEEE bit patterns of comptime floats */
i128 f_to_bits(f128 f, int bits) {
  if (bits == 32) {
    float x = (float)f;
    uint32_t u;
    memcpy(&u, &x, 4);
    return u;
  }
  if (bits == 64) {
    double x = (double)f;
    uint64_t u;
    memcpy(&u, &x, 8);
    return u;
  }
  if (bits == 128) {
    i128 u;
    memcpy(&u, &f, 16);
    return u;
  }
  if (bits == 80) {
    long double x = (long double)f;
    unsigned char b[16] = {0};
    memcpy(b, &x, 10);
    uint64_t mant;
    uint16_t se;
    memcpy(&mant, b, 8);
    memcpy(&se, b + 8, 2);
    return ((i128)se << 64) | mant;
  }
  /* f16 */
  long double fl = (long double)f;
  int sg = signbit(fl) ? 1 : 0;
  long double a = fabsl(fl);
  uint16_t r;
  if (a != a)
    r = 0x7e00;
  else if (isinf(a))
    r = 0x7c00;
  else if (a == 0)
    r = 0;
  else {
    int e;
    frexpl(a, &e);
    e -= 1; /* a = m * 2^e, 1 <= m < 2 */
    if (e < -14)
      r = (uint16_t)nearbyintl(a * ldexpl(1, 24));
    else {
      long double m = a * ldexpl(1, -e);
      int fr = (int)nearbyintl((m - 1) * 1024);
      if (fr == 1024) {
        fr = 0;
        e++;
      }
      r = e > 15 ? 0x7c00 : (uint16_t)(((e + 15) << 10) | fr);
    }
  }
  return (i128)(r | (sg << 15));
}
f128 bits_to_f(i128 v, int bits) {
  if (bits == 32) {
    uint32_t u = (uint32_t)v;
    float x;
    memcpy(&x, &u, 4);
    return x;
  }
  if (bits == 64) {
    uint64_t u = (uint64_t)v;
    double x;
    memcpy(&x, &u, 8);
    return x;
  }
  if (bits == 128) {
    f128 x;
    memcpy(&x, &v, 16);
    return x;
  }
  if (bits == 80) {
    uint64_t mant = (uint64_t)v;
    uint16_t se = (uint16_t)(v >> 64);
    unsigned char b[16] = {0};
    memcpy(b, &mant, 8);
    memcpy(b + 8, &se, 2);
    long double f;
    memcpy(&f, b, sizeof f);
    return (f128)f;
  }
  uint16_t h = (uint16_t)v;
  int sg = h >> 15, e = (h >> 10) & 31, fr = h & 1023;
  long double r;
  if (e == 31)
    r = fr ? NAN : INFINITY;
  else if (e == 0)
    r = ldexpl(fr, -24);
  else
    r = ldexpl(fr + 1024, e - 25);
  return (f128)(sg ? -r : r);
}
/* pack/unpack packed structs to/from integers (bitcast) */
i128 pack_val(CVal *v) {
  if (v->k == CV_AGG && is_packed(v->t)) {
    i128 r = 0;
    for (int i = 0; i < v->n; i++) {
      Field *f = field_at(v->t, i);
      r |= (pack_val(v->el[i]) & umask(bits_of(f->t))) << f->bitoff;
    }
    return r;
  }
  if (v->k == CV_AGG && is_packed_union(v->t)) {
    Field *f = field_at(v->t, (int)v->i);
    return pack_val(v->el[0]) & umask(bits_of(f->t));
  }
  if (v->k == CV_BOOL || v->k == CV_INT) return v->i;
  if (v->k == CV_FLOAT) return f_to_bits(v->f, v->t && v->t->k == TY_FLOAT ? v->t->bits : 64);
  return 0;
}
CVal unpack_val(i128 x, Type *t) {
  if (is_packed_union(t)) {
    CVal a = agg_new(t);
    Field *f = field_at(t, 0);
    a.i = 0;
    *a.el[0] = unpack_val(x & umask(bits_of(f->t)), f->t);
    return a;
  }
  if (is_packed(t)) {
    CVal a = agg_new(t);
    for (int i = 0; i < a.n; i++) {
      Field *f = field_at(t, i);
      *a.el[i] = unpack_val((x >> f->bitoff) & umask(bits_of(f->t)), f->t);
    }
    return a;
  }
  if (t->k == TY_BOOL) return cv_bool((int)(x & 1));
  if (t->k == TY_FLOAT) return cv_float(bits_to_f(x & umask(t->bits), t->bits), t);
  return cv_int(wrap_int(x, t->k == TY_ENUM ? t->ct->tag : t), t);
}
Type *peer_int(CVal *a, CVal *b) {
  Type *t = cv_typeof(a);
  if (t->k == TY_CINT) t = cv_typeof(b);
  return t;
}
CVal ovf_tuple(i128 r, Type *t) {
  Vec names = {0}, types = {0};
  vpush(&names, "0");
  vpush(&names, "1");
  vpush(&types, t);
  vpush(&types, t_u1);
  Type *tt = mk_anon_struct(&names, &types, 1);
  CVal a = agg_new(tt);
  i128 w = wrap_int(r, t);
  *a.el[0] = cv_int(w, t);
  *a.el[1] = cv_int(w != r, t_u1);
  return a;
}

int cleaf_ok(Type *t) {
  while (t->k == TY_ARRAY) t = t->elem;
  return packed_type(t);
}
int clbits(Type *t) {
  return t->k == TY_ARRAY ? (int)(clbits(t->elem) * t->len) : bits_of(t);
}
void cflat(CVal *a, Type *t, i128 *acc, int *off) {
  if (t->k == TY_ARRAY) {
    for (int i = 0; i < t->len; i++) cflat(a->el[i], t->elem, acc, off);
    return;
  }
  int nb = bits_of(t);
  i128 v = pack_val(a) & umask(nb);
  *acc |= v << *off;
  *off += nb;
}
CVal cunflat(Type *t, i128 acc, int *off) {
  if (t->k == TY_ARRAY) {
    CVal r = agg_new(t);
    for (int i = 0; i < r.n; i++) *r.el[i] = cunflat(t->elem, acc, off);
    return r;
  }
  int nb = bits_of(t);
  CVal r = unpack_val((acc >> *off) & umask(nb), t);
  *off += nb;
  return r;
}
