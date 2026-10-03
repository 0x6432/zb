/* debug runtime helper for zb-compiled programs (ZB_TRAPLOC=1): print trap location + frame-pointer backtrace */
#include <unistd.h>
#include <stdio.h>
#include <stdint.h>
void zb_trapbt(const char *m, long n) {
  write(2, m, n);
  void **fp = __builtin_frame_address(0);
  for (int i = 0; i < 40 && fp; i++) {
    void *ret = fp[1]; if (!ret) break;
    fprintf(stderr, "  #%d %p\n", i, ret);
    void **nfp = (void **)fp[0]; if (nfp <= fp) break; fp = nfp;
  }
}
/* runtime float shims: zb keeps f16 in 's' and f80/f128 in 'd' registers; memory uses the real formats */
double zb_ldf128(const void *p) { __float128 x; __builtin_memcpy(&x, p, 16); return (double)x; }
void zb_stf128(void *p, double v) { __float128 x = v; __builtin_memcpy(p, &x, 16); }
double zb_ldf80(const void *p) { long double x; __builtin_memcpy(&x, p, 10); return (double)x; }
void zb_stf80(void *p, double v) { long double x = v; __builtin_memset(p, 0, 16); __builtin_memcpy(p, &x, 10); }
float zb_h2f(unsigned h) {
  unsigned s = (h >> 15) & 1, e = (h >> 10) & 31, m = h & 1023; unsigned u;
  if (e == 0) { if (!m) u = s << 31; else { e = 127 - 15 + 1; while (!(m & 1024)) { m <<= 1; e--; } m &= 1023; u = (s << 31) | (e << 23) | (m << 13); } }
  else if (e == 31) u = (s << 31) | (255u << 23) | (m << 13);
  else u = (s << 31) | ((e - 15 + 127) << 23) | (m << 13);
  float f; __builtin_memcpy(&f, &u, 4); return f;
}
unsigned zb_f2h(float f) {
  unsigned u; __builtin_memcpy(&u, &f, 4);
  unsigned s = (u >> 16) & 0x8000; int e = (int)((u >> 23) & 255) - 127 + 15; unsigned m = u & 0x7fffff;
  if (((u >> 23) & 255) == 255) return s | 0x7c00 | (m ? 0x200 : 0);
  if (e >= 31) return s | 0x7c00;
  if (e <= 0) { if (e < -10) return s; m |= 0x800000; unsigned sh = 14 - e; unsigned r = m >> sh, rem = m & ((1u << sh) - 1), half = 1u << (sh - 1); if (rem > half || (rem == half && (r & 1))) r++; return s | r; }
  unsigned r = (unsigned)(e << 10) | (m >> 13), rem = m & 0x1fff; if (rem > 0x1000 || (rem == 0x1000 && (r & 1))) r++; return s | r;
}
float zb_ldf16(const void *p) { unsigned short h; __builtin_memcpy(&h, p, 2); return zb_h2f(h); }
void zb_stf16(void *p, float v) { unsigned short h = (unsigned short)zb_f2h(v); __builtin_memcpy(p, &h, 2); }

/* ---- f80/f128 runtime: values live in 16-byte memory slots in their real format ---- */
typedef __float128 zbQ; typedef long double zbX;
static zbX ldx(const void *p) { zbX x; __builtin_memcpy(&x, p, 10); return x; }
static void stx(void *p, zbX x) { __builtin_memset(p, 0, 16); __builtin_memcpy(p, &x, 10); }
static zbQ ldq(const void *p) { zbQ q; __builtin_memcpy(&q, p, 16); return q; }
static void stq(void *p, zbQ q) { __builtin_memcpy(p, &q, 16); }
static zbQ q_trunc(zbQ a) { unsigned __int128 u; __builtin_memcpy(&u, &a, 16); int e = (int)((u >> 112) & 0x7fff) - 16383;
  if (e >= 112) return a; if (e < 0) { u &= (unsigned __int128)1 << 127; } else { u &= ~((((unsigned __int128)1) << (112 - e)) - 1); }
  zbQ r; __builtin_memcpy(&r, &u, 16); return r; }
static zbQ q_floor(zbQ a) { zbQ t = q_trunc(a); return (t != a && a < 0) ? t - 1 : t; }
static zbQ q_ceil(zbQ a) { zbQ t = q_trunc(a); return (t != a && a > 0) ? t + 1 : t; }
static zbQ q_round(zbQ a) { zbQ t = q_trunc(a), d = a - t; if (d >= (zbQ)0.5) return t + 1; if (d <= (zbQ)-0.5) return t - 1; return t; }
static zbQ q_fmod(zbQ a, zbQ b) { if (b == 0 || a != a || b != b || a - a != 0) return (a * b) / (a * b);
  zbQ x = a < 0 ? -a : a, y = b < 0 ? -b : b; if (x < y) return a;
  while (x >= y) { zbQ z = y; while (z * 2 <= x && z * 2 - z * 2 == 0) z *= 2; x -= z; }
  return a < 0 ? -x : x; }
static zbQ q_sqrt(zbQ a) { if (!(a > 0) || a - a != 0) return a == 0 || a - a != 0 ? a : (a - a) / (a - a); zbQ r = (zbQ)__builtin_sqrtl((zbX)a);
  r = (r + a / r) / 2; r = (r + a / r) / 2; return r; }
#define ZB_MATH(T, ld, st, TRUNC, FLOOR, CEIL, ROUND, FMOD, SQRT) \
  static void m_##T(int op, void *r, const void *pa, const void *pb) { T a = ld(pa), b = pb ? ld(pb) : 0, v = 0; switch (op) { \
    case 0: v = a + b; break; case 1: v = a - b; break; case 2: v = a * b; break; case 3: v = a / b; break; \
    case 4: v = FMOD(a, b); break; case 5: { T m = FMOD(a, b); if (m != 0 && ((m < 0) != (b < 0))) m += b; v = m; break; } \
    case 6: v = (a != a) ? b : (b != b) ? a : a < b ? a : b; break; case 7: v = (a != a) ? b : (b != b) ? a : a > b ? a : b; break; \
    case 8: v = -a; break; case 9: v = a < 0 || (a == 0 && 1 / a < 0) ? -a : a; break; case 10: v = SQRT(a); break; \
    case 11: v = FLOOR(a); break; case 12: v = CEIL(a); break; case 13: v = TRUNC(a); break; case 14: v = ROUND(a); break; \
    case 15: v = __builtin_sinl((zbX)a); break; case 16: v = __builtin_cosl((zbX)a); break; case 17: v = __builtin_tanl((zbX)a); break; \
    case 18: v = __builtin_expl((zbX)a); break; case 19: v = __builtin_exp2l((zbX)a); break; case 20: v = __builtin_powl(10, (zbX)a); break; \
    case 21: v = __builtin_logl((zbX)a); break; case 22: v = __builtin_log2l((zbX)a); break; case 23: v = __builtin_log10l((zbX)a); break; \
    case 24: v = (a / b); v = FLOOR(v); break; } st(r, v); }
ZB_MATH(zbX, ldx, stx, __builtin_truncl, __builtin_floorl, __builtin_ceill, __builtin_roundl, __builtin_fmodl, __builtin_sqrtl)
ZB_MATH(zbQ, ldq, stq, q_trunc, q_floor, q_ceil, q_round, q_fmod, q_sqrt)
void zb_fop(int bits, int op, void *r, const void *a, const void *b) { if (bits == 80) m_zbX(op, r, a, b); else m_zbQ(op, r, a, b); }
void zb_fma(int bits, void *r, const void *a, const void *b, const void *c) {
  if (bits == 80) stx(r, __builtin_fmal(ldx(a), ldx(b), ldx(c))); else stq(r, ldq(a) * ldq(b) + ldq(c)); }
int zb_fcmp(int bits, int op, const void *pa, const void *pb) {
  zbQ a = bits == 80 ? (zbQ)ldx(pa) : ldq(pa), b = bits == 80 ? (zbQ)ldx(pb) : ldq(pb);
  switch (op) { case 0: return a == b; case 1: return a != b; case 2: return a < b; case 3: return a <= b; case 4: return a > b; default: return a >= b; } }
void zb_fext(int bits, void *r, double v) { if (bits == 80) stx(r, v); else stq(r, v); }
double zb_fto64(int bits, const void *p) { return bits == 80 ? (double)ldx(p) : (double)ldq(p); }
float zb_fto32(int bits, const void *p) { return bits == 80 ? (float)ldx(p) : (float)ldq(p); }
void zb_fconv(int tob, void *r, int fromb, const void *p) { if (tob == 80) stx(r, fromb == 80 ? ldx(p) : (zbX)ldq(p)); else stq(r, fromb == 80 ? (zbQ)ldx(p) : ldq(p)); }
void zb_fromi(int bits, void *r, long v, int sg) { if (bits == 80) stx(r, sg ? (zbX)v : (zbX)(unsigned long)v); else stq(r, sg ? (zbQ)v : (zbQ)(unsigned long)v); }
void zb_fromi128(int bits, void *r, const void *p, int sg) { __int128 v; __builtin_memcpy(&v, p, 16);
  if (bits == 80) stx(r, sg ? (zbX)v : (zbX)(unsigned __int128)v); else stq(r, sg ? (zbQ)v : (zbQ)(unsigned __int128)v); }
long zb_toi(int bits, const void *p, int sg) { if (bits == 80) return sg ? (long)ldx(p) : (long)(unsigned long)ldx(p); return sg ? (long)ldq(p) : (long)(unsigned long)ldq(p); }
void zb_toi128(int bits, void *r, const void *p, int sg) { __int128 v;
  if (bits == 80) v = sg ? (__int128)ldx(p) : (__int128)(unsigned __int128)ldx(p); else v = sg ? (__int128)ldq(p) : (__int128)(unsigned __int128)ldq(p);
  __builtin_memcpy(r, &v, 16); }

/* 0.17 @bitCast logical bit stream helpers */
void zb_bitput(unsigned char *b, unsigned long off, unsigned long v, unsigned n) {
  for (unsigned i = 0; i < n; i++, off++) { if ((v >> i) & 1) b[off >> 3] |= (unsigned char)(1u << (off & 7)); else b[off >> 3] &= (unsigned char)~(1u << (off & 7)); }
}
unsigned long zb_bitget(const unsigned char *b, unsigned long off, unsigned n) {
  unsigned long v = 0; for (unsigned i = 0; i < n; i++, off++) v |= (unsigned long)((b[off >> 3] >> (off & 7)) & 1) << i; return v;
}
