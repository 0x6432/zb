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
