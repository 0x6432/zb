#include "zb.h"
#include <execinfo.h>
#ifdef ZB_GC
#include <gc.h>
#define ZREALLOC GC_REALLOC
#else
#define ZREALLOC realloc
#endif

void vpush(Vec *v, void *x) {
  if (v->n == v->cap) { v->cap = v->cap ? v->cap * 2 : 8; v->a = ZREALLOC(v->a, v->cap * sizeof(void *)); }
  v->a[v->n++] = x;
}
#ifdef ZB_GC
void *xalloc_atomic(size_t n) { char *p = GC_MALLOC_ATOMIC(n); if (!p) die("oom"); memset(p, 0, n); return p; }
void *xalloc(size_t n) { void *p = GC_MALLOC(n); if (!p) die("oom"); return p; }
char *xstrndup(const char *s, size_t n) { char *p = GC_MALLOC_ATOMIC(n + 1); if (!p) die("oom"); memcpy(p, s, n); p[n] = 0; return p; }
char *fmt(const char *f, ...) {
  char tb[256]; va_list ap; va_start(ap, f); int n = vsnprintf(tb, sizeof tb, f, ap); va_end(ap); if (n < 0) die("oom");
  char *s = GC_MALLOC_ATOMIC(n + 1); if (!s) die("oom");
  if (n < (int)sizeof tb) memcpy(s, tb, n + 1); else { va_start(ap, f); vsnprintf(s, n + 1, f, ap); va_end(ap); }
  return s;
}
#else
void *xalloc(size_t n) { void *p = calloc(1, n); if (!p) die("oom"); return p; }
void *xalloc_atomic(size_t n) { return xalloc(n); }
char *xstrndup(const char *s, size_t n) { char *p = xalloc(n + 1); memcpy(p, s, n); return p; }
char *fmt(const char *f, ...) {
  va_list ap; va_start(ap, f); char *s; if (vasprintf(&s, f, ap) < 0) die("oom"); va_end(ap); return s;
}
#endif
_Noreturn void die(const char *f, ...) {
  va_list ap; va_start(ap, f); fprintf(stderr, "zb: "); vfprintf(stderr, f, ap); fprintf(stderr, "\n"); va_end(ap);
  { extern Node *gen_cur_pub(void); Node *g = gen_cur_pub(); if (g && g->tok) fprintf(stderr, "zb:   (while generating code at %s:%d)\n", g->tok->file, g->tok->line);
    extern FnInst *gen_cur_fi; int k = 0; for (FnInst *f = gen_cur_fi; f && k < 12; f = f->from, k++) if (f->from_node && f->from_node->tok) fprintf(stderr, "zb:   in %s, instantiated from %s:%d\n", f->d->name, f->from_node->tok->file, f->from_node->tok->line); }
  if (getenv("ZB_BT")) { void *b[64]; int k = backtrace(b, 64); backtrace_symbols_fd(b, k, 2); }
  exit(1);
}
char *read_file(const char *path, long *len) {
  FILE *f = fopen(path, "rb"); if (!f) return NULL;
  fseek(f, 0, SEEK_END); long n = ftell(f); fseek(f, 0, SEEK_SET);
  char *b = xstrndup("", 0); b = n ? xalloc_atomic(n + 1) : b; if (fread(b, 1, n, f) != (size_t)n) die("read %s", path); fclose(f);
  if (len) *len = n; return b;
}

static const char *kws[] = { "addrspace","align","allowzero","and","anyframe","anytype","asm",
 "break","callconv","catch","comptime","const","continue","defer","else","enum","errdefer",
 "error","export","extern","fn","for","if","inline","linksection","noalias","noinline","nosuspend",
 "opaque","or","orelse","packed","pub","resume","return","struct","suspend","switch","test",
 "threadlocal","try","union","unreachable","usingnamespace","var","volatile","while", 0 };
static const char *puncts[] = { "<<|=", "<<=", ">>=", "+%=", "-%=", "*%=", "+|=", "-|=", "*|=", "<<|",
 "...", "**", "++", "||", "+%", "-%", "*%", "+|", "-|", "*|", "+=", "-=", "*=", "/=", "%=", "&=", "|=",
 "^=", "<<", ">>", "==", "!=", "<=", ">=", "=>", "->", "..", ".*", ".?", 0 };

static void utf8(char *buf, int *n, uint32_t c) {
  if (c < 0x80) buf[(*n)++] = c;
  else if (c < 0x800) { buf[(*n)++] = 0xC0 | (c >> 6); buf[(*n)++] = 0x80 | (c & 63); }
  else if (c < 0x10000) { buf[(*n)++] = 0xE0 | (c >> 12); buf[(*n)++] = 0x80 | ((c >> 6) & 63); buf[(*n)++] = 0x80 | (c & 63); }
  else { buf[(*n)++] = 0xF0 | (c >> 18); buf[(*n)++] = 0x80 | ((c >> 12) & 63); buf[(*n)++] = 0x80 | ((c >> 6) & 63); buf[(*n)++] = 0x80 | (c & 63); }
}
static int hexv(int c) { return isdigit(c) ? c - '0' : (tolower(c) - 'a' + 10); }
/* parse one escape at p (after backslash); returns codepoint/byte, sets *isbyte */
static uint32_t esc(const char **pp, int *isbyte) {
  const char *p = *pp; uint32_t v = 0; *isbyte = 0;
  switch (*p++) {
  case 'n': v = 10; break; case 'r': v = 13; break; case 't': v = 9; break;
  case '\\': v = '\\'; break; case '\'': v = '\''; break; case '"': v = '"'; break;
  case 'x': v = hexv(p[0]) * 16 + hexv(p[1]); p += 2; *isbyte = 1; break;
  case 'u': p++; while (*p != '}') v = v * 16 + hexv(*p++); p++; break;
  default: die("bad escape");
  }
  *pp = p; return v;
}

/* identifier / punctuator strings are interned: tokens are kept for the whole compilation */
static char **itab; static size_t icap, icnt;
static char *intern(const char *s, size_t n) {
  if (icnt * 2 >= icap) { size_t nc = icap ? icap * 2 : 65536; char **nt = xalloc(nc * sizeof(char *));
    for (size_t i = 0; i < icap; i++) if (itab[i]) { unsigned h = 2166136261u; for (const char *q = itab[i]; *q; q++) h = (h ^ (unsigned char)*q) * 16777619u; size_t j = h & (nc - 1); while (nt[j]) j = (j + 1) & (nc - 1); nt[j] = itab[i]; }
    itab = nt; icap = nc; }
  unsigned h = 2166136261u; for (size_t i = 0; i < n; i++) h = (h ^ (unsigned char)s[i]) * 16777619u;
  size_t j = h & (icap - 1);
  while (itab[j]) { if (!strncmp(itab[j], s, n) && !itab[j][n]) return itab[j]; j = (j + 1) & (icap - 1); }
  icnt++; return itab[j] = xstrndup(s, n);
}
Tok *lex(const char *file, const char *src, int *ntok) {
  int cap = 1024, n = 0, line = 1; Tok *t = xalloc(cap * sizeof(Tok));
  const char *p = src;
  for (;;) {
    if (n + 2 >= cap) { cap *= 2; t = ZREALLOC(t, cap * sizeof(Tok)); }
    while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') { if (*p == '\n') line++; p++; }
    if (p[0] == '/' && p[1] == '/') { while (*p && *p != '\n') p++; continue; }
    Tok *k = &t[n]; memset(k, 0, sizeof *k); k->line = line; k->file = file;
    if (!*p) { k->k = TK_EOF; k->s = ""; n++; break; }
    if (isalpha((unsigned char)*p) || *p == '_') {
      const char *s = p; while (isalnum((unsigned char)*p) || *p == '_') p++;
      k->s = intern(s, p - s); k->len = p - s; k->k = TK_ID;
      for (int i = 0; kws[i]; i++) if (!strcmp(kws[i], k->s)) k->k = TK_KW;
      n++; continue;
    }
    if (*p == '@') {
      p++;
      if (*p == '"') { /* @"ident" */
        p++; char buf[1024]; int m = 0;
        while (*p != '"') { if (*p == '\\') { p++; int b; uint32_t c = esc(&p, &b); if (b) buf[m++] = c; else utf8(buf, &m, c); } else buf[m++] = *p++; }
        p++; k->k = TK_ID; k->s = xstrndup(buf, m); k->len = m; k->ival = 1; n++; continue;
      }
      const char *s = p; while (isalnum((unsigned char)*p) || *p == '_') p++;
      k->k = TK_BUILTIN; k->s = intern(s, p - s); n++; continue;
    }
    if (isdigit((unsigned char)*p)) {
      unsigned __int128 v = 0; int base = 10;
      if (p[0] == '0' && (p[1] == 'x' || p[1] == 'o' || p[1] == 'b')) { base = p[1] == 'x' ? 16 : p[1] == 'o' ? 8 : 2; p += 2; }
      for (;; p++) {
        if (*p == '_') continue;
        int d;
        if (isdigit((unsigned char)*p)) d = *p - '0';
        else if (base == 16 && isxdigit((unsigned char)*p)) d = hexv(*p);
        else break;
        v = v * base + d;
      }
      if ((*p == '.' && isxdigit((unsigned char)p[1]) && (base == 16 || isdigit((unsigned char)p[1]))) || (base == 10 && (*p == 'e' || *p == 'E')) || (base == 16 && (*p == 'p' || *p == 'P'))) {
        const char *q = p; while (isalnum((unsigned char)*q) || *q == '.' || *q == '_' || ((*q == '+' || *q == '-') && strchr("eEpP", q[-1]))) q++;
        const char *st = p; while (st > src && (isalnum((unsigned char)st[-1]) || st[-1] == '_' || st[-1]=='.')) st--;
        char buf[128]; int m = 0; for (const char *r = st; r < q && m < 127; r++) if (*r != '_') buf[m++] = *r; buf[m] = 0;
        k->k = TK_FLOAT; k->fval = parse_f128(buf); k->s = xstrndup(buf, m); p = q; n++; continue;
      }
      k->k = TK_INT; k->ival = v; n++; continue;
    }
    if (*p == '\'') {
      p++; uint32_t c;
      if (*p == '\\') { p++; int b; c = esc(&p, &b); }
      else { /* utf8 decode */
        unsigned char u = *p;
        if (u < 0x80) { c = u; p++; }
        else { int len = u >= 0xF0 ? 4 : u >= 0xE0 ? 3 : 2; c = u & (0x7F >> len); p++; for (int i = 1; i < len; i++) c = (c << 6) | (*p++ & 63); }
      }
      p++; k->k = TK_CHAR; k->ival = c; n++; continue;
    }
    if (*p == '"' || (p[0] == '\\' && p[1] == '\\')) {
      int cap2 = 256, m = 0; char *buf = xalloc(cap2);
      if (*p == '"') {
        p++;
        while (*p != '"') {
          if (m + 8 >= cap2) { cap2 *= 2; buf = ZREALLOC(buf, cap2); }
          if (*p == '\\') { p++; int b; uint32_t c = esc(&p, &b); if (b) buf[m++] = c; else utf8(buf, &m, c); }
          else buf[m++] = *p++;
        }
        p++;
      } else {
        int first = 1;
        for (;;) {
          const char *q = p;
          for (;;) { while (*q == ' ' || *q == '\t' || *q == '\r' || *q == '\n') q++; if (!first && q[0] == '/' && q[1] == '/') { while (*q && *q != '\n') q++; continue; } break; }
          if (!(q[0] == '\\' && q[1] == '\\')) break;
          for (const char *r = p; r < q; r++) if (*r == '\n') line++;
          p = q + 2; if (!first) buf[m++] = '\n'; first = 0;
          while (*p && *p != '\n') { if (m + 8 >= cap2) { cap2 *= 2; buf = ZREALLOC(buf, cap2); } if (*p != '\r') buf[m++] = *p; p++; }
        }
      }
      buf[m] = 0; k->k = TK_STR; k->s = buf; k->len = m; n++; continue;
    }
    int done = 0;
    for (int i = 0; puncts[i]; i++) {
      int l = strlen(puncts[i]);
      if (!strncmp(p, puncts[i], l)) { k->k = TK_P; k->s = (char *)puncts[i]; p += l; done = 1; break; }
    }
    if (!done) { k->k = TK_P; k->s = intern(p, 1); p++; }
    n++;
  }
  { Tok *e = xalloc((n + 1) * sizeof(Tok)); memcpy(e, t, (n + 1) * sizeof(Tok)); t = e; } /* trim */
  *ntok = n; return t;
}

/* decimal/hex float literal -> binary128 (comptime_float precision) */
f128 parse_f128(const char *s) {
  if (s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) {
    unsigned __int128 m = 0; int e = 0, any = 0; const char *p = s + 2; int dot = 0, drop = 0;
    for (; *p; p++) {
      if (*p == '.') { dot = 1; continue; }
      if (!isxdigit((unsigned char)*p)) break;
      int d = isdigit((unsigned char)*p) ? *p - '0' : (tolower(*p) - 'a' + 10);
      if (m >> 120) { drop++; if (dot) drop--; else e += 0; if (!dot) e += 4; continue; }
      m = m * 16 + d; any = 1; if (dot) e -= 4;
    }
    (void)drop; (void)any;
    if (*p == 'p' || *p == 'P') { e += atoi(p + 1); }
    f128 r = (f128)m; while (e > 0) { r *= 2; e--; } while (e < 0) { r /= 2; e++; }
    return r;
  }
  unsigned __int128 m = 0; int e = 0, nd = 0; const char *p = s; int dot = 0;
  for (; *p; p++) {
    if (*p == '.') { dot = 1; continue; }
    if (!isdigit((unsigned char)*p)) break;
    if (nd < 38) { m = m * 10 + (*p - '0'); if (m) nd++; if (dot) e--; }
    else if (!dot) e++;
  }
  if (*p == 'e' || *p == 'E') e += atoi(p + 1);
  f128 r = (f128)m;
  if (m == 0) return 0;
  /* scale by 10^|e| using exact powers where possible */
  f128 p10 = 1, base = 10; int ae = e < 0 ? -e : e;
  if (ae > 4966) return e < 0 ? 0 : r * (f128)INFINITY;
  while (ae) { if (ae & 1) p10 *= base; base *= base; ae >>= 1; }
  return e < 0 ? r / p10 : r * p10;
}
