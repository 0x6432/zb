#include "zb.h"
#include <malloc.h>

FILE *outf;
static FILE *fb, *ab, *db, *xb; /* fn body, allocs, data, extra fns */

static int tmpc, lblc, term, strc;
typedef struct { Type *t; char *op; int lv; int ck; CVal cv; int bf, bitoff, hbytes; } Val; /* bf: bit-field lvalue in a packed host of hbytes at op */
typedef struct Defer { Node *n; int err; Scope *s; char *cap; } Defer;
typedef struct Res { Type *t; char *slot; int has; Type *ex; int collect; } Res;
typedef struct Inl { Res *res; char *lx; int dbase, nret, allck, level; CVal ckv; } Inl;
static Inl *inl;
typedef struct Loop { char *label, *brk, *cont; Res *res; int dbase, kind, cont_used, brk_used; char *swslot, *swdisp; Type *swt; struct Loop *up; } Loop;
static Vec defers; static Loop *loops; static Type *fret; static char *fsret;
static Vec queue;

static Val gen(Node *n, Scope *s, Type *ex);
static Val coerce(Val v, Type *to);
Node *gen_cur_pub(void);
static int is_wide(Type *t);
static Type *typeof_impl(Node *n, Scope *s); static Type *typeof_ex(Node *n, Scope *s, Type *ex); static FILE *devnull;
static int in_typeof; static Loop *typeof_outer;

/* ---------- emission ---------- */
static char *strdata(const char *s, int n);
extern Node *gen_cur_pub(void);
static int dbg_on = -1, dbg_line; static char *dbg_file;
static void emit(const char *f, ...) {
  if (term) { fprintf(fb, "@L%d\n", ++lblc); term = 0; }
  if (dbg_on) { Node *cn = gen_cur_pub(); if (cn && cn->tok && cn->tok->file == dbg_file && cn->tok->line != dbg_line) { dbg_line = cn->tok->line; fprintf(fb, "\tdbgloc %d\n", dbg_line); } }
  if (!strcmp(f, "hlt") && getenv("ZB_TRAPLOC")) { Node *cn = gen_cur_pub(); char *m = fmt("trap at %s:%d\n", cn ? cn->tok->file : "?", cn ? cn->tok->line : 0); fprintf(fb, "\tcall $zb_trapbt(l %s, l %d)\n", strdata(m, (int)strlen(m)), (int)strlen(m)); }
  va_list ap; va_start(ap, f); fputc('\t', fb); vfprintf(fb, f, ap); fputc('\n', fb); va_end(ap);
}
static char *newl(void) { return fmt("L%d", ++lblc); }
static void label(char *l) { fprintf(fb, "@%s\n", l); term = 0; }
static void jmp(char *l) { if (!term) emit("jmp @%s", l); term = 1; }
static void br(char *c, char *a, char *b) { emit("jnz %s, @%s, @%s", c, a, b); term = 1; }
static char *tmp(void) { return fmt("%%t%d", ++tmpc); }
static char qc(Type *t) {
  if (t->k == TY_FLOAT) { if (t->bits == 32) return 's'; if (t->bits == 64) return 'd'; return t->bits == 16 ? 's' : 'l'; /* f16 in 's', f80/f128 in 'd' registers; memory via zbrt shims */ }
  if (t->k == TY_CFLOAT) return 'd';
  if (is_aggr(t)) return 'l'; return tsize(t) == 8 ? 'l' : 'w'; }
static char *slot(Type *t) {
  char *n = tmp(); int a = talign(t), s = tsize(t); if (s < 1) s = 1;
  fprintf(ab, "\t%s =l alloc%d %d\n", n, a >= 16 ? 16 : a > 4 ? 8 : 4, s); return n;
}
static void blit(char *src, char *dst, int n) { if (n > 0) emit("blit %s, %s, %d", src, dst, n); }
static char *load(Type *t, char *addr) {
  int s = tsize(t); if (!s) return "0";
  int sg = t->k == TY_INT && t->sign; char *r = tmp();
  const char *ins = s == 1 ? (sg ? "loadsb" : "loadub") : s == 2 ? (sg ? "loadsh" : "loaduh") : s == 4 ? "loadw" : "loadl";
  if (t->k == TY_FLOAT && t->bits > 64) { char *sl = slot(t); blit(addr, sl, 16); return sl; }
  if (t->k == TY_FLOAT && t->bits != 32 && t->bits != 64) { emit("%s =%c call $zb_ldf%d(l %s)", r, qc(t), t->bits, addr); return r; }
  if (t->k == TY_FLOAT) ins = qc(t) == 's' ? "loads" : "loadd";
  emit("%s =%c %s %s", r, qc(t), ins, addr); return r;
}
static void store(Type *t, char *v, char *addr) {
  int s = tsize(t); if (!s) return;
  if (t->k == TY_FLOAT && t->bits > 64) { blit(v, addr, 16); return; }
  if (t->k == TY_FLOAT && t->bits != 32 && t->bits != 64) { emit("call $zb_stf%d(l %s, %c %s)", t->bits, addr, qc(t), v); return; }
  if (t->k == TY_FLOAT) { emit("store%c %s, %s", qc(t), v, addr); return; }
  emit("store%s %s, %s", s == 1 ? "b" : s == 2 ? "h" : s == 4 ? "w" : "l", v, addr);
}
static char *addp(char *a, int64_t off) { if (!off) return a; char *r = tmp(); emit("%s =l add %s, %lld", r, a, (long long)off); return r; }
static char *norm(char *v, Type *t) {
  if (t->k != TY_INT) return v; int b = t->bits; char c = qc(t);
  if (b == 32 || b == 64) return v;
  char *r = tmp();
  if (b == 8) emit("%s =w %s %s", r, t->sign ? "extsb" : "extub", v);
  else if (b == 16) emit("%s =w %s %s", r, t->sign ? "extsh" : "extuh", v);
  else if (!t->sign) emit("%s =%c and %s, %llu", r, c, v, (unsigned long long)((1ULL << b) - 1));
  else { char *q = tmp(); int sh = (c == 'w' ? 32 : 64) - b; emit("%s =%c shl %s, %d", q, c, v, sh); emit("%s =%c sar %s, %d", r, c, q, sh); }
  return r;
}

/* ---------- values ---------- */
static Val V(Type *t, char *op) { Val v; memset(&v, 0, sizeof v); v.t = t; v.op = op; return v; }
static Val LV(Type *t, char *a) { Val v = V(t, a); v.lv = 1; return v; }
static Val VOIDV(void) { return V(t_void, "0"); }
static Val NORET(void) { return V(t_noret, "0"); }
static Val CK(CVal c) { Val v; memset(&v, 0, sizeof v); v.ck = 1; v.cv = c; v.t = cv_typeof(&c); if (c.k == CV_VOID) { v.ck = 0; v.op = "0"; } return v; }
static int is_ctonly(Type *t) { return t->k == TY_CINT || t->k == TY_CFLOAT || t->k == TY_TYPE || t->k == TY_ENUMLIT || t->k == TY_NULL || t->k == TY_UNDEF || t->k == TY_ANYTYPE; }

static void data_bytes(FILE *f, const char *s, int n) {
  int instr = 0, any = 0;
  for (int i = 0; i < n; i++) {
    unsigned char c = s[i];
    if (c >= 32 && c < 127 && c != '"' && c != '\\') { if (!instr) { fprintf(f, "%sb \"", any ? ", " : ""); instr = 1; } fputc(c, f); }
    else { if (instr) { fputc('"', f); instr = 0; } fprintf(f, "%sb %d", any ? ", " : "", c); }
    any = 1;
  }
  if (instr) fputc('"', f);
}
static char *strdata(const char *s, int n) {
  char *nm = fmt("$zbs%d", ++strc);
  fprintf(db, "data %s = { ", nm); data_bytes(db, s, n); fprintf(db, "%sb 0 }\n", n ? ", " : ""); return nm;
}
/* ---------- comptime value -> static data ---------- */
static FnInst *plain_inst(Decl *d);
static void **pm_k; static char **pm_v; static int pm_cap, pm_n; static int datac;
static char *pm_get(void *k) {
  if (!pm_cap) return NULL;
  unsigned h = (unsigned)(((uintptr_t)k >> 4) * 2654435761u) & (pm_cap - 1);
  while (pm_k[h]) { if (pm_k[h] == k) return pm_v[h]; h = (h + 1) & (pm_cap - 1); }
  return NULL;
}
static void pm_put(void *k, char *v) {
  if (pm_n * 2 >= pm_cap) {
    int oc = pm_cap; void **ok = pm_k; char **ov = pm_v; pm_cap = oc ? oc * 2 : 256;
    pm_k = xalloc(sizeof(void *) * pm_cap); pm_v = xalloc(sizeof(char *) * pm_cap); pm_n = 0;
    for (int i = 0; i < oc; i++) if (ok[i]) pm_put(ok[i], ov[i]);
  }
  unsigned h = (unsigned)(((uintptr_t)k >> 4) * 2654435761u) & (pm_cap - 1);
  while (pm_k[h]) h = (h + 1) & (pm_cap - 1);
  pm_k[h] = k; pm_v[h] = v; pm_n++;
}
static void ser(FILE *f, int *first, CVal *v, Type *t);
static char *cell_sym(CVal *cell, Type *t);
static void ditem(FILE *f, int *first, const char *fm, ...) {
  if (!*first) fputs(", ", f); *first = 0;
  va_list ap; va_start(ap, fm); vfprintf(f, fm, ap); va_end(ap);
}
static void dz(FILE *f, int *first, int64_t n) { if (n > 0) ditem(f, first, "z %lld", (long long)n); }
static void ser_int(FILE *f, int *first, int sz, i128 v) {
  if (sz <= 0) return;
  if (sz <= 8) { ditem(f, first, "%c %lld", sz == 1 ? 'b' : sz == 2 ? 'h' : sz == 4 ? 'w' : 'l', (long long)(int64_t)v); return; }
  for (int i = 0; i < sz / 8; i++) ditem(f, first, "l %lld", (long long)(int64_t)(i < 2 ? (v >> (64 * i)) : (v < 0 ? -1 : 0)));
}
static char *str_sym(CVal *sc) {
  char *nm = pm_get(sc); if (nm) return nm;
  nm = strdata(sc->s, sc->slen); pm_put(sc, nm); return nm;
}
/* address of a comptime pointer as symbol + offset */
static char *ptr_parts(CVal *p, int64_t *off) {
  *off = 0;
  if (p->k == CV_STR) return strdata(p->s, p->slen);
  if (!p->base) { if (p->s) { *off = (int64_t)p->i; return fmt("$%s", p->s); } return NULL; }
  CVal *b = p->base;
  if (b->k == CV_STR) { *off = p->idx < 0 ? 0 : p->idx; return str_sym(b); }
  Type *bt = cv_typeof(b);
  if (bt->k == TY_CINT || bt->k == TY_UNDEF) bt = p->t && (p->t->k == TY_PTR || p->t->k == TY_MPTR || p->t->k == TY_SLICE) ? p->t->elem : t_i64;
  if (p->idx >= 0) { Type *et = bt->k == TY_ARRAY ? bt->elem : bt; *off = p->idx * tsize(et); }
  int fi; CVal *par;
  while ((par = cell_parent(b, &fi))) {
    Type *pt = cv_typeof(par); if (!pt || (pt->k != TY_STRUCT && pt->k != TY_UNION)) break;
    if (fi >= 0) { layout(pt->ct); *off += ((Field *)pt->ct->fields.a[fi])->off; }
    b = par; bt = pt;
  }
  return cell_sym(b, bt);
}
static void ser_ptr(FILE *f, int *first, CVal *v) {
  int64_t off; char *sym;
  switch (v->k) {
  case CV_PTR: case CV_SLICE: case CV_STR:
    sym = ptr_parts(v, &off); if (!sym) { ditem(f, first, "l 0"); return; }
    if (off) ditem(f, first, "l %s + %lld", sym, (long long)off); else ditem(f, first, "l %s", sym); return;
  case CV_FN: ditem(f, first, "l $%s", plain_inst(v->fn)->sym); return;
  case CV_INT: case CV_NULL: case CV_UNDEF: ditem(f, first, "l %lld", (long long)(int64_t)v->i); return;
  default: die("cannot materialize comptime value kind %d as a pointer", v->k);
  }
}
static void ser(FILE *f, int *first, CVal *v, Type *t) {
  int sz = tsize(t);
  if (sz <= 0 || type_is_ctonly(t)) return;
  if (v->k == CV_UNDEF || v->k == CV_NONE) { dz(f, first, sz); return; }
  switch (t->k) {
  case TY_INT: case TY_BOOL: case TY_ERRSET: case TY_ENUM:
    if (v->k == CV_AGG && t->k == TY_ENUM && v->t->k == TY_UNION) { ser_int(f, first, sz, ((Field *)v->t->ct->fields.a[v->i])->val); return; }
    ser_int(f, first, sz, v->i); return;
  case TY_PTR: case TY_MPTR: case TY_FN: ser_ptr(f, first, v); return;
  case TY_FLOAT: ser_int(f, first, sz, f_to_bits(v->k == CV_FLOAT ? v->f : (f128)v->i, t->bits)); return;
  case TY_OPT:
    if (v->k == CV_NULL) { dz(f, first, sz); return; }
    if (opt_is_ptr(t)) { ser_ptr(f, first, v); return; }
    ser(f, first, v, t->elem); ditem(f, first, "b 1"); dz(f, first, sz - tsize(t->elem) - 1); return;
  case TY_ERRU:
    if (v->k == CV_ERR) { ser_int(f, first, 2, v->i); dz(f, first, sz - 2); return; }
    ser_int(f, first, 2, 0); dz(f, first, erru_off(t) - 2); ser(f, first, v, t->elem); dz(f, first, sz - erru_off(t) - tsize(t->elem)); return;
  case TY_SLICE: {
    int64_t len = v->k == CV_STR ? v->slen : v->k == CV_SLICE ? v->slen : 0;
    if (v->k == CV_PTR && v->t && v->t->k == TY_PTR && v->t->elem->k == TY_ARRAY) len = v->t->elem->len;
    ser_ptr(f, first, v); ditem(f, first, "l %lld", (long long)len); return;
  }
  case TY_ARRAY: {
    int es = tsize(t->elem); int64_t w = 0;
    if (v->k == CV_STR) { int n = v->slen < t->len ? v->slen : (int)t->len; if (n > 0) { if (!*first) fputs(", ", f); *first = 0; data_bytes(f, v->s, n); } w = n; }
    else if (v->k == CV_AGG) { for (int i = 0; i < v->n && i < t->len; i++) ser(f, first, v->el[i], t->elem); w = (int64_t)(v->n < t->len ? v->n : t->len) * es; }
    else if (v->k == CV_INT || v->k == CV_BOOL) { for (int64_t i = 0; i < t->len; i++) ser(f, first, v, t->elem); w = t->len * es; }
    else die("cannot materialize comptime value kind %d as %s", v->k, tname(t));
    if (t->hassent && w == t->len * es) { ser_int(f, first, es, t->sent); w += es; }
    dz(f, first, sz - w); return;
  }
  case TY_STRUCT: case TY_TUPLE: {
    if (v->k != CV_AGG) die("cannot materialize comptime value kind %d as %s", v->k, tname(t));
    layout(t->ct);
    if (is_packed(t)) { ser_int(f, first, sz, cv_pack(v)); return; }
    int pos = 0;
    for (int i = 0; i < t->ct->fields.n && i < v->n; i++) {
      Field *fl = t->ct->fields.a[i]; if (type_is_ctonly(fl->t) || !tsize(fl->t)) continue;
      dz(f, first, fl->off - pos); ser(f, first, v->el[i], fl->t); pos = fl->off + tsize(fl->t);
    }
    dz(f, first, sz - pos); return;
  }
  case TY_UNION: {
    if (v->k != CV_AGG || v->i < 0) { dz(f, first, sz); return; }
    layout(t->ct); Field *fl = t->ct->fields.a[v->i]; int ps = type_is_ctonly(fl->t) ? 0 : tsize(fl->t);
    if (ps) ser(f, first, v->el[0], fl->t);
    if (t->ct->tagged) { int to = union_tag_off(t); dz(f, first, to - ps); ser_int(f, first, tsize(t->ct->tag), fl->val); dz(f, first, sz - to - tsize(t->ct->tag)); }
    else dz(f, first, sz - ps);
    return;
  }
  default: dz(f, first, sz); return;
  }
}
static char *emit_data(CVal *v, Type *t, char *nm) {
  char *buf; size_t bsz; FILE *f = open_memstream(&buf, &bsz); int first = 1;
  ser(f, &first, v, t); if (first) fputs("z 1", f); fclose(f);
  int al = talign(t); if (al < 1) al = 1; if (al > 16) al = 16;
  fprintf(db, "data %s = align %d { %s }\n", nm, al, buf); free(buf); return nm;
}
static char *cell_sym(CVal *cell, Type *t) {
  char *nm = pm_get(cell); if (nm) return nm;
  nm = fmt("$zbc%d", ++datac); pm_put(cell, nm);
  return emit_data(cell, t, nm);
}
static char *cv_data(CVal *v, Type *t) { return emit_data(v, t, fmt("$zbc%d", ++datac)); }
static int ck_ok(CVal *r, Type *to) {
  if (r->k == CV_UNDEF) return 1;
  switch (to->k) {
  case TY_OPT: return r->k == CV_NULL || ck_ok(r, to->elem);
  case TY_ERRU: return r->k == CV_ERR || ck_ok(r, to->elem);
  case TY_INT: case TY_CINT: return r->k == CV_INT;
  case TY_FLOAT: case TY_CFLOAT: return r->k == CV_FLOAT;
  case TY_ENUM: return r->k == CV_INT;
  case TY_BOOL: return r->k == CV_BOOL;
  case TY_ERRSET: return r->k == CV_ERR;
  case TY_TYPE: return r->k == CV_TYPE;
  case TY_VOID: return r->k == CV_VOID;
  case TY_PTR: case TY_MPTR: return r->k == CV_PTR || r->k == CV_STR || r->k == CV_INT || r->k == CV_FN || (r->k == CV_SLICE && to->k == TY_MPTR);
  case TY_SLICE: return r->k == CV_SLICE || r->k == CV_STR || (r->k == CV_PTR && r->t && r->t->k == TY_PTR && r->t->elem->k == TY_ARRAY);
  case TY_ARRAY: case TY_STRUCT: case TY_UNION: case TY_TUPLE: return r->k == CV_AGG && (r->t == to || (tsize(r->t) == tsize(to) && r->t->k == to->k));
  case TY_FN: return r->k == CV_FN;
  case TY_ENUMLIT: return r->k == CV_ENUMLIT;
  case TY_NULL: return r->k == CV_NULL;
  default: return 0;
  }
}
void queue_fn(FnInst *fi);
static FnInst *plain_inst(Decl *d) {
  Vec c = {0}; for (int i = 0; i < d->node->list.n; i++) vpush(&c, NULL); FnInst *fi = fn_instance(d, &c); queue_fn(fi); return fi;
}
static char *mat(Val v) {
  if (!v.ck) return v.op;
  if (v.t && v.t->k == TY_FLOAT && v.t->bits > 64 && (v.cv.k == CV_FLOAT || v.cv.k == CV_INT)) return cv_data(&v.cv, v.t);
  switch (v.cv.k) {
  case CV_INT: case CV_BOOL: case CV_ERR: return fmt("%lld", (long long)v.cv.i);
  case CV_NULL: case CV_UNDEF: return "0";
  case CV_FLOAT: { Type *t = v.t && v.t->k == TY_FLOAT ? v.t : t_f64; return qc(t) == 's' ? fmt("s_%a", (double)(float)v.cv.f) : fmt("d_%a", (double)v.cv.f); }
  case CV_FN: return fmt("$%s", plain_inst(v.cv.fn)->sym);
  case CV_STR: return strdata(v.cv.s, v.cv.slen);
  case CV_PTR: case CV_SLICE: { int64_t off; char *sym = ptr_parts(&v.cv, &off); if (!sym) return fmt("%lld", (long long)off); return addp(sym, off); }
  case CV_ENUMLIT: die("enum literal .%s has no result type", v.cv.s);
  case CV_TYPE: die("type %s used as a runtime value", tname(v.cv.t));
  default: { Node *cn = gen_cur_pub(); die("%s:%d: cannot use comptime value (kind %d, %s) at runtime", cn ? cn->tok->file : "?", cn ? cn->tok->line : 0, v.cv.k, tname(v.t)); }
  }
}
static Type *host_int(int bytes) { return int_type(bytes * 8, 0); }
static Val w_from_parts(Type *t, char *lo, char *hi); static Val wconv(Val v, Type *to); static Val w_arith(const char *op, Type *t, Val a, Val b);
static char *wlo(Val v); static char *whi(Val v); static char *addr_of(Val v);
static int bf_needs_wide(Val *v) { /* field does not fit an 8-byte window of its host */
  if (v->hbytes <= 8) return 0;
  int nb = bits_of(v->t), b0 = v->bitoff / 8; if (b0 + 8 > v->hbytes) b0 = v->hbytes - 8;
  return v->bitoff - b0 * 8 + nb > 64;
}
static Val bf_wide_window(Val *v, char **base, int *bo) { /* 16-byte window (u128) containing the field */
  int b0 = v->bitoff / 8; if (b0 + 16 > v->hbytes) b0 = v->hbytes - 16; if (b0 < 0) b0 = 0;
  *bo = v->bitoff - b0 * 8; *base = addp(v->op, b0);
  if (v->hbytes - b0 >= 16) return w_from_parts(int_type(128, 0), load(t_u64, *base), load(t_u64, addp(*base, 8)));
  char *sl = slot(int_type(128, 0)); store(t_u64, "0", sl); store(t_u64, "0", addp(sl, 8));
  emit("call $memcpy(l %s, l %s, l %d)", sl, *base, v->hbytes - b0); return V(int_type(128, 0), sl);
}
static void bf_window(Val *v) { /* hosts wider than 64 bits: use an (unaligned) 8-byte window containing the field */
  if (v->hbytes <= 8) return;
  int nb = bits_of(v->t), b0 = v->bitoff / 8; if (b0 + 8 > v->hbytes) b0 = v->hbytes - 8;
  int bo = v->bitoff - b0 * 8; if (bo + nb > 64) die("packed field of %d bits at bit %d of a %d-byte host is not supported at runtime", nb, v->bitoff, v->hbytes);
  v->op = addp(v->op, b0); v->hbytes = 8; v->bitoff = bo;
}
static char *bf_load(Val v) { /* returns field bits as an integer of the field's int width */
  if (bf_needs_wide(&v)) {
    char *base; int bo; Val w = bf_wide_window(&v, &base, &bo); int nb = bits_of(v.t);
    if (bo) { CVal sc = {0}; sc.k = CV_INT; sc.t = t_cint; sc.i = bo; w = w_arith(">>", int_type(128, 0), w, CK(sc)); }
    Type *ft = v.t->k == TY_INT ? v.t : int_type(nb, 0);
    return wconv(w, ft).op;
  }
  bf_window(&v); Type *h = host_int(v.hbytes);
  char *x = load(h, v.op); char c = qc(h); int nb = bits_of(v.t);
  if (v.bitoff) { char *y = tmp(); emit("%s =%c shr %s, %d", y, c, x, v.bitoff); x = y; }
  Type *ft = v.t->k == TY_INT ? v.t : int_type(nb, 0); char fc = qc(ft);
  if (fc == 'l' && c == 'w') { char *y = tmp(); emit("%s =l extuw %s", y, x); x = y; }
  else if (fc == 'w' && c == 'l') { char *y = tmp(); emit("%s =w copy %s", y, x); x = y; }
  if (nb < (fc == 'l' ? 64 : 32)) {
    if (ft->sign) { char *q = tmp(), *r = tmp(); int sh = (fc == 'l' ? 64 : 32) - nb; emit("%s =%c shl %s, %d", q, fc, x, sh); emit("%s =%c sar %s, %d", r, fc, q, sh); x = r; }
    else { char *r = tmp(); emit("%s =%c and %s, %llu", r, fc, x, (unsigned long long)((1ULL << nb) - 1)); x = r; }
  }
  return x;
}
static void bf_store(Val l, char *v) { /* v: integer operand holding the field bits */
  if (bf_needs_wide(&l)) {
    char *base; int bo; Val w = bf_wide_window(&l, &base, &bo); int nb = bits_of(l.t); Type *U = int_type(128, 0);
    Type *ft = l.t->k == TY_INT ? l.t : int_type(nb, 0);
    Val fv = wconv(V(ft, v), U);
    unsigned __int128 m = nb >= 128 ? ~(unsigned __int128)0 : (((unsigned __int128)1 << nb) - 1);
    unsigned __int128 hm = m << bo, keep = ~hm;
    Val mv = w_from_parts(U, fmt("%llu", (unsigned long long)m), fmt("%llu", (unsigned long long)(m >> 64)));
    Val kv = w_from_parts(U, fmt("%llu", (unsigned long long)keep), fmt("%llu", (unsigned long long)(keep >> 64)));
    fv = w_arith("&", U, fv, mv);
    if (bo) { CVal sc = {0}; sc.k = CV_INT; sc.t = t_cint; sc.i = bo; fv = w_arith("<<", U, fv, CK(sc)); }
    Val r = w_arith("|", U, w_arith("&", U, w, kv), fv);
    int b0 = l.bitoff / 8; if (b0 + 16 > l.hbytes) b0 = l.hbytes - 16; if (b0 < 0) b0 = 0;
    if (l.hbytes - b0 >= 16) { store(t_u64, wlo(r), base); store(t_u64, whi(r), addp(base, 8)); }
    else emit("call $memcpy(l %s, l %s, l %d)", base, addr_of(r), l.hbytes - b0);
    return;
  }
  bf_window(&l); Type *h = host_int(l.hbytes);
  char c = qc(h); int nb = bits_of(l.t); Type *ft = l.t->k == TY_INT ? l.t : int_type(nb, 0);
  unsigned long long m = nb >= 64 ? ~0ULL : ((1ULL << nb) - 1);
  char *x = v; if (qc(ft) == 'w' && c == 'l') { char *y = tmp(); emit("%s =l extuw %s", y, x); x = y; } else if (qc(ft) == 'l' && c == 'w') { char *y = tmp(); emit("%s =w copy %s", y, x); x = y; }
  char *a = tmp(); emit("%s =%c and %s, %llu", a, c, x, m);
  if (l.bitoff) { char *b = tmp(); emit("%s =%c shl %s, %d", b, c, a, l.bitoff); a = b; }
  char *o = load(h, l.op); char *k = tmp(); emit("%s =%c and %s, %llu", k, c, o, ~(m << l.bitoff) & (l.hbytes == 8 ? ~0ULL : ((1ULL << (l.hbytes * 8)) - 1)));
  char *r = tmp(); emit("%s =%c or %s, %s", r, c, k, a); store(h, r, l.op);
}
static Val rv(Val v) {
  if (!v.t) { Node *cn = gen_cur_pub(); die("%s:%d: internal: value without type", cn ? cn->tok->file : "?", cn ? cn->tok->line : 0); }
  if (v.ck || !v.lv) return v;
  if (v.bf) {
    if (bf_needs_wide(&v) && bits_of(v.t) > 64) return V(v.t, bf_load(v)); /* slot holding the field */
    char *x = bf_load(v);
    if (is_aggr(v.t)) { char *sl = slot(v.t); store(int_type(tsize(v.t) * 8, 0), x, sl); return V(v.t, sl); }
    return V(v.t, x);
  }
  if (is_aggr(v.t)) return V(v.t, v.op);
  return V(v.t, load(v.t, v.op));
}
static char *opnd(Val v) { return mat(rv(v)); }
static char *addr_of(Val v) {
  if (v.ck) {
    if (v.cv.k == CV_STR && !is_aggr(v.t)) return mat(v);
    if (is_aggr(v.t) && v.cv.k != CV_UNDEF && !(v.cv.k == CV_NULL && v.t->k == TY_OPT)) return cv_data(&v.cv, v.t);
    if (!is_aggr(v.t) && v.cv.k != CV_UNDEF) { char *sl = slot(v.t); store(v.t, mat(v), sl); return sl; }
    char *sl = slot(v.t);
    if (v.cv.k == CV_NULL && v.t->k == TY_OPT) store(t_u8, "0", addp(sl, tsize(v.t->elem)));
    return sl;
  }
  return v.op;
}
static void put(Val v, Type *t, char *addr) {
  if (v.ck && v.cv.k == CV_UNDEF) { if (!is_aggr(t) && tsize(t) > 0) store(t, "0", addr); return; }
  if (v.t->k == TY_NORET) return;
  if (is_aggr(t)) blit(addr_of(v), addr, tsize(t));
  else store(t, opnd(v), addr);
}
static void put_lv(Val v, Val l) {
  if (!l.bf) { put(v, l.t, l.op); return; }
  if (v.ck && v.cv.k == CV_UNDEF) return;
  if (v.t->k == TY_NORET) return;
  if (bf_needs_wide(&l) && bits_of(l.t) > 64) { bf_store(l, addr_of(v)); return; } /* wide field: pass its storage */
  if (is_aggr(l.t)) bf_store(l, load(int_type(tsize(l.t) * 8, 0), addr_of(v)));
  else bf_store(l, opnd(v));
}
static int is_ptrish(Type *t) { return t->k == TY_PTR || t->k == TY_MPTR || t->k == TY_FN || opt_is_ptr(t); }
static Val retype(Val v, Type *t) { v = rv(v); v.t = t; return v; }

static Val wconv(Val v, Type *to);
static int is_bigf(Type *t) { return t->k == TY_FLOAT && t->bits > 64; }
static Val bigf_conv(Val v, Type *f, Type *to) {
  char *o = opnd(v);
  if (f->k == TY_BOOL) { v = coerce(v, t_u8); f = t_u8; o = opnd(v); }
  if (is_bigf(f) && is_bigf(to)) { if (f->bits == to->bits) return V(to, o); char *sl = slot(to); emit("call $zb_fconv(w %d, l %s, w %d, l %s)", to->bits, sl, f->bits, o); return V(to, sl); }
  if (is_bigf(f) && to->k == TY_FLOAT) { char *r = tmp(); emit("%s =%c call $zb_fto%d(w %d, l %s)", r, qc(to), qc(to) == 's' ? 32 : 64, f->bits, o); return V(to, r); }
  if (f->k == TY_FLOAT && is_bigf(to)) { char *x = o; if (qc(f) == 's') { x = tmp(); emit("%s =d exts %s", x, o); } char *sl = slot(to); emit("call $zb_fext(w %d, l %s, d %s)", to->bits, sl, x); return V(to, sl); }
  if (is_bigf(f) && to->k == TY_INT) {
    if (is_wide(to)) { if (to->bits > 128) die("f%d -> %s unsupported", f->bits, tname(to)); char *sl = slot(to); emit("call $zb_toi128(w %d, l %s, l %s, w %d)", f->bits, sl, o, to->sign); return V(to, sl); }
    char *r = tmp(); emit("%s =l call $zb_toi(w %d, l %s, w %d)", r, f->bits, o, to->sign);
    if (qc(to) == 'w') { char *r2 = tmp(); emit("%s =w copy %s", r2, r); return V(to, norm(r2, to)); } return V(to, r); }
  if (f->k == TY_INT && is_bigf(to)) { char *sl = slot(to);
    if (is_wide(f)) { if (f->bits > 128) die("%s -> f%d unsupported", tname(f), to->bits); emit("call $zb_fromi128(w %d, l %s, l %s, w %d)", to->bits, sl, o, f->sign); return V(to, sl); }
    char *x = o; if (qc(f) == 'w') { x = tmp(); emit("%s =l ext%sw %s", x, f->sign ? "s" : "u", o); }
    emit("call $zb_fromi(w %d, l %s, l %s, w %d)", to->bits, sl, x, f->sign); return V(to, sl); }
  die("bad float conversion %s -> %s", tname(f), tname(to));
}
static char *bigf_op(int op, Type *t, char *a, char *b) { char *sl = slot(t); emit("call $zb_fop(w %d, w %d, l %s, l %s, l %s)", t->bits, op, sl, a, b ? b : "0"); return sl; }
static Val float_conv(Val v, Type *to) { /* float -> float, int -> float, float -> int at runtime */
  v = rv(v); Type *f = v.t;
  if (v.ck) { CVal c = v.cv; if (c.k == CV_INT && is_float(to)) c = cv_float((f128)c.i, to);
    if (c.k == CV_FLOAT && is_float(to)) return CK(cv_float(fround(c.f, to), to));
    if (c.k == CV_FLOAT && to->k == TY_INT) return CK(cv_int(wrap_int((i128)c.f, to), to));
    if (c.k == CV_INT && to->k == TY_INT) return CK(cv_int(wrap_int(c.i, to), to));
    if (f->k == TY_CINT) { v = coerce(v, t_i64); f = t_i64; } else if (f->k == TY_CFLOAT) { v = coerce(v, t_f64); f = t_f64; } }
  if (is_bigf(f) || is_bigf(to)) return bigf_conv(v, f, to);
  char *o = opnd(v), *r = tmp();
  if (f->k == TY_FLOAT && to->k == TY_FLOAT) {
    if (qc(f) == qc(to)) return V(to, o);
    emit("%s =%c %s %s", r, qc(to), qc(to) == 'd' ? "exts" : "truncd", o); return V(to, r);
  }
  if (f->k == TY_FLOAT && to->k == TY_INT) {
    if (is_wide(to)) { char *q = tmp(); int s4 = qc(f) == 's';
      emit("%s =:zbw call $%s(%c %s)", q, to->sign ? (s4 ? "__fixsfti" : "__fixdfti") : (s4 ? "__fixunssfti" : "__fixunsdfti"), qc(f), o);
      return w_from_parts(to, load(t_u64, q), load(t_u64, addp(q, 8))); }
    int u = !to->sign; char c = qc(to);
    if (to->bits < 32 || (u && to->bits == 32)) { char *t2 = tmp(); emit("%s =l %ctosi %s", t2, qc(f), o); if (c == 'w') { emit("%s =w copy %s", r, t2); return V(to, norm(r, to)); } return V(to, t2); }
    emit("%s =%c %cto%ci %s", r, c, qc(f), u ? 'u' : 's', o); return V(to, r);
  }
  if ((f->k == TY_INT || f->k == TY_BOOL) && to->k == TY_FLOAT) {
    if (is_wide(f)) { int s4 = qc(to) == 's';
      emit("%s =%c call $%s(l %s, l %s)", r, qc(to), f->sign ? (s4 ? "__floattisf" : "__floattidf") : (s4 ? "__floatuntisf" : "__floatuntidf"), wlo(v), whi(v)); return V(to, r); }
    if (f->k == TY_BOOL) f = t_u8;
    int u = !f->sign;
    if (qc(f) == 'w' && f->bits < 32) { emit("%s =%c %s %s", r, qc(to), "swtof", o); return V(to, r); }
    emit("%s =%c %c%ctof %s", r, qc(to), u ? 'u' : 's', qc(f), o); return V(to, r);
  }
  die("bad float conversion %s -> %s", tname(f), tname(to));
}
static Val coerce(Val v, Type *to) {
  if (!to || v.t == to) return v;
  if (v.ck && v.cv.k == CV_AGG && is_tuple_type(v.t) && (to->k == TY_STRUCT || to->k == TY_TUPLE || to->k == TY_ARRAY) && !is_packed(to)) {
    int any = 0; if (is_tuple_type(to)) { layout(to->ct); for (int i = 0; i < to->ct->fields.n; i++) if (((Field *)to->ct->fields.a[i])->t->k == TY_ANYTYPE) any = 1; }
    if (!any) { CVal c = ccoerce(v.cv, to); if (c.k == CV_AGG && c.t == to) { Val r = CK(c); r.t = to; return r; } }
  }
  if (is_tuple_type(to) && is_tuple_type(v.t) && v.t->k != TY_NORET) { /* partially typed tuple hint: anytype fields take the value's types */
    layout(to->ct); int any = 0; for (int i = 0; i < to->ct->fields.n; i++) if (((Field *)to->ct->fields.a[i])->t->k == TY_ANYTYPE) any = 1;
    if (any) { layout(v.t->ct); if (v.t->ct->fields.n != to->ct->fields.n) return v; Vec nm = {0}, ty = {0};
      for (int i = 0; i < to->ct->fields.n; i++) { Type *tt = ((Field *)to->ct->fields.a[i])->t; Type *ft = ((Field *)v.t->ct->fields.a[i])->t; vpush(&nm, fmt("%d", i)); vpush(&ty, tt->k == TY_ANYTYPE ? (ft->k == TY_CINT ? t_i64 : ft->k == TY_CFLOAT ? t_f64 : ft) : tt); }
      to = mk_anon_struct(&nm, &ty, 1); if (v.t == to) return v; }
  }
  if (!v.ck && v.t->k == TY_SLICE && to->k == TY_PTR && to->elem->k == TY_ARRAY && to->elem->elem == v.t->elem) return V(to, load(t_u64, addr_of(v)));
  if (!v.ck && v.t->k == TY_ARRAY && to->k == TY_ARRAY && (is_vec(v.t) || is_vec(to)) && v.t->len == to->len && v.t->elem == to->elem) { v = rv(v); v.t = to; return v; }
  Type *f = v.t;
  if (f->k == TY_NORET || to->k == TY_ANYTYPE) return v;
  if (v.ck) {
    CVal r = ccoerce(v.cv, to);
    if (ck_ok(&r, to)) { Val o = CK(r); o.t = to; if (r.k == CV_VOID) { o.ck = 0; o.op = "0"; } return o; }
  }
  if (v.ck) {
    CVal c = v.cv;
    switch (c.k) {
    case CV_UNDEF: { Val r = v; r.t = to; return r; }
    case CV_INT:
      if (to->k == TY_INT || to->k == TY_CINT) { c.t = to; c.i = wrap_int(c.i, to); return CK(c); }
      if (to->k == TY_ENUM && f->k == TY_ENUM) { c.t = to; return CK(c); }
      break;
    case CV_ENUMLIT:
      if (to->k == TY_ENUM) { int64_t x; if (!enum_val(to, c.s, &x)) die("no field .%s in %s", c.s, tname(to)); CVal r = {0}; r.k = CV_INT; r.i = x; r.t = to; return CK(r); }
      if (to->k == TY_UNION && to->ct->tagged) {
        int64_t x; enum_val(to, c.s, &x); char *sl = slot(to); char tv[32]; snprintf(tv, 32, "%lld", (long long)x);
        store(to->ct->tag, tv, addp(sl, union_tag_off(to))); return V(to, sl);
      }
      break;
    case CV_NULL:
      if (to->k == TY_OPT) { if (opt_is_ptr(to)) { Val r = v; r.t = to; return r; } Val r = v; r.t = to; return V(to, addr_of(r)); }
      break;
    case CV_ERR:
      if (to->k == TY_ERRSET) { Val r = v; r.t = to; return r; }
      if (to->k == TY_ERRU) { char *sl = slot(to); store(t_u16, mat(v), sl); return V(to, sl); }
      break;
    case CV_STR: {
      char *p = mat(v);
      if (to->k == TY_SLICE) { char *sl = slot(to); store(t_u64, p, sl); store(t_u64, fmt("%d", c.slen), addp(sl, 8)); return V(to, sl); }
      if (to->k == TY_MPTR || to->k == TY_PTR || to->k == TY_ARRAY) return V(to, p);
      if (to->k == TY_OPT) break;
      break;
    }
    case CV_FN: if (to->k == TY_FN || to->k == TY_PTR) return V(to, mat(v)); break;
    case CV_BOOL: if (to->k == TY_BOOL) return v; break;
    case CV_TYPE: if (to->k == TY_TYPE) return v; break;
    }
  }
  if (to->k == TY_OPT) {
    if (f->k == TY_OPT && opt_is_ptr(f) == opt_is_ptr(to)) { v.t = to; return v; }
    if (f->k == TY_NULL) { CVal c = {0}; c.k = CV_NULL; return coerce(CK(c), to); }
    Val pv = coerce(v, to->elem);
    if (opt_is_ptr(to)) return retype(pv, to);
    char *sl = slot(to); put(pv, to->elem, sl); store(t_u8, "1", addp(sl, tsize(to->elem))); return V(to, sl);
  }
  if (to->k == TY_ERRU) {
    if (f->k == TY_ERRU) { v.t = to; return v; }
    if (f->k == TY_ERRSET) { char *sl = slot(to); store(t_u16, opnd(v), sl); return V(to, sl); }
    Val pv = coerce(v, to->elem); char *sl = slot(to); store(t_u16, "0", sl);
    if (to->elem != t_void) put(pv, to->elem, addp(sl, erru_off(to)));
    return V(to, sl);
  }
  if (to->k == TY_INT && f->k == TY_INT && (is_wide(f) || is_wide(to))) return wconv(v, to);
  if (to->k == TY_INT && f->k == TY_INT) {
    char *o = opnd(v);
    if (qc(f) == 'w' && qc(to) == 'l') { char *r = tmp(); emit("%s =l %s %s", r, f->sign ? "extsw" : "extuw", o); return V(to, r); }
    if (qc(f) == 'l' && qc(to) == 'w') { char *r = tmp(); emit("%s =w copy %s", r, o); return V(to, norm(r, to)); }
    if (to->bits < f->bits) return V(to, norm(o, to));
    return V(to, o);
  }
  if (to->k == TY_INT && f->k == TY_BOOL) return retype(v, to);
  if (to->k == TY_FLOAT && f->k == TY_FLOAT) return float_conv(v, to);
  if (to->k == TY_SLICE && f->k == TY_PTR && f->elem->k == TY_ARRAY) {
    char *p = opnd(v), *sl = slot(to); store(t_u64, p, sl); store(t_u64, fmt("%lld", (long long)f->elem->len), addp(sl, 8)); return V(to, sl);
  }
  if (to->k == TY_SLICE && f->k == TY_SLICE) { v.t = to; return v; }
  if (to->k == TY_MPTR && f->k == TY_SLICE) return V(to, load(t_u64, addr_of(v)));
  if (is_ptrish(to) && is_ptrish(f)) return retype(v, to);
  if (to->k == TY_ERRSET && f->k == TY_ERRSET) return retype(v, to);
  if (to->k == TY_ENUM && f->k == TY_UNION && f->ct->tagged) return V(to, load(to, addp(addr_of(v), union_tag_off(f))));
  if (to->k == TY_UNION && f->k == TY_ENUM) { char *sl = slot(to); store(to->ct->tag, opnd(v), addp(sl, union_tag_off(to))); return V(to, sl); }
  if (to->k == TY_ARRAY && f->k == TY_ARRAY && to->len == f->len) { v.t = to; return v; }
  if (to->k == TY_ARRAY && f->k == TY_PTR && f->elem->k == TY_ARRAY) return V(to, opnd(v));
  if (to->k == TY_ENUM && f->k == TY_ENUM) return retype(v, to);
  if (f->k == TY_UNDEF) { v.t = to; return v; }
  if ((f->k == TY_STRUCT || f->k == TY_TUPLE) && (to->k == TY_STRUCT || to->k == TY_TUPLE || to->k == TY_ARRAY) && (is_anon(f) || is_tuple_type(f))) {
    /* anonymous struct / tuple -> struct, tuple or array, field by field */
    layout(f->ct); if (to->ct) layout(to->ct); char *src = addr_of(v), *sl = slot(to); int tup = is_tuple_type(f);
    char *set = xalloc((to->k == TY_ARRAY ? to->len : to->ct->fields.n) + 1);
    for (int i = 0; i < f->ct->fields.n; i++) {
      Field *ff = f->ct->fields.a[i]; Type *tt; int off;
      if (to->k == TY_ARRAY) { tt = to->elem; off = i * tsize(tt); set[i] = 1; }
      else { Field *tf = tup && is_tuple_type(to) ? (i < to->ct->fields.n ? to->ct->fields.a[i] : NULL) : find_field(to->ct, ff->name); if (!tf) continue; tt = tf->t; off = tf->off;
        for (int j = 0; j < to->ct->fields.n; j++) if (to->ct->fields.a[j] == tf) set[j] = 1; }
      Val e = coerce(ff->is_ct ? CK(*(CVal *)ff->defcv) : rv(LV(ff->t, addp(src, ff->off))), tt); put(e, tt, addp(sl, off));
    }
    if (to->k != TY_ARRAY) for (int j = 0; j < to->ct->fields.n; j++) { Field *tf = to->ct->fields.a[j]; if (!set[j] && (tf->def || tf->defcv)) { CVal dv; if (tf->defcv) dv = *(CVal *)tf->defcv; else if (!ceval_ex(tf->def, to->ct->scope, tf->t, &dv)) continue; put(coerce(CK(dv), tf->t), tf->t, addp(sl, tf->off)); } }
    return V(to, sl);
  }
  if ((to->k == TY_SLICE || (to->k == TY_PTR && to->elem->k == TY_ARRAY)) && f->k == TY_PTR && is_tuple_type(f->elem)) { /* &tuple -> slice / *[n]T */
    layout(f->elem->ct); int64_t nn = f->elem->ct->fields.n; Type *at = to->k == TY_SLICE ? array_of(to->elem, nn, 0, 0) : to->elem;
    Val av = coerce(rv(LV(f->elem, opnd(v))), at); char *p = addr_of(av);
    if (to->k == TY_PTR) return V(to, p);
    char *sl = slot(to); store(t_u64, p, sl); store(t_u64, fmt("%lld", (long long)nn), addp(sl, 8)); return V(to, sl);
  }
  if (f->k == TY_ARRAY && is_tuple_type(to)) { /* array -> tuple, element-wise */
    layout(to->ct); char *src = addr_of(v), *sl = slot(to);
    for (int i = 0; i < to->ct->fields.n && i < f->len; i++) { Field *tf = to->ct->fields.a[i]; Val e = coerce(rv(LV(f->elem, addp(src, (int64_t)i * tsize(f->elem)))), tf->t); put(e, tf->t, addp(sl, tf->off)); }
    return V(to, sl);
  }
  if (to->k == TY_SLICE && f->k == TY_ARRAY && to->isconst) { /* array rvalue -> const slice of a temporary */
    char *p = addr_of(v), *sl = slot(to); store(t_u64, p, sl); store(t_u64, fmt("%lld", (long long)f->len), addp(sl, 8)); return V(to, sl);
  }
  { extern Node *gen_cur_pub(void); Node *cn = gen_cur_pub(); die("%s:%d: cannot coerce %s to %s", cn ? cn->tok->file : "?", cn ? cn->tok->line : 0, tname(f), tname(to)); }
}

/* ---------- optionals / error unions ---------- */
static char *opt_has(Val v) {
  char *r = tmp();
  if (opt_is_ptr(v.t)) { emit("%s =w cnel %s, 0", r, opnd(v)); return r; }
  return load(t_u8, addp(addr_of(v), tsize(v.t->elem)));
}
static Val opt_payload(Val v, char *ptrval) {
  if (opt_is_ptr(v.t)) return V(v.t->elem, ptrval ? ptrval : opnd(v));
  return LV(v.t->elem, addr_of(v));
}
static void bind_local(Scope *s, char *name, Type *t, char *addr) {
  Sym *y = xalloc(sizeof *y); y->name = name; y->k = S_LOCAL; y->t = t; y->addr = addr; vpush(&s->syms, y);
}
static void bind_val(Scope *s, char *name, Val v) {
  if (!name || !strcmp(name, "_")) return;
  if (v.ck) { if (type_is_ctonly(v.t) || v.cv.k == CV_FN) { CVal c = v.cv; bind_cval(s, name, c); return; } }
  if (is_aggr(v.t)) { bind_local(s, name, v.t, addr_of(v)); return; }
  char *sl = slot(v.t); store(v.t, opnd(v), sl); bind_local(s, name, v.t, sl);
}

/* ---------- result slots ---------- */
static Type *peer_t(Type *a, Type *b);
static int discarding;
static void res_put(Res *r, Val v) {
  if (v.t->k == TY_NORET || term) return;
  if (r->collect) { Type *p = peer_t(r->t, v.t); r->t = p ? p : r->t; r->has = 1; return; }
  if (!r->t) {
    r->t = r->ex ? r->ex : v.t;
    if (r->ex && is_tuple_type(r->ex)) { layout(r->ex->ct); for (int i = 0; i < r->ex->ct->fields.n; i++) if (((Field *)r->ex->ct->fields.a[i])->t->k == TY_ANYTYPE) { r->t = coerce(v, r->ex).t; break; } }
    if (r->t->k == TY_CINT) r->t = t_i64;
    if (r->t->k == TY_ENUMLIT || r->t->k == TY_NULL) die("cannot infer type of branch result");
    if (r->t->k != TY_VOID && r->t->k != TY_TYPE && tsize(r->t) > 0) r->slot = slot(r->t);
  }
  r->has = 1;
  if (r->t->k == TY_VOID) return;
  if (v.t->k == TY_VOID && discarding) return; /* mixed void/value peers (only valid when the result is discarded) */
  v = coerce(v, r->t);
  if (r->slot) put(v, r->t, r->slot);
}
static Val res_get(Res *r) {
  if (!r->has) { if (!term) emit("hlt"); term = 1; return NORET(); }
  if (!r->slot) return V(r->t ? r->t : t_void, "0");
  return rv(LV(r->t, r->slot));
}

/* ---------- defers ---------- */
static void run_defers(int base, char *errop) {
  for (int i = defers.n - 1; i >= base; i--) {
    Defer *d = defers.a[i];
    if (d->err && !errop) continue;
    if (term) return;
    if (d->err && d->n->k == N_BUILTIN && !strcmp(d->n->s, "compileError")) continue; /* guard against error paths that zb cannot prove impossible */
    Scope *s = d->s;
    if (d->err && d->cap) { s = new_scope(s, NULL); bind_val(s, d->cap, V(t_errset, errop)); }
    int save = defers.n; gen(d->n, s, NULL); defers.n = save;
  }
}
static int have_errdefer(int base) { for (int i = base; i < defers.n; i++) if (((Defer *)defers.a[i])->err) return 1; return 0; }

/* ---------- runtime support emitted once ---------- */
static Vec tagfns; /* Type* enums with tagName helper */
static char *tagname_fn(Type *et) {
  for (int i = 0; i < tagfns.n; i++) if (tagfns.a[i] == et) return et->ct->tagnames_sym;
  vpush(&tagfns, et); Container *c = et->ct; layout(c);
  char *sym = fmt("zb.tagName.%d", tagfns.n); c->tagnames_sym = sym;
  fprintf(xb, "function l $%s(w %%v) {\n@start\n", sym);
  for (int i = 0; i < c->fields.n; i++) {
    Field *f = c->fields.a[i]; char *s = strdata(f->name, strlen(f->name));
    fprintf(db, "data $%s.%d = { l %s, l %d }\n", sym, i, s, (int)strlen(f->name));
    fprintf(xb, "\t%%c%d =w ceqw %%v, %lld\n\tjnz %%c%d, @y%d, @n%d\n@y%d\n\tret $%s.%d\n@n%d\n", i, (long long)f->val, i, i, i, i, sym, i, i);
  }
  fprintf(xb, "\thlt\n}\n");
  return sym;
}



/* ---------- wide integers (65..128 bits): 16-byte memory values {lo, hi} ---------- */
static int is_wide(Type *t) { return t && t->k == TY_INT && t->bits > 64; }
static void wnorm(Type *t, char *sl) { /* canonicalize the high word for widths < 128 */
  if (t->bits >= 128) return; int hb = t->bits - 64; char *h = load(t_u64, addp(sl, 8)), *r = tmp();
  if (t->sign) { char *q = tmp(); emit("%s =l shl %s, %d", q, h, 64 - hb); emit("%s =l sar %s, %d", r, q, 64 - hb); }
  else emit("%s =l and %s, %llu", r, h, (unsigned long long)((1ULL << hb) - 1));
  store(t_u64, r, addp(sl, 8));
}
static Val w_from_parts(Type *t, char *lo, char *hi) { char *sl = slot(t); store(t_u64, lo, sl); store(t_u64, hi, addp(sl, 8)); wnorm(t, sl); return V(t, sl); }
static char *wlo(Val v) { return load(t_u64, addr_of(v)); }
static char *whi(Val v) { return load(t_u64, addp(addr_of(v), 8)); }
static Val wconv(Val v, Type *to) { /* any int <-> any int where one side is wide */
  Type *f = v.t; if (f->k == TY_BOOL) f = t_u1; if (f->k == TY_ENUM) f = f->ct->tag;
  if (is_wide(f) && is_wide(to)) { char *a = addr_of(v); return w_from_parts(to, load(t_u64, a), load(t_u64, addp(a, 8))); }
  if (is_wide(f)) { char *lo = wlo(v); if (qc(to) == 'w') { char *r = tmp(); emit("%s =w copy %s", r, lo); return V(to, norm(r, to)); } return V(to, norm(lo, to)); }
  char *o = opnd(v), *lo = o;
  if (qc(f) == 'w') { lo = tmp(); emit("%s =l %s %s", lo, f->sign ? "extsw" : "extuw", o); }
  char *hi = "0"; if (f->sign) { hi = tmp(); emit("%s =l sar %s, 63", hi, lo); }
  return w_from_parts(to, lo, hi);
}
static Val wcall(const char *fn, Type *t, Val a, Val b, int bshift) {
  char *r = tmp();
  if (bshift) { Val bb = coerce(rv(b), t_u32); emit("%s =:zbw call $%s(l %s, l %s, w %s)", r, fn, wlo(a), whi(a), opnd(bb)); }
  else emit("%s =:zbw call $%s(l %s, l %s, l %s, l %s)", r, fn, wlo(a), whi(a), wlo(b), whi(b));
  return w_from_parts(t, load(t_u64, r), load(t_u64, addp(r, 8)));
}
static Val w_arith(const char *op, Type *t, Val a, Val b) {
  int sg = t->sign;
  if (op[0] == '<' || op[0] == '>') { if (b.ck) b = coerce(b, t_u32); return wcall(op[0] == '<' ? "__ashlti3" : sg ? "__ashrti3" : "__lshrti3", t, a, b, 1); }
  a = coerce(a, t); b = coerce(b, t);
  char *al = wlo(a), *ah = whi(a), *bl = wlo(b), *bh = whi(b), *lo = tmp(), *hi = tmp();
  if (op[0] == '+') { char *c = tmp(), *cl = tmp(), *h1 = tmp(); emit("%s =l add %s, %s", lo, al, bl); emit("%s =w cultl %s, %s", c, lo, al); emit("%s =l extuw %s", cl, c); emit("%s =l add %s, %s", h1, ah, bh); emit("%s =l add %s, %s", hi, h1, cl); }
  else if (op[0] == '-') { char *c = tmp(), *cl = tmp(), *h1 = tmp(); emit("%s =l sub %s, %s", lo, al, bl); emit("%s =w cultl %s, %s", c, al, bl); emit("%s =l extuw %s", cl, c); emit("%s =l sub %s, %s", h1, ah, bh); emit("%s =l sub %s, %s", hi, h1, cl); }
  else if (op[0] == '&' || op[0] == '|' || op[0] == '^') { const char *ins = op[0] == '&' ? "and" : op[0] == '|' ? "or" : "xor"; emit("%s =l %s %s, %s", lo, ins, al, bl); emit("%s =l %s %s, %s", hi, ins, ah, bh); }
  else if (op[0] == '*') return wcall("__multi3", t, a, b, 0);
  else if (op[0] == '/') return wcall(sg ? "__divti3" : "__udivti3", t, a, b, 0);
  else if (op[0] == '%') return wcall(sg ? "__modti3" : "__umodti3", t, a, b, 0);
  else die("unsupported operator %s on %s", op, tname(t));
  return w_from_parts(t, lo, hi);
}
static Val w_cmp(const char *op, Type *t, Val a, Val b) {
  a = coerce(a, t); b = coerce(b, t);
  char *al = wlo(a), *ah = whi(a), *bl = wlo(b), *bh = whi(b), *r = tmp();
  int eq = !strcmp(op, "=="), ne = !strcmp(op, "!=");
  if (eq || ne) { char *x = tmp(), *y = tmp(), *z = tmp(); emit("%s =l xor %s, %s", x, al, bl); emit("%s =l xor %s, %s", y, ah, bh); emit("%s =l or %s, %s", z, x, y); emit("%s =w %s %s, 0", r, eq ? "ceql" : "cnel", z); return V(t_bool, r); }
  int sg = t->sign; const char *hs, *ls; /* strict compare on hi, then lo (unsigned) */
  if (op[0] == '<') { hs = sg ? "csltl" : "cultl"; ls = op[1] == '=' ? "culel" : "cultl"; } else { hs = sg ? "csgtl" : "cugtl"; ls = op[1] == '=' ? "cugel" : "cugtl"; }
  char *h1 = tmp(), *he = tmp(), *l1 = tmp(), *t2 = tmp(); emit("%s =w %s %s, %s", h1, hs, ah, bh); emit("%s =w ceql %s, %s", he, ah, bh); emit("%s =w %s %s, %s", l1, ls, al, bl);
  emit("%s =w and %s, %s", t2, he, l1); emit("%s =w or %s, %s", r, h1, t2); return V(t_bool, r);
}

/* ---------- vectors (stored like arrays; ops are unrolled per element) ---------- */
static Val gen_arith(const char *op, Val a, Val b);
static Val gen_cmp(const char *op, Val a, Val b);
static Val vel(Val v, int64_t i) { Type *et = v.t->elem; return rv(LV(et, addp(addr_of(v), i * tsize(et)))); }
static Val vec_bin(const char *op, Val a, Val b, int cmp) {
  Type *vt = is_vec(a.t) ? a.t : b.t;
  if (!is_vec(a.t)) a = coerce(a, vt); if (!is_vec(b.t)) b = coerce(b, vt);
  Type *rt = cmp ? vec_of(t_bool, vt->len) : vt; char *sl = slot(rt);
  char *pa = addr_of(a), *pb = addr_of(b); a = V(a.t, pa); b = V(b.t, pb);
  for (int64_t i = 0; i < vt->len; i++) {
    Val r = cmp ? gen_cmp(op, vel(a, i), vel(b, i)) : gen_arith(op, vel(a, i), vel(b, i));
    r = coerce(r, rt->elem); put(r, rt->elem, addp(sl, i * tsize(rt->elem)));
  }
  return V(rt, sl);
}
static Val vec_splat(Val x, Type *vt) {
  char *sl = slot(vt); x = coerce(rv(x), vt->elem); char *o = is_aggr(vt->elem) ? NULL : opnd(x);
  for (int64_t i = 0; i < vt->len; i++) { if (o) store(vt->elem, o, addp(sl, i * tsize(vt->elem))); else put(x, vt->elem, addp(sl, i * tsize(vt->elem))); }
  return V(vt, sl);
}
static Val sel2(Val c, Val a, Val b, Type *t) { /* c ? a : b */
  char *sl = slot(t), *l1 = newl(), *l2 = newl(), *le = newl(); br(opnd(c), l1, l2);
  label(l1); put(coerce(a, t), t, sl); jmp(le); label(l2); put(coerce(b, t), t, sl); jmp(le); label(le);
  return rv(LV(t, sl));
}
static Val vec_reduce(const char *on, Val v) {
  Type *et = v.t->elem; v = V(v.t, addr_of(v)); Val acc = vel(v, 0);
  for (int64_t i = 1; i < v.t->len; i++) {
    Val e = vel(v, i);
    if (!strcmp(on, "Min") || !strcmp(on, "Max")) { Val c = gen_cmp(on[1] == 'i' ? "<" : ">", e, acc); acc = sel2(c, e, acc, et); continue; }
    const char *bop = !strcmp(on, "And") ? "&" : !strcmp(on, "Or") ? "|" : !strcmp(on, "Xor") ? "^" : !strcmp(on, "Add") ? (et->k == TY_INT ? "+%" : "+") : "*%";
    if (et->k == TY_BOOL) { char *r = tmp(); emit("%s =w %s %s, %s", r, bop[0] == '&' ? "and" : bop[0] == '|' ? "or" : "xor", opnd(acc), opnd(e)); acc = V(t_bool, r); }
    else acc = coerce(gen_arith(bop, acc, e), et);
  }
  return acc;
}
static Val vec_un(const char *op, Val v) {
  Type *vt = v.t; char *sl = slot(vt); v = V(vt, addr_of(v));
  for (int64_t i = 0; i < vt->len; i++) {
    Val e = vel(v, i); char *r = tmp(); Type *et = vt->elem;
    if (op[0] == '!') emit("%s =w ceqw %s, 0", r, opnd(e));
    else if (op[0] == '~') { emit("%s =%c xor %s, -1", r, qc(et), opnd(e)); r = norm(r, et); }
    else { emit("%s =%c neg %s", r, qc(et), opnd(e)); r = norm(r, et); }
    store(et, r, addp(sl, i * tsize(et)));
  }
  return V(vt, sl);
}

/* ---------- expressions ---------- */
static Val gen_member(Val base, const char *name, Node *n) {
  if (base.ck) {
    CVal m;
    if (ceval_member(base.cv, name, &m)) return CK(m);
    if (base.cv.k == CV_TYPE && base.cv.t->ct) { Decl *d = find_decl(base.cv.t->ct, name); if (d) { resolve_decl(d); if (d->kind == D_VAR) return LV(d->t, fmt("$%s", d->sym)); } }
    if (base.cv.k == CV_PTR && base.t && (base.t->k == TY_PTR || base.t->k == TY_MPTR)) {
      if (!strcmp(name, "len") && base.t->k == TY_PTR && base.t->elem->k == TY_ARRAY) { CVal l = {0}; l.k = CV_INT; l.t = t_usize; l.i = base.t->elem->len; return CK(l); }
      base = V(base.t, mat(base));
    } else if ((base.cv.k == CV_SLICE || (base.cv.k == CV_PTR && base.cv.t && base.cv.t->k == TY_PTR && base.cv.t->elem->k == TY_ARRAY)) && base.t && base.t->k == TY_SLICE && (!strcmp(name, "len") || !strcmp(name, "ptr"))) {
      if (name[0] == 'l') { CVal l = {0}; l.k = CV_INT; l.t = t_usize; l.i = base.cv.k == CV_SLICE ? base.cv.slen : base.cv.t->elem->len; return CK(l); }
      return V(mptr_to(base.t->elem, base.t->isconst, base.t->hassent, base.t->sent), mat(base));
    } else if (base.cv.k != CV_STR) die("%s:%d: no member '%s' (ck kind %d, %s)", n->tok->file, n->tok->line, name, base.cv.k, tname(base.t));
  }
  Type *t = base.t;
  if (t->k == TY_PTR && t->elem->k != TY_OPAQUE) { base = LV(t->elem, opnd(base)); t = t->elem; }
  switch (t->k) {
  case TY_STRUCT: case TY_UNION: case TY_TUPLE: {
    Field *f = find_field(t->ct, name);
    if (!f) {
      Decl *d = find_decl(t->ct, name);
      if (d) { resolve_decl(d); if (d->kind == D_VAR) return LV(d->t, fmt("$%s", d->sym)); return CK(d->cv); }
      if (!strcmp(name, "len") && is_tuple_type(t)) { CVal l = {0}; l.k = CV_INT; l.t = t_cint; l.i = t->ct->fields.n; return CK(l); }
      die("%s:%d: no field '%s' in %s", n->tok->file, n->tok->line, name, tname(t));
    }
    if (f->is_ct) { Val r = CK(*(CVal *)f->defcv); r.t = f->t; return r; }
    if (t->k == TY_STRUCT && is_packed(t)) {
      Val r = LV(f->t, NULL);
      if (base.lv && base.bf) { r.op = base.op; r.hbytes = base.hbytes; r.bitoff = base.bitoff + f->bitoff; }
      else { r.op = addr_of(base); r.hbytes = tsize(t); r.bitoff = f->bitoff; }
      r.bf = 1; if (!base.lv) { Val x = r; x.lv = 1; return rv(x); }
      return r;
    }
    if (t->k == TY_UNION && base.lv && base.bf) { Val r = base; r.t = f->t; return r; } /* packed union inside a packed struct */
    return LV(f->t, addp(addr_of(base), f->off));
  }
  case TY_SLICE:
    if (!strcmp(name, "len")) return LV(t_usize, addp(addr_of(base), 8));
    if (!strcmp(name, "ptr")) return LV(mptr_to(t->elem, t->isconst, 0, 0), addr_of(base));
    break;
  case TY_ARRAY:
    if (!strcmp(name, "len")) { CVal c = {0}; c.k = CV_INT; c.i = t->len; c.t = t_cint; return CK(c); }
    break;
  case TY_ENUM: case TY_ERRU: case TY_OPT: break;
  default: break;
  }
  die("%s:%d: no member '%s' on %s", n->tok->file, n->tok->line, name, tname(t));
}
static Val gen_index(Val b, Val i) {
  Type *t = b.t, *et; char *base;
  { Type *tt = t->k == TY_PTR ? t->elem : t;
    if ((tt->k == TY_TUPLE || (tt->k == TY_STRUCT && tt->ct && tt->ct->is_tuple)) && i.ck) { char nb[32]; snprintf(nb, sizeof nb, "%lld", (long long)i.cv.i); return gen_member(b, nb, NULL); } }
  if (b.ck && b.cv.k == CV_STR) { base = mat(b); et = t_u8; }
  else if (t->k == TY_PTR && t->elem->k == TY_ARRAY) { base = opnd(b); et = t->elem->elem; }
  else if (t->k == TY_ARRAY) { base = addr_of(b); et = t->elem; }
  else if (t->k == TY_SLICE) { base = load(t_u64, addr_of(b)); et = t->elem; }
  else if (t->k == TY_MPTR) { base = opnd(b); et = t->elem; }
  else { Node *cn = gen_cur_pub(); die("%s:%d: cannot index %s", cn ? cn->tok->file : "?", cn ? cn->tok->line : 0, tname(t)); }
  i = coerce(i, t_usize);
  if (i.ck) return LV(et, addp(base, i.cv.i * tsize(et)));
  char *o = tmp(), *a = tmp(); emit("%s =l mul %s, %d", o, opnd(i), tsize(et)); emit("%s =l add %s, %s", a, base, o);
  return LV(et, a);
}
static Val gen_slice(Node *n, Scope *s) {
  Val b = gen(n->a, s, NULL); Type *t = b.t, *et; char *base, *len = NULL; int c = 0;
  if (b.ck && b.cv.k == CV_STR) { base = mat(b); et = t_u8; len = fmt("%d", b.cv.slen); c = 1; }
  else if (t->k == TY_PTR && t->elem->k == TY_ARRAY) { base = opnd(b); et = t->elem->elem; len = fmt("%lld", (long long)t->elem->len); c = t->isconst; }
  else if (t->k == TY_ARRAY) { base = addr_of(b); et = t->elem; len = fmt("%lld", (long long)t->len); }
  else if (t->k == TY_SLICE) { char *a = addr_of(b); base = load(t_u64, a); len = load(t_u64, addp(a, 8)); et = t->elem; c = t->isconst; }
  else if (t->k == TY_MPTR) { base = opnd(b); et = t->elem; c = t->isconst; }
  else if (t->k == TY_PTR) { base = opnd(b); et = t->elem; c = t->isconst; len = "1"; }
  else die("%s:%d: cannot slice %s", n->tok->file, n->tok->line, tname(t));
  int64_t clen = (t->k == TY_PTR && t->elem->k == TY_ARRAY) ? t->elem->len : t->k == TY_ARRAY ? t->len : (t->k == TY_PTR) ? 1 : -1;
  if (b.ck && b.cv.k == CV_STR) clen = b.cv.slen;
  Val lov = coerce(gen(n->b, s, t_usize), t_usize), hiv; int hck = 0; int64_t hcv = clen;
  if (n->c) { hiv = coerce(gen(n->c, s, t_usize), t_usize); if (hiv.ck) { hck = 1; hcv = (int64_t)hiv.cv.i; } } else hck = clen >= 0;
  char *lo = opnd(lov);
  char *hi = n->c ? opnd(hiv) : len;
  if (!hi && t->k == TY_MPTR) { /* mptr[lo..] is a many-pointer */
    char *o = tmp(), *r = tmp(); emit("%s =l mul %s, %d", o, lo, tsize(et)); emit("%s =l add %s, %s", r, base, o);
    return V(mptr_to(et, c, 0, 0), r);
  }
  if (!hi) die("slice of many-pointer needs an end");
  if (lov.ck && hck && !(b.ck && b.cv.k == CV_STR)) { /* comptime-known bounds: pointer to array */
    int hs2 = 0; int64_t sv2 = 0;
    if (n->d) { CVal sc; if (ceval_ex(n->d, s, et, &sc)) { hs2 = 1; sv2 = (int64_t)sc.i; } }
    else if (!n->c && t->k == TY_PTR && t->elem->k == TY_ARRAY && t->elem->hassent) { hs2 = 1; sv2 = t->elem->sent; }
    Type *pt = ptr_to(array_of(et, hcv - (int64_t)lov.cv.i, hs2, sv2), c);
    return V(pt, addp(base, (int64_t)lov.cv.i * tsize(et)));
  }
  int hs = 0; int64_t sv = 0;
  if (n->d) { CVal sc; if (!ceval_ex(n->d, s, et, &sc) && !ceval_rt(n->d, s, et, &sc)) die("%s:%d: slice sentinel must be comptime (at %s)", n->tok->file, n->tok->line, ct_fail_loc()); hs = 1; sv = (int64_t)sc.i; }
  else if (!n->c && t->k == TY_SLICE && t->hassent) { hs = 1; sv = t->sent; }
  else if (!n->c && t->k == TY_PTR && t->elem->k == TY_ARRAY && t->elem->hassent) { hs = 1; sv = t->elem->sent; }
  Type *st = slice_of_s(et, c, hs, sv); char *sl = slot(st);
  char *off = tmp(), *p = tmp(), *l = tmp();
  emit("%s =l mul %s, %d", off, lo, tsize(et)); emit("%s =l add %s, %s", p, base, off); emit("%s =l sub %s, %s", l, hi, lo);
  store(t_u64, p, sl); store(t_u64, l, addp(sl, 8));
  return V(st, sl);
}
static Type *peer(Val a, Val b) {
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
static Val fold_bin(const char *op, Val a, Val b) {
  CVal r; if (!cv_binop(op, a.cv, b.cv, &r)) die("cannot fold comptime operation %s", op);
  return CK(r);
}

/* saturating integer arithmetic (+| -| *| <<|) for ints up to 64 bits */
static char *sat_l(Val v, Type *t) { char *x = opnd(v); if (qc(t) == 'w') { char *r = tmp(); emit("%s =l %s %s", r, t->sign ? "extsw" : "extuw", x); return r; } return x; }
static char *sat_sel(char *cw, char *th, char *el) { /* cw ? th : el (all l except cw) */
  char *c = tmp(), *m = tmp(), *d = tmp(), *e = tmp(), *r = tmp();
  emit("%s =l extuw %s", c, cw); emit("%s =l sub 0, %s", m, c); emit("%s =l xor %s, %s", d, th, el); emit("%s =l and %s, %s", e, d, m); emit("%s =l xor %s, %s", r, el, e); return r;
}
static Val sat_arith(const char *op, Type *t, Val a, Val b) {
  int bits = t->bits, sg = t->sign;
  char *mx = fmt("%lld", sg ? (long long)((1ULL << (bits - 1)) - 1) : bits == 64 ? -1LL : (long long)((1ULL << bits) - 1));
  char *mn = fmt("%lld", sg ? (long long)(-(1ULL << (bits - 1))) : 0LL);
  char *X = sat_l(a, t), *r = tmp(), *c1 = tmp(), *c2 = tmp();
  if (op[0] == '<') { /* <<| */
    char *Y = opnd(coerce(b, t_u64)); if (qc(b.t) == 'w' && !b.ck) { char *e = tmp(); emit("%s =l extuw %s", e, Y); Y = e; }
    char *sh = tmp(), *bk = tmp(); emit("%s =l shl %s, %s", sh, X, Y);
    char *tr = sh; if (bits < 64) { tr = tmp(); emit("%s =l shl %s, %d", tr, sh, 64 - bits); char *t2 = tmp(); emit("%s =l %s %s, %d", t2, sg ? "sar" : "shr", tr, 64 - bits); tr = t2; }
    emit("%s =l %s %s, %s", bk, sg ? "sar" : "shr", tr, Y); emit("%s =w cnel %s, %s", c1, bk, X);
    char *big = tmp(); emit("%s =w cugel %s, %d", big, Y, bits); char *nz = tmp(); emit("%s =w cnel %s, 0", nz, X); char *bz = tmp(); emit("%s =w and %s, %s", bz, big, nz);
    char *ov = tmp(); emit("%s =w or %s, %s", ov, c1, bz);
    char *satv = mx; if (sg) { char *ng = tmp(); emit("%s =w csltl %s, 0", ng, X); satv = sat_sel(ng, mn, mx); }
    r = sat_sel(ov, satv, tr);
  } else {
    b = coerce(b, t); char *Y = sat_l(b, t);
    const char *ins = op[0] == '+' ? "add" : op[0] == '-' ? "sub" : "mul";
    emit("%s =l %s %s, %s", r, ins, X, Y);
    if (op[0] == '*' && bits > 32) { /* overflow of the 64-bit product */
      char *nz = tmp(), *dv = tmp(), *q = tmp(), *ov = tmp(), *nzl = tmp(), *inv = tmp();
      emit("%s =w cnel %s, 0", nz, X); emit("%s =l extuw %s", nzl, nz); emit("%s =l xor %s, 1", inv, nzl); emit("%s =l add %s, %s", dv, X, inv);
      emit("%s =l %s %s, %s", q, sg ? "div" : "udiv", r, dv); char *ne = tmp(); emit("%s =w cnel %s, %s", ne, q, Y); emit("%s =w and %s, %s", ov, ne, nz);
      char *satv = mx; if (sg) { char *xy = tmp(), *ng = tmp(); emit("%s =l xor %s, %s", xy, X, Y); emit("%s =w csltl %s, 0", ng, xy); satv = sat_sel(ng, mn, mx); }
      r = sat_sel(ov, satv, r);
      if (bits == 64) goto done;
    }
    if (bits == 64 && op[0] != '*') {
      char *ov = tmp();
      if (!sg) { if (op[0] == '+') { emit("%s =w cultl %s, %s", ov, r, X); r = sat_sel(ov, mx, r); } else { emit("%s =w cultl %s, %s", ov, X, Y); r = sat_sel(ov, "0", r); } }
      else {
        char *p1 = tmp(), *p2 = tmp(), *p3 = tmp(), *ng = tmp();
        if (op[0] == '+') { emit("%s =l xor %s, %s", p1, X, r); emit("%s =l xor %s, %s", p2, Y, r); }
        else { emit("%s =l xor %s, %s", p1, X, Y); emit("%s =l xor %s, %s", p2, X, r); }
        emit("%s =l and %s, %s", p3, p1, p2); emit("%s =w csltl %s, 0", ov, p3); emit("%s =w csltl %s, 0", ng, X);
        r = sat_sel(ov, sat_sel(ng, mn, mx), r);
      }
      goto done;
    }
    if (!sg) {
      if (op[0] == '-') { emit("%s =w csltl %s, 0", c1, r); r = sat_sel(c1, "0", r); }
      else { emit("%s =w cugtl %s, %s", c1, r, mx); r = sat_sel(c1, mx, r); }
    } else {
      emit("%s =w csgtl %s, %s", c1, r, mx); r = sat_sel(c1, mx, r);
      emit("%s =w csltl %s, %s", c2, r, mn); r = sat_sel(c2, mn, r);
    }
  }
done:
  if (qc(t) == 'w') { char *w = tmp(); emit("%s =w copy %s", w, r); r = w; }
  return V(t, r);
}
static Val gen_cmp(const char *op, Val a, Val b) {
  if ((is_vec(a.t) || is_vec(b.t)) && !(a.ck && b.ck)) return vec_bin(op, rv(a), rv(b), 1);
  if (!a.ck && b.ck && b.cv.k == CV_INT && b.cv.i == 0 && !b.cv.big && a.t->k == TY_INT && !a.t->sign) { /* unsigned vs 0: comptime-known (as in Sema) */
    if (!strcmp(op, ">=")) return CK(cv_bool(1)); if (!strcmp(op, "<")) return CK(cv_bool(0)); }
  if (a.ck && !b.ck && a.cv.k == CV_INT && a.cv.i == 0 && !a.cv.big && b.t->k == TY_INT && !b.t->sign) {
    if (!strcmp(op, "<=")) return CK(cv_bool(1)); if (!strcmp(op, ">")) return CK(cv_bool(0)); }
  { /* runtime int vs comptime int outside its range: comptime-known result (as in Sema) */
    for (int sw = 0; sw < 2; sw++) {
      Val r = sw ? a : b, c = sw ? b : a; /* r: runtime side, c: constant side */
      if (r.ck || !c.ck || c.cv.k != CV_INT || c.cv.big || r.t->k != TY_INT || r.t->bits > 127) continue;
      int bits = r.t->bits; i128 lo = r.t->sign ? -((i128)1 << (bits - 1)) : 0, hi = r.t->sign ? ((i128)1 << (bits - 1)) - 1 : (((i128)1 << bits) - 1);
      i128 cv = c.cv.i; Type *ctt = cv_typeof(&c.cv); if (ctt && ctt->k == TY_INT && !ctt->sign && ctt->bits >= 128 && cv < 0) cv = hi + 1; /* huge u128 */
      int below = cv < lo, above = cv > hi; if (!below && !above) continue;
      /* rgt: runtime side always > constant; sw=1: runtime operand is on the left */
      int rgt = below; const char *o = op; int res;
      if (!strcmp(o, "==")) res = 0; else if (!strcmp(o, "!=")) res = 1;
      else { int lt = !strcmp(o, "<") || !strcmp(o, "<="), gt = !strcmp(o, ">") || !strcmp(o, ">=");
        /* left side relation */
        int left_gt = sw ? rgt : !rgt; res = lt ? !left_gt : gt ? left_gt : 0; }
      return CK(cv_bool(res));
    }
  }
  int eq = !strcmp(op, "=="), ne = !strcmp(op, "!=");
  if ((eq || ne) && !(a.ck && b.ck) && ((a.t->k == TY_STRUCT && is_packed(a.t)) || (b.t->k == TY_STRUCT && is_packed(b.t)))) {
    Type *pt = (a.t->k == TY_STRUCT && is_packed(a.t)) ? a.t : b.t, *h = int_type(tsize(pt) * 8, 0);
    a = coerce(a, pt); b = coerce(b, pt);
    a = V(h, a.ck ? fmt("%llu", (unsigned long long)cv_pack(&a.cv)) : load(h, addr_of(a)));
    b = V(h, b.ck ? fmt("%llu", (unsigned long long)cv_pack(&b.cv)) : load(h, addr_of(b)));
  }
  if ((eq || ne) && (a.t->k == TY_NULL || b.t->k == TY_NULL)) {
    Val o = a.t->k == TY_NULL ? b : a; char *h = opt_has(o), *r = tmp();
    emit("%s =w %s %s, 0", r, eq ? "ceqw" : "cnew", h); return V(t_bool, r);
  }
  if ((eq || ne) && !(a.ck && b.ck) && ((a.t->k == TY_OPT && !opt_is_ptr(a.t)) || (b.t->k == TY_OPT && !opt_is_ptr(b.t)))) {
    char *r = tmp();
    if (a.t->k == TY_OPT && b.t->k == TY_OPT) {
      char *ha = opt_has(a), *hb = opt_has(b); Val c = gen_cmp("==", rv(opt_payload(a, NULL)), rv(opt_payload(b, NULL)));
      char *same = tmp(), *nh = tmp(), *t1 = tmp();
      emit("%s =w ceqw %s, %s", same, ha, hb); emit("%s =w ceqw %s, 0", nh, ha); emit("%s =w or %s, %s", t1, nh, opnd(c));
      emit("%s =w and %s, %s", r, same, t1);
    } else {
      Val o = a.t->k == TY_OPT ? a : b, x = a.t->k == TY_OPT ? b : a;
      char *h = opt_has(o); Val c = gen_cmp("==", rv(opt_payload(o, NULL)), x);
      emit("%s =w and %s, %s", r, h, opnd(c));
    }
    if (ne) { char *r2 = tmp(); emit("%s =w xor %s, 1", r2, r); r = r2; }
    return V(t_bool, r);
  }
  if (a.t->k == TY_UNION && a.t->ct->tagged && b.t->k != TY_UNION) a = coerce(a, a.t->ct->tag);
  if (b.t->k == TY_UNION && b.t->ct->tagged && a.t->k != TY_UNION) b = coerce(b, b.t->ct->tag);
  Type *t = peer(a, b); a = coerce(a, t); b = coerce(b, t);
  if (is_wide(t) && !(a.ck && b.ck)) return w_cmp(op, t, a, b);
  if (a.ck && b.ck && (a.cv.k == CV_INT || a.cv.k == CV_BOOL || a.cv.k == CV_ERR) && a.cv.k == b.cv.k) return fold_bin(op, a, b);
  if (a.ck && b.ck && a.cv.k == CV_TYPE) { CVal r = {0}; r.k = CV_BOOL; r.t = t_bool; r.i = (a.cv.t == b.cv.t) == eq; return CK(r); }
  if (a.ck && b.ck && (a.cv.k == CV_FLOAT || b.cv.k == CV_FLOAT)) return fold_bin(op, a, b);
  if (is_float(t)) {
    if (t->k == TY_CFLOAT) { t = t_f64; a = coerce(a, t); b = coerce(b, t); }
    if (is_bigf(t)) { int k = eq ? 0 : ne ? 1 : !strcmp(op, "<") ? 2 : !strcmp(op, "<=") ? 3 : !strcmp(op, ">") ? 4 : 5; char *x = opnd(a), *y = opnd(b), *r = tmp();
      emit("%s =w call $zb_fcmp(w %d, w %d, l %s, l %s)", r, t->bits, k, x, y); return V(t_bool, r); }
    const char *fc = eq ? "ceq" : ne ? "cne" : !strcmp(op, "<") ? "clt" : !strcmp(op, ">") ? "cgt" : !strcmp(op, "<=") ? "cle" : "cge";
    char *x = opnd(a), *y = opnd(b), *r = tmp(); emit("%s =w %s%c %s, %s", r, fc, qc(t), x, y); return V(t_bool, r);
  }
  int sg = (t->k == TY_INT && t->sign);
  const char *cc = eq ? "ceq" : ne ? "cne" : !strcmp(op, "<") ? (sg ? "cslt" : "cult") : !strcmp(op, ">") ? (sg ? "csgt" : "cugt")
    : !strcmp(op, "<=") ? (sg ? "csle" : "cule") : (sg ? "csge" : "cuge");
  char *x = opnd(a), *y = opnd(b), *r = tmp();
  emit("%s =w %s%c %s, %s", r, cc, qc(t), x, y);
  return V(t_bool, r);
}
static Val gen_arith(const char *op, Val a, Val b) {
  a = rv(a); b = rv(b);
  if ((is_vec(a.t) || is_vec(b.t)) && !(a.ck && b.ck)) return vec_bin(op, a, b, 0);
  if ((a.t->k == TY_MPTR || a.t->k == TY_PTR) && (b.t->k == TY_MPTR || b.t->k == TY_PTR) && op[0] == '-') { char *d = tmp(), *r = tmp(); emit("%s =l sub %s, %s", d, opnd(a), opnd(b)); emit("%s =l udiv %s, %d", r, d, tsize(a.t->elem) ? tsize(a.t->elem) : 1); return V(t_usize, r); }
  if (a.t->k == TY_MPTR && (op[0] == '+' || op[0] == '-') && b.t->k != TY_MPTR) {
    b = coerce(b, t_usize); char *o = tmp(), *r = tmp();
    emit("%s =l mul %s, %d", o, opnd(b), tsize(a.t->elem)); emit("%s =l %s %s, %s", r, op[0] == '+' ? "add" : "sub", opnd(a), o);
    return V(a.t, r);
  }
  if (a.t->k == TY_MPTR && b.t->k == TY_MPTR) { char *d = tmp(), *r = tmp(); emit("%s =l sub %s, %s", d, opnd(a), opnd(b)); emit("%s =l udiv %s, %d", r, d, tsize(a.t->elem)); return V(t_usize, r); }
  int shift = !strcmp(op, "<<") || !strcmp(op, ">>") || !strcmp(op, "<<|");
  Type *t = shift ? a.t : peer(a, b);
  if (a.ck && b.ck && (a.cv.k == CV_INT || a.cv.k == CV_BOOL || a.cv.k == CV_FLOAT)) return fold_bin(op, coerce(a, t), b);
  if (t->k == TY_CINT) t = t_i64;
  if (t->k == TY_CFLOAT) t = t_f64;
  if (t->k == TY_FLOAT) {
    a = coerce(a, t); b = coerce(b, t); char c = qc(t), *x = opnd(a), *y = opnd(b), *r = tmp();
    if (is_bigf(t)) { int k = op[0] == '+' ? 0 : op[0] == '-' ? 1 : op[0] == '*' ? 2 : op[0] == '/' ? 3 : op[0] == '%' ? 4 : -1; if (k < 0) die("unsupported float operator %s", op); return V(t, bigf_op(k, t, x, y)); }
    if (op[0] == '%') { emit("%s =%c call $%s(%c %s, %c %s)", r, c, c == 's' ? "fmodf" : "fmod", c, x, c, y); return V(t, r); }
    const char *ins = op[0] == '+' ? "add" : op[0] == '-' ? "sub" : op[0] == '*' ? "mul" : op[0] == '/' ? "div" : NULL;
    if (!ins) die("unsupported float operator %s", op);
    emit("%s =%c %s %s, %s", r, c, ins, x, y); return V(t, r);
  }
  if (t->k == TY_INT && !is_wide(t) && (!strcmp(op, "+|") || !strcmp(op, "-|") || !strcmp(op, "*|") || !strcmp(op, "<<|"))) return sat_arith(op, t, coerce(a, t), b);
  if (is_wide(t)) { const char *o2 = op; return w_arith(o2, t, shift ? a : a, b); }
  a = coerce(a, t); if (!shift) b = coerce(b, t);
  int sg = t->k == TY_INT && t->sign; char c = qc(t);
  const char *ins;
  if (op[0] == '+') ins = "add"; else if (op[0] == '-') ins = "sub"; else if (op[0] == '*') ins = "mul";
  else if (op[0] == '/') ins = sg ? "div" : "udiv"; else if (op[0] == '%') ins = sg ? "rem" : "urem";
  else if (!strcmp(op, "&")) ins = "and"; else if (!strcmp(op, "|")) ins = "or"; else if (!strcmp(op, "^")) ins = "xor";
  else if (!strcmp(op, "<<") || !strcmp(op, "<<|")) ins = "shl"; else if (!strcmp(op, ">>")) ins = sg ? "sar" : "shr";
  else die("unsupported operator %s", op);
  char *x = opnd(a), *y = opnd(b);
  if (shift) { if (b.ck) y = fmt("%lld", (long long)b.cv.i); else if (c == 'l' && qc(b.t) == 'w') { char *e = tmp(); emit("%s =l extuw %s", e, y); y = e; } }
  char *r = tmp(); emit("%s =%c %s %s, %s", r, c, ins, x, y);
  if (op[1] == '%' || op[1] == '|' || !strcmp(op, "<<") || op[0] == '+' || op[0] == '-' || op[0] == '*') r = norm(r, t);
  return V(t, r);
}
static Val gen_logic(Node *n, Scope *s) {
  int isand = !strcmp(n->s, "and");
  Val a = coerce(gen(n->a, s, t_bool), t_bool);
  if (a.ck) { if (isand ? !a.cv.i : a.cv.i) return a; return coerce(gen(n->b, s, t_bool), t_bool); }
  char *sl = slot(t_bool), *lr = newl(), *le = newl();
  char *x = opnd(a); store(t_bool, x, sl);
  if (isand) br(x, lr, le); else br(x, le, lr);
  label(lr); Val b = coerce(gen(n->b, s, t_bool), t_bool); store(t_bool, opnd(b), sl); jmp(le);
  label(le); return V(t_bool, load(t_bool, sl));
}
static Val gen_init(Node *n, Scope *s, Type *ex) {
  Type *t;
  if (n->a && n->a->k == N_TARRAY && !n->a->a) {
    int hs = 0; int64_t sv = 0; if (n->a->c) { CVal c; ceval(n->a->c, s, &c); hs = 1; sv = c.i; }
    t = array_of(eval_type(n->a->b, s), n->list.n, hs, sv);
  } else t = n->a ? eval_type(n->a, s) : ex;
  if (t && (t->k == TY_OPT || t->k == TY_ERRU) && t->elem->k != TY_VOID) return coerce(gen_init(n, s, t->elem), t);
  Type *hint = NULL; /* partially typed tuple (fields of type anytype are inferred) */
  if (t && is_tuple_type(t) && !(n->flags & F_FIELDS)) { layout(t->ct); for (int i = 0; i < t->ct->fields.n; i++) if (((Field *)t->ct->fields.a[i])->t->k == TY_ANYTYPE) { hint = t; t = NULL; break; } }
  if (!t || t->k == TY_ANYTYPE) {
    Vec names = {0}, types = {0}, vals = {0}; CVal **cts = xalloc(sizeof(CVal *) * (n->list.n + 1)); int nct = 0;
    for (int i = 0; i < n->list.n; i++) {
      Type *ht = hint && i < hint->ct->fields.n ? ((Field *)hint->ct->fields.a[i])->t : NULL; if (ht && ht->k == TY_ANYTYPE) ht = NULL;
      Val v = rv(gen(n->list.a[i], s, ht)); if (ht) v = coerce(v, ht); if (v.t->k == TY_CINT) v = coerce(v, t_i64); else if (v.t->k == TY_CFLOAT) v = coerce(v, t_f64);
      if (v.ck && (v.cv.k == CV_ENUMLIT || v.cv.k == CV_TYPE)) { cts[i] = xalloc(sizeof(CVal)); *cts[i] = v.cv; nct++; }
      Val *pv = xalloc(sizeof *pv); *pv = v; vpush(&vals, pv); vpush(&types, v.t);
      vpush(&names, (n->flags & F_FIELDS) ? ((Node *)n->list2.a[i])->s : fmt("%d", i));
    }
    t = nct ? mk_anon_struct_cv(&names, &types, !(n->flags & F_FIELDS), cts) : mk_anon_struct(&names, &types, !(n->flags & F_FIELDS));
    char *sl = slot(t);
    for (int i = 0; i < vals.n; i++) { Field *f = t->ct->fields.a[i]; if (f->is_ct) continue; put(*(Val *)vals.a[i], f->t, addp(sl, f->off)); }
    return V(t, sl);
  }
  char *sl = slot(t);
  if (t->k == TY_STRUCT || t->k == TY_TUPLE) {
    Container *c = t->ct; layout(c);
    char *set = xalloc(c->fields.n + 1);
    if (is_packed(t)) {
      store(int_type(tsize(t) * 8, 0), "0", sl);
      for (int pass = 0; pass < 2; pass++)
        for (int i = 0; i < (pass ? c->fields.n : n->list.n); i++) {
          Field *f; Node *vn;
          if (!pass) { f = (n->flags & F_FIELDS) ? find_field(c, ((Node *)n->list2.a[i])->s) : c->fields.a[i]; vn = n->list.a[i];
            for (int j = 0; j < c->fields.n; j++) if (c->fields.a[j] == f) set[j] = 1; }
          else { f = c->fields.a[i]; if (set[i] || !f->def) continue; vn = f->def; }
          Val v = coerce(gen(vn, pass ? c->scope : s, f->t), f->t);
          if (v.ck && v.cv.k == CV_UNDEF) continue;
          Val l = LV(f->t, sl); l.bf = 1; l.hbytes = tsize(t); l.bitoff = f->bitoff; put_lv(v, l);
        }
      return V(t, sl);
    }
    for (int i = 0; i < n->list.n; i++) {
      Field *f = (n->flags & F_FIELDS) ? find_field(c, ((Node *)n->list2.a[i])->s) : c->fields.a[i];
      if (!f) die("%s:%d: no such field", n->tok->file, n->tok->line);
      for (int j = 0; j < c->fields.n; j++) if (c->fields.a[j] == f) set[j] = 1;
      Val v = coerce(gen(n->list.a[i], s, f->t), f->t); put(v, f->t, addp(sl, f->off));
    }
    for (int j = 0; j < c->fields.n; j++) {
      Field *f = c->fields.a[j]; if (set[j] || !f->def) continue;
      Val v = coerce(gen(f->def, c->scope, f->t), f->t); put(v, f->t, addp(sl, f->off));
    }
    return V(t, sl);
  }
  if (t->k == TY_UNION) {
    if (!n->list.n) return V(t, sl);
    Field *f = find_field(t->ct, ((Node *)n->list2.a[0])->s);
    Val v = coerce(gen(n->list.a[0], s, f->t), f->t); put(v, f->t, sl);
    if (t->ct->tagged) store(t->ct->tag, fmt("%lld", (long long)f->val), addp(sl, union_tag_off(t)));
    return V(t, sl);
  }
  if (t->k == TY_ARRAY) {
    int es = tsize(t->elem);
    for (int i = 0; i < n->list.n; i++) { Val v = coerce(gen(n->list.a[i], s, t->elem), t->elem); put(v, t->elem, addp(sl, (int64_t)i * es)); }
    if (t->hassent) store(t->elem, fmt("%lld", (long long)t->sent), addp(sl, t->len * es));
    return V(t, sl);
  }
  if (t->k == TY_VOID) return VOIDV();
  die("%s:%d: cannot initialize %s with init list", n->tok->file, n->tok->line, tname(t));
}

/* ---------- calls ---------- */
static int all_ct_fields(Type *t) { /* tuple/struct whose fields are all comptime: its value is implied by the type */
  if (!t || !is_tuple_type(t) || !t->ct) return 0; layout(t->ct);
  for (int i = 0; i < t->ct->fields.n; i++) { Field *f = t->ct->fields.a[i]; int k = f->t->k;
    if (!f->is_ct && k != TY_ENUMLIT && k != TY_CINT && k != TY_CFLOAT && k != TY_TYPE && k != TY_NULL && !all_ct_fields(f->t)) return 0; } return 1; }
static int param_ct(Node *p) { return (p->flags & F_COMPTIME) || (p->a && p->a->k == N_IDENT && !strcmp(p->a->s, "type")); }
static char *argtxt(Val v, Type *t) {
  if (tsize(t) == 0) return NULL;
  if (is_aggr(t)) return fmt("l %s", addr_of(v));
  return fmt("%c %s", qc(t), opnd(v));
}
static Val do_call(char *callee, Vec *args, Type *ret, int ext) {
  char buf[4096]; int m = 0; buf[0] = 0; char *sl = NULL;
  if (is_aggr(ret)) { sl = slot(ret); m += snprintf(buf + m, sizeof buf - m, "l %s", sl); }
  for (int i = 0; i < args->n; i++) if (args->a[i]) m += snprintf(buf + m, sizeof buf - m, "%s%s", m ? ", " : "", (char *)args->a[i]);
  if (ret->k == TY_VOID || ret->k == TY_NORET || sl || tsize(ret) == 0) {
    emit("call %s(%s)", callee, buf);
    if (ret->k == TY_NORET) { emit("hlt"); term = 1; return NORET(); }
    if (sl) return V(ret, sl);
    return ret->k == TY_VOID ? VOIDV() : V(ret, "0");
  }
  char *r = tmp(); emit("%s =%c call %s(%s)", r, qc(ret), callee, buf);
  if (ext && (ret->k == TY_BOOL || (ret->k == TY_INT && ret->bits < 32))) r = norm(r, ret->k == TY_BOOL ? t_u8 : ret);
  return V(ret, r);
}
static Val gen_block(Node *n, Scope *s, Type *ex);
static void run_defers(int base, char *errop);
static Val gen_inline_body(FnInst *fi, Val *vals) { if (getenv("ZB_INLDBG")) fprintf(stderr, "inline %s\n", fi->d->name);
  Node *f = fi->node; Scope *fs = new_scope(fi->scope, NULL);
  for (int i = 0; i < f->list.n; i++) {
    Node *p = f->list.a[i]; Type *t = fi->ptypes.a[i];
    if (!t || !p->s) continue;
    Val v = vals[i];
    if (v.ck && v.cv.k != CV_UNDEF) { bind_cval(fs, p->s, ccoerce(v.cv, t)); continue; }
    v = rv(v);
    if (tsize(t) == 0) { bind_local(fs, p->s, t, "0"); continue; }
    char *sl = slot(t); put(v, t, sl); bind_local(fs, p->s, t, sl);
  }
  Type *sfret = fret; Loop *sl = loops; Inl *si = inl; int sdn = defers.n;
  Res R; memset(&R, 0, sizeof R); R.ex = fi->ret; Inl I; memset(&I, 0, sizeof I); I.res = &R; I.lx = newl(); I.dbase = defers.n; I.allck = 1; I.level = in_typeof;
  fret = fi->ret; loops = NULL; inl = &I;
  gen_block(f->b, fs, NULL);
  if (!term) {
    run_defers(I.dbase, NULL);
    if (!term) {
      if (fret->k == TY_ERRU) { char *e = slot(fret); store(t_u16, "0", e); res_put(&R, V(fret, e)); I.allck = 0; I.nret++; }
      else if (fret->k == TY_VOID) { res_put(&R, VOIDV()); I.nret++; if (I.nret > 1) I.allck = 0; I.ckv = cv_void(); }
      else emit("hlt");
      jmp(I.lx);
    }
  }
  fret = sfret; loops = sl; inl = si; defers.n = sdn;
  label(I.lx);
  if (!R.has) { if (!term) emit("hlt"); term = 1; return NORET(); }
  term = 0;
  Val r = res_get(&R);
  if (I.allck && I.nret > 0 && fi->ret->k != TY_VOID && I.ckv.k != CV_VOID) { Val c = CK(I.ckv); c.t = fi->ret; return c; }
  return r;
}
static Val gen_call(Node *n, Scope *s, Type *ex) {
  Node *cal = n->a; Decl *fd = NULL; Val self; int has_self = 0; Val fnv; memset(&fnv, 0, sizeof fnv); memset(&self, 0, sizeof self);
  if (cal->k == N_FIELD) {
    Val base; int got = 0;
    { /* method with a comptime self parameter: evaluate the receiver at comptime instead of generating it */
      Type *bt = typeof_impl(cal->a, s); if (bt && bt->k == TY_PTR) bt = bt->elem;
      if (bt && bt->k != TY_TYPE && bt->ct) { Decl *d = find_decl(bt->ct, cal->s);
        if (d) { resolve_decl(d); Decl *fdd = d->kind == D_FN || (d->kind == D_CONST && d->cv.k == CV_FN) ? d->cv.fn : NULL;
          if (fdd && fdd->node && fdd->node->list.n && param_ct(fdd->node->list.a[0])) { CVal cv; if (ceval_force(cal->a, s, &cv)) { base = CK(cv); got = 1; } } } } }
    if (!got) base = gen(cal->a, s, NULL);
    if (base.ck && base.cv.k == CV_TYPE) { CVal m; if (!ceval_member(base.cv, cal->s, &m)) die("%s:%d: no decl '%s' in %s", n->tok->file, n->tok->line, cal->s, tname(base.cv.t)); fnv = CK(m); }
    else {
      Type *ct = base.t->k == TY_PTR ? base.t->elem : base.t; Decl *d = ct->ct ? find_decl(ct->ct, cal->s) : NULL;
      if (d) { resolve_decl(d); if (d->kind == D_FN || (d->kind == D_CONST && d->cv.k == CV_FN)) { fd = d->cv.fn; has_self = 1; self = base; } else fnv = gen_member(base, cal->s, cal); }
      else fnv = gen_member(base, cal->s, cal);
    }
  } else if (cal->k == N_ENUMLIT && ex) {
    Type *bt = ex; while (bt->k == TY_OPT || bt->k == TY_ERRU || bt->k == TY_PTR) bt = bt->elem;
    Decl *d = bt->ct ? find_decl(bt->ct, cal->s) : NULL; if (!d) die("%s:%d: no decl '%s' in %s", n->tok->file, n->tok->line, cal->s, tname(bt));
    resolve_decl(d); fnv = CK(d->cv);
  } else fnv = gen(cal, s, NULL);
  if (!fd && fnv.ck && fnv.cv.k == CV_FN) fd = fnv.cv.fn;
  if (fd) {
    Node *f = fd->node;
    if (fn_returns_ctonly(fd)) { CVal r; if (!ceval_force(n, s, &r)) die("%s:%d: cannot evaluate call to %s at comptime (at %s)", n->tok->file, n->tok->line, fd->name, ct_fail_loc()); return CK(r); }
    if (fn_takes_ctonly(fd)) { CVal r; if (ceval_force(n, s, &r)) return CK(r); if (getenv("ZB_CT_TRACE")) fprintf(stderr, "ctonly call failed %s:%d (%s)\n", n->tok->file, n->tok->line, ct_fail_loc()); }
    Scope *pscope = new_scope(fd->ct->scope, NULL);
    Vec cargs = {0}; int np = f->list.n; Val *pre = xalloc(sizeof(Val) * (np + n->list.n + 2)); char *haspre = xalloc(np + n->list.n + 2);
    for (int i = 0; i < np; i++) {
      Node *p = f->list.a[i]; int ai = i - has_self;
      if (p->flags & F_VARARGS) { vpush(&cargs, NULL); break; }
      if (i == 0 && has_self) {
        if (p->flags & F_ANYTYPE) { CVal *c = xalloc(sizeof *c); c->k = CV_TYPE; c->t = self.t; c->slen = -1; vpush(&cargs, c); pre[i] = self; haspre[i] = 1; if (p->s) bind_placeholder(pscope, p->s, self.t); }
        else if (param_ct(p)) { /* comptime self parameter */
          CVal *c = xalloc(sizeof *c); Type *pt = NULL;
          if (p->a) { CVal tv; if (ceval_force(p->a, pscope, &tv) && tv.k == CV_TYPE) pt = tv.t; }
          if (self.ck) *c = self.cv; else if (!ceval_force(cal->a, s, c)) die("%s:%d: comptime self argument is not comptime-known (at %s)", n->tok->file, n->tok->line, ct_fail_loc());
          if (pt && pt->k == TY_PTR && c->k != CV_PTR) { CVal pv = {0}; pv.k = CV_PTR; pv.base = xalloc(sizeof(CVal)); *pv.base = *c; pv.idx = -1; pv.t = pt; *c = pv; }
          else if (pt && pt->k != TY_PTR && c->k == CV_PTR) { CVal pv; if (ceval_force(cal->a, s, &pv)) *c = pv; }
          if (pt) *c = ccoerce(*c, pt);
          if (p->s) bind_cval(pscope, p->s, *c);
          vpush(&cargs, c);
        }
        else vpush(&cargs, NULL);
        continue;
      }
      Node *an = n->list.a[ai];
      if (param_ct(p)) {
        CVal *c = xalloc(sizeof *c); Type *pt = NULL;
        if (p->a) { CVal tv; if (ceval_force(p->a, pscope, &tv) && tv.k == CV_TYPE) pt = tv.t; }
        if (!ceval_rt(an, s, pt, c)) die("%s:%d: comptime argument is not comptime-known (at %s)", an->tok->file, an->tok->line, ct_fail_loc());
        if (pt) *c = ccoerce(*c, pt);
        if (p->s) bind_cval(pscope, p->s, *c);
        vpush(&cargs, c); continue;
      }
      if (p->flags & F_ANYTYPE) {
        Val v = rv(gen(an, s, NULL)); CVal *c = xalloc(sizeof *c);
        if (getenv("ZB_DBGA") && p->s && !strcmp(p->s, getenv("ZB_DBGA"))) { fprintf(stderr, "anyarg ck=%d k=%d t=%s at %s:%d:", v.ck, v.cv.k, tname(v.t), an->tok->file, an->tok->line); if (v.t->ct) { layout(v.t->ct); for (int q = 0; q < v.t->ct->fields.n; q++) { Field *f = v.t->ct->fields.a[q]; fprintf(stderr, " %s:%d:%s", f->name, f->is_ct, tname(f->t)); } } fprintf(stderr, "\n"); }
        if (v.ck && (type_is_ctonly(v.t) || v.cv.k == CV_FN || all_ct_fields(v.t))) *c = v.cv; else { if (v.t->k == TY_CINT) v = coerce(v, t_i64); else if (v.t->k == TY_CFLOAT) v = coerce(v, t_f64); c->k = CV_TYPE; c->t = v.t; c->slen = -1; pre[i] = v; haspre[i] = 1; }
        if (p->s) { if (c->k == CV_TYPE && c->slen == -1) bind_placeholder(pscope, p->s, c->t); else bind_cval(pscope, p->s, *c); }
        vpush(&cargs, c); continue;
      }
      vpush(&cargs, NULL);
    }
    while (cargs.n < np) vpush(&cargs, NULL);
    FnInst *fi = fn_instance(fd, &cargs);
    if (fi->ret && type_is_ctonly(fi->ret)) { CVal r; if (!ceval_force(n, s, &r)) die("%s:%d: cannot evaluate call to %s (returns comptime-only %s) at comptime (at %s)", n->tok->file, n->tok->line, fd->name, tname(fi->ret), ct_fail_loc()); return CK(r); }
    Vec args = {0}; int va = 0;
    Val *inl_vals = NULL; static int inl_depth;
    static int noinl = -1; if (noinl < 0) noinl = !!getenv("ZB_NOINLINE");
    if (!noinl && (f->flags & F_INLINE) && !(f->flags & F_EXTERN) && f->b && inl_depth < 48) { inl_vals = xalloc(sizeof(Val) * (np + 1)); for (int i = 0; i < np; i++) if (((Node *)f->list.a[i])->flags & F_VARARGS) inl_vals = NULL; }
    for (int i = 0; i < np; i++) {
      Node *p = f->list.a[i]; Type *pt = fi->ptypes.a[i];
      if (p->flags & F_VARARGS) { va = 1; break; }
      if (!pt) continue;
      Val v;
      if (haspre[i]) v = pre[i];
      else if (i == 0 && has_self) {
        v = self;
        if (pt->k == TY_PTR && self.t->k != TY_PTR) v = V(ptr_to(self.t, 0), addr_of(self));
        else if (pt->k != TY_PTR && self.t->k == TY_PTR) v = LV(self.t->elem, opnd(self));
      } else v = gen(n->list.a[i - has_self], s, pt);
      v = coerce(v, pt);
      if (v.t->k == TY_NORET) return v;
      if (inl_vals) {
        if (!v.ck && !(i == 0 && has_self)) { CVal c; if (ceval(n->list.a[i - has_self], s, &c) && c.k != CV_UNDEF && c.k != CV_VOID) { Val cv = CK(c); cv.t = pt; v = cv; } }
        inl_vals[i] = v; continue;
      }
      if ((f->flags & F_EXTERN) && is_packed(pt) && tsize(pt) <= 8) { Type *h = int_type(tsize(pt) * 8, 0); vpush(&args, fmt("%c %s", qc(h), load(h, addr_of(v)))); continue; }
      char *a = argtxt(v, pt); if (a) vpush(&args, a);
    }
    if (va) {
      vpush(&args, "...");
      for (int j = np - 1 - has_self; j < n->list.n; j++) {
        Val v = rv(gen(n->list.a[j], s, NULL));
        if (v.t->k == TY_CINT) v = coerce(v, (v.cv.i > 2147483647LL || v.cv.i < -2147483648LL) ? t_i64 : t_i32);
        if (v.ck && v.cv.k == CV_STR) v = coerce(v, mptr_to(t_u8, 1, 1, 0));
        if (v.t->k == TY_CFLOAT) v = coerce(v, t_f64); else if (v.t->k == TY_FLOAT && v.t->bits < 64) v = float_conv(v, t_f64);
        Type *t = v.t; if (t->k == TY_BOOL || (t->k == TY_INT && t->bits < 32)) { v = coerce(v, t->k == TY_INT && t->sign ? t_i32 : t_u32); t = v.t; }
        vpush(&args, argtxt(v, t));
      }
    }
    if (inl_vals) { inl_depth++; Val r = gen_inline_body(fi, inl_vals); inl_depth--; return r; }
    queue_fn(fi);
    return do_call(fmt("$%s", fi->sym), &args, fi->ret, !!(f->flags & F_EXTERN));
  }
  /* indirect call through function pointer */
  Val fp = rv(fnv); Type *ft = fp.t->k == TY_PTR ? fp.t->elem : fp.t;
  if (ft->k == TY_OPT) ft = ft->elem->k == TY_PTR ? ft->elem->elem : ft->elem;
  if (ft->k != TY_FN) die("%s:%d: call of non-function %s", n->tok->file, n->tok->line, tname(fp.t));
  Vec args = {0}; char *callee = opnd(fp);
  for (int i = 0; i < n->list.n; i++) {
    Type *pt = i < ft->params.n ? ft->params.a[i] : NULL; Val v = gen(n->list.a[i], s, pt);
    if (pt) v = coerce(v, pt); else v = rv(v);
    char *a = argtxt(v, pt ? pt : v.t); if (a) vpush(&args, a);
  }
  return do_call(callee, &args, ft->ret, 0);
}

/* ---------- builtins ---------- */
static Val int_conv(Val v, Type *to, int trunc) {
  v = rv(v);
  if (v.ck) { CVal c = v.cv; c.t = to; if (trunc) c.i = wrap_int(c.i, to); return CK(c); }
  if (is_wide(v.t) || is_wide(to)) return wconv(v, to);
  Type *f = v.t; if (f->k == TY_BOOL) f = t_u1;
  if (f->k == TY_ENUM) f = f->ct->tag;
  char *o = opnd(v);
  if (qc(f) == 'w' && qc(to) == 'l') { char *r = tmp(); emit("%s =l %s %s", r, f->sign ? "extsw" : "extuw", o); return V(to, r); }
  if (qc(f) == 'l' && qc(to) == 'w') { char *r = tmp(); emit("%s =w copy %s", r, o); return V(to, norm(r, to)); }
  if (to->k == TY_INT && f->k == TY_INT && (to->bits < f->bits || to->sign != f->sign)) return V(to, norm(o, to));
  return V(to, o);
}
static Val gen_minmax(Node *n, Scope *s, Type *ex, int mn) {
  Val acc = rv(gen(n->list.a[0], s, NULL));
  for (int i = 1; i < n->list.n; i++) {
    Val b = rv(gen(n->list.a[i], s, NULL)); Type *t = peer(acc, b); if (t->k == TY_CINT) t = ex && ex->k == TY_INT ? ex : t_i64;
    acc = coerce(acc, t); b = coerce(b, t);
    Val c = gen_cmp(mn ? "<" : ">", acc, b);
    char *sl = slot(t), *la = newl(), *lb = newl(), *le = newl();
    br(opnd(c), la, lb); label(la); store(t, opnd(acc), sl); jmp(le); label(lb); store(t, opnd(b), sl); jmp(le); label(le);
    acc = V(t, load(t, sl));
  }
  return acc;
}
static Val gen_builtin(Node *n, Scope *s, Type *ex) {
  const char *b = n->s; Node *x = n->list.n ? n->list.a[0] : NULL, *y = n->list.n > 1 ? n->list.a[1] : NULL;
  CVal c; Type *ex0 = ex; if (ex && ex->k == TY_ERRU) ex = ex->elem;
  if (!strcmp(b, "backingInt")) { Type *at = typeof_impl(x, s);
    if (at->k == TY_ENUM || (at->k == TY_UNION && at->ct->tagged) || at->k == TY_INT || at->k == TY_CINT) b = "intFromEnum"; else { b = "bitCast"; ex = ex0 = int_type(bits_of(at), 0); } }
  else if (!strcmp(b, "fromBackingInt")) { Type *u = ex && ex->k == TY_OPT ? ex->elem : ex; if (!u) die("%s:%d: @fromBackingInt needs a result type", n->tok->file, n->tok->line); 
    if (u->ct) layout(u->ct); Type *bt = u->k == TY_ENUM ? u->ct->tag : int_type(bits_of(u), 0);
    Val v = coerce(rv(gen(x, s, bt)), bt); if (v.ck && u->k == TY_ENUM) { CVal r = v.cv; r.t = u; return CK(r); }
    if (u->k == TY_ENUM) return V(u, opnd(v));
    if (!is_aggr(u)) return V(u, opnd(v));
    char *sl = slot(u); store(bt, opnd(v), sl); return V(u, sl); }
  if (!strcmp(b, "divCeil")) {
    Val a = rv(gen(x, s, ex)), d = rv(gen(y, s, ex)); Type *t = peer(a, d); if (t->k == TY_CINT) t = ex ? ex : t_i64;
    a = coerce(a, t); d = coerce(d, t); if (is_wide(t)) die("%s:%d: @divCeil on wide ints unsupported", n->tok->file, n->tok->line);
    char cl = qc(t), *A = opnd(a), *D = opnd(d), *q = tmp(), *r = tmp(), *nz = tmp(), *adj = tmp(), *ext = tmp(), *res = tmp();
    emit("%s =%c %s %s, %s", q, cl, t->sign ? "div" : "udiv", A, D); emit("%s =%c %s %s, %s", r, cl, t->sign ? "rem" : "urem", A, D);
    emit("%s =w cne%c %s, 0", nz, cl, r);
    if (t->sign) { char *x1 = tmp(), *pos = tmp(); emit("%s =%c xor %s, %s", x1, cl, r, D); emit("%s =w csge%c %s, 0", pos, cl, x1); emit("%s =w and %s, %s", adj, nz, pos); }
    else emit("%s =w copy %s", adj, nz);
    if (cl == 'l') emit("%s =l extuw %s", ext, adj); else emit("%s =w copy %s", ext, adj);
    emit("%s =%c add %s, %s", res, cl, q, ext); return V(t, norm(res, t));
  }
  if (!strcmp(b, "call")) {
    Node *fnn = y, *an = n->list.a[2]; Node *cn = xalloc(sizeof *cn); cn->k = N_CALL; cn->tok = n->tok; cn->a = fnn;
    if (an->k == N_INIT && !an->a && !(an->flags & F_FIELDS)) { for (int i = 0; i < an->list.n; i++) vpush(&cn->list, an->list.a[i]); }
    else {
      Type *tt = typeof_impl(an, s); if (tt->k == TY_PTR) tt = tt->elem; if (!tt->ct) die("%s:%d: @call args must be a tuple", n->tok->file, n->tok->line); layout(tt->ct);
      for (int i = 0; i < tt->ct->fields.n; i++) { Node *f = xalloc(sizeof *f); f->k = N_FIELD; f->tok = an->tok; f->a = an; f->s = fmt("%d", i); vpush(&cn->list, f); }
    }
    return gen(cn, s, ex0);
  }
  if (!strcmp(b, "errorCast")) { Val v = rv(gen(x, s, NULL)); if (ex0 && (ex0->k == TY_ERRU || ex0->k == TY_ERRSET) && v.t->k == ex0->k) { if (v.ck) { v.cv.t = ex0; } v.t = ex0; } return v; }
  if (strcmp(b, "memcpy") && strcmp(b, "memmove") && strncmp(b, "atomic", 6) && strcmp(b, "memset") && strcmp(b, "panic") && strcmp(b, "trap") && ceval_ex(n, s, ex, &c)) {
    Val v = CK(c); return ex && v.t->k == TY_CINT && ex->k == TY_INT ? coerce(v, ex) : v;
  }
  if (!strcmp(b, "as")) { Type *t = eval_type(x, s); return coerce(gen(y, s, t), t); }
  if (!strcmp(b, "splat")) { if (!ex || !is_vec(ex)) { if (ex && ex->k == TY_ARRAY) return vec_splat(gen(x, s, ex->elem), ex); die("%s:%d: @splat needs a vector result type", n->tok->file, n->tok->line); } return vec_splat(gen(x, s, ex->elem), ex); }
  if (!strcmp(b, "reduce")) {
    CVal op; if (!ceval_ex(x, s, NULL, &op)) die("@reduce op must be comptime"); const char *on = op.k == CV_ENUMLIT ? op.s : NULL;
    if (!on) { Container *rc = ((Type *)op.t)->ct; layout(rc); for (int i = 0; i < rc->fields.n; i++) { Field *f = rc->fields.a[i]; if (f->val == (int64_t)op.i) on = f->name; } }
    return vec_reduce(on, rv(gen(y, s, NULL)));
  }
  if (!strcmp(b, "select")) {
    Type *et = eval_type(x, s); Val m = rv(gen(y, s, NULL)); Type *vt = vec_of(et, m.t->len);
    Val a = coerce(rv(gen(n->list.a[2], s, vt)), vt), bb = coerce(rv(gen(n->list.a[3], s, vt)), vt);
    m = V(m.t, addr_of(m)); a = V(vt, addr_of(a)); bb = V(vt, addr_of(bb)); char *sl = slot(vt);
    for (int64_t i = 0; i < vt->len; i++) { Val r = sel2(vel(m, i), vel(a, i), vel(bb, i), et); put(r, et, addp(sl, i * tsize(et))); }
    return V(vt, sl);
  }
  if (!strcmp(b, "shuffle")) {
    Type *et = eval_type(x, s); Val a = rv(gen(y, s, NULL)), bb = rv(gen(n->list.a[2], s, NULL)); CVal mk;
    if (!ceval_force(n->list.a[3], s, &mk)) die("@shuffle mask must be comptime");
    int64_t ml = mk.k == CV_AGG ? mk.n : 0; Type *vt = vec_of(et, ml); char *sl = slot(vt);
    a = V(a.t, addr_of(a)); bb = V(bb.t, addr_of(bb));
    for (int64_t i = 0; i < ml; i++) { int64_t k = (int64_t)mk.el[i]->i; if (mk.el[i]->k == CV_UNDEF) k = 0; Val e = k >= 0 ? vel(a, k) : vel(bb, ~k); put(e, et, addp(sl, i * tsize(et))); }
    return V(vt, sl);
  }
  if (!strcmp(b, "floatFromInt") || !strcmp(b, "intFromFloat") || !strcmp(b, "floatCast")) {
    if (!ex) die("%s:%d: @%s needs a result type", n->tok->file, n->tok->line, b);
    Type *to = ex; if (to->k == TY_OPT) to = to->elem;
    if (is_vec(to)) { Val v = rv(gen(x, s, NULL)); Type *vt = v.t; char *sl = slot(to); v = V(vt, addr_of(v));
      for (int64_t i = 0; i < to->len; i++) put(float_conv(vel(v, i), to->elem), to->elem, addp(sl, i * tsize(to->elem))); return V(to, sl); }
    return float_conv(gen(x, s, NULL), to);
  }
  if (!strcmp(b, "sqrt") || !strcmp(b, "sin") || !strcmp(b, "cos") || !strcmp(b, "tan") || !strcmp(b, "exp") || !strcmp(b, "exp2") || !strcmp(b, "exp10") || !strcmp(b, "log") || !strcmp(b, "log2") || !strcmp(b, "log10") || !strcmp(b, "floor") || !strcmp(b, "ceil") || !strcmp(b, "trunc") || !strcmp(b, "round") || (!strcmp(b, "abs") && 0)) {
    Val v = rv(gen(x, s, ex)); if (v.t->k == TY_CFLOAT) v = coerce(v, ex && ex->k == TY_FLOAT ? ex : t_f64);
    Type *t = v.t;
    if (is_vec(t)) { char *sl = slot(t); Val av = V(t, addr_of(v));
      for (int64_t i = 0; i < t->len; i++) { char c = qc(t->elem), *r = tmp(); emit("%s =%c call $%s%s(%c %s)", r, c, b, c == 's' ? "f" : "", c, opnd(vel(av, i))); store(t->elem, r, addp(sl, i * tsize(t->elem))); }
      return V(t, sl); }
    if (is_bigf(t)) { static const char *nm[] = { "sqrt", "floor", "ceil", "trunc", "round", "sin", "cos", "tan", "exp", "exp2", "exp10", "log", "log2", "log10" };
      for (int k = 0; k < 14; k++) if (!strcmp(b, nm[k])) return V(t, bigf_op(10 + k, t, opnd(v), NULL)); }
    char c = qc(t), *r = tmp(); emit("%s =%c call $%s%s(%c %s)", r, c, b, c == 's' ? "f" : "", c, opnd(v)); return V(t, r);
  }
  if (!strcmp(b, "mulAdd")) {
    Type *t = eval_type(x, s); Val a1 = coerce(gen(y, s, t), t), a2 = coerce(gen(n->list.a[2], s, t), t), a3 = coerce(gen(n->list.a[3], s, t), t);
    if (is_bigf(t)) { char *sl = slot(t); emit("call $zb_fma(w %d, l %s, l %s, l %s, l %s)", t->bits, sl, opnd(a1), opnd(a2), opnd(a3)); return V(t, sl); }
    char c = qc(t), *r = tmp(); emit("%s =%c call $fma%s(%c %s, %c %s, %c %s)", r, c, c == 's' ? "f" : "", c, opnd(a1), c, opnd(a2), c, opnd(a3)); return V(t, r);
  }
  if (!strcmp(b, "intCast") || !strcmp(b, "truncate")) {
    if (!ex) die("%s:%d: @%s needs a result type", n->tok->file, n->tok->line, b);
    if (ex->k == TY_OPT) ex = ex->elem;
    return int_conv(gen(x, s, NULL), ex, b[0] == 't');
  }
  if (!strcmp(b, "bitCast")) {
    Val v = rv(gen(x, s, NULL)); if (!ex) die("@bitCast needs a result type");
    if (v.ck) { CVal r; if (ceval_rt(n, s, ex, &r)) { Val c = CK(r); c.t = ex; return c; } if (is_aggr(ex) || is_aggr(v.t)) v = V(v.t, mat(v)), v.ck = 0, v = is_aggr(v.t) ? V(v.t, addr_of(coerce(CK(v.cv), v.t))) : v; else return coerce(v, ex); }
    if (is_aggr(v.t) || is_aggr(ex)) { if (is_aggr(v.t)) { if (is_aggr(ex)) { if (is_wide(ex) && ex->bits < 128 && ex->bits > 64) { char *sl = slot(ex); blit(addr_of(v), sl, 16); wnorm(ex, sl); return V(ex, sl); } return V(ex, addr_of(v)); } return V(ex, load(ex, addr_of(v))); } char *sl = slot(ex); store(v.t, opnd(v), sl); return V(ex, sl); }
    if (v.t->k == TY_FLOAT && v.t->bits == 16 && ex->k != TY_FLOAT) { char *r = tmp(); emit("%s =w call $zb_f2h(s %s)", r, opnd(v)); return V(ex, norm(r, ex)); }
    if (ex->k == TY_FLOAT && ex->bits == 16 && v.t->k != TY_FLOAT) { char *r = tmp(); emit("%s =s call $zb_h2f(w %s)", r, opnd(v)); return V(ex, r); }
    if ((v.t->k == TY_FLOAT) != (ex->k == TY_FLOAT)) { char *r = tmp(); emit("%s =%c cast %s", r, qc(ex), opnd(v)); return V(ex, r); }
    return V(ex, norm(opnd(v), ex));
  }
  if (!strcmp(b, "ptrCast") || !strcmp(b, "alignCast") || !strcmp(b, "constCast") || !strcmp(b, "volatileCast")) {
    Val v = rv(gen(x, s, (b[0] == 'a' || b[0] == 'v') ? ex : NULL)); Type *to = ex ? ex : v.t;
    if (!strcmp(b, "constCast") && !ex) { if (v.t->k == TY_PTR) to = ptr_to(v.t->elem, 0); else if (v.t->k == TY_SLICE) to = slice_of(v.t->elem, 0); else if (v.t->k == TY_MPTR) to = mptr_to(v.t->elem, 0, v.t->hassent, v.t->sent); }
    if (to->k == TY_OPT && to->elem->k == TY_SLICE && v.t->k != TY_OPT) { /* cast to the slice, then wrap */
      Type *st = to->elem; Val r;
      if (v.t->k == TY_SLICE && tsize(v.t->elem) != tsize(st->elem) && tsize(st->elem) > 0) {
        char *a = addr_of(v), *l = load(t_u64, addp(a, 8)), *m = tmp(), *q = tmp(), *sl = slot(st);
        emit("%s =l mul %s, %d", m, l, tsize(v.t->elem)); emit("%s =l udiv %s, %d", q, m, tsize(st->elem));
        store(t_u64, load(t_u64, a), sl); store(t_u64, q, addp(sl, 8)); r = V(st, sl);
      } else { r = v; r.t = st; }
      return coerce(r, to);
    }
    if (v.t->k == TY_SLICE && to->k != TY_SLICE && !(to->k == TY_OPT && to->elem->k == TY_SLICE)) return V(to, load(t_u64, addr_of(v)));
    if (v.t->k == TY_SLICE && to->k == TY_SLICE && tsize(v.t->elem) != tsize(to->elem) && tsize(to->elem) > 0) {
      char *a = addr_of(v), *l = load(t_u64, addp(a, 8)), *m = tmp(), *q = tmp(), *sl = slot(to);
      emit("%s =l mul %s, %d", m, l, tsize(v.t->elem)); emit("%s =l udiv %s, %d", q, m, tsize(to->elem));
      store(t_u64, load(t_u64, a), sl); store(t_u64, q, addp(sl, 8)); return V(to, sl);
    }
    if (to->k == TY_SLICE && (v.t->k == TY_PTR || v.t->k == TY_MPTR)) {
      int64_t bytes = v.t->k == TY_PTR ? tsize(v.t->elem) : 0; int es = tsize(to->elem); char *sl = slot(to);
      store(t_u64, opnd(v), sl); store(t_u64, fmt("%lld", (long long)(es ? bytes / es : 0)), addp(sl, 8)); return V(to, sl);
    }
    if (is_aggr(to) || is_aggr(v.t)) { v.t = to; return v; }
    return V(to, opnd(v));
  }
  if (!strcmp(b, "intFromPtr")) { Val v = rv(gen(x, s, NULL)); if (v.t->k == TY_SLICE) return V(t_usize, load(t_u64, addr_of(v))); return V(t_usize, opnd(v)); }
  if (!strcmp(b, "ptrFromInt")) { Val v = coerce(gen(x, s, t_usize), t_usize); return V(ex, opnd(v)); }
  if (!strcmp(b, "intFromBool")) { Val v = coerce(gen(x, s, t_bool), t_bool); return V(t_u1, opnd(v)); }
  if (!strcmp(b, "intFromEnum")) {
    Val v = rv(gen(x, s, NULL)); Type *t = v.t; if (t->ct) layout(t->ct); if (t->k == TY_UNION && t->ct->tag && t->ct->tag->ct) layout(t->ct->tag->ct);
    if (t->k == TY_UNION) { return V(t->ct->tag->ct->tag, load(t->ct->tag, addp(addr_of(v), union_tag_off(t)))); }
    return V(t->ct->tag, opnd(v));
  }
  if (!strcmp(b, "enumFromInt")) { if (ex && ex->k == TY_OPT) ex = ex->elem; if (!ex || ex->k != TY_ENUM) die("%s:%d: @enumFromInt needs an enum result type", n->tok->file, n->tok->line); } 
  if (!strcmp(b, "enumFromInt")) { layout(ex->ct); Val v = rv(gen(x, s, NULL)); if (v.ck) { CVal r = v.cv; r.t = ex; return CK(r); } return V(ex, opnd(int_conv(v, ex->ct->tag, 0))); }
  if (!strcmp(b, "intFromError")) { Val v = rv(gen(x, s, NULL)); return V(t_u16, opnd(v)); }
  if (!strcmp(b, "errorFromInt")) { Val v = coerce(gen(x, s, t_u16), t_u16); return V(t_errset, opnd(v)); }
  if (!strcmp(b, "errorName")) {
    Val v = rv(gen(x, s, NULL)); char *e = opnd(v), *w = tmp(), *o = tmp(), *a = tmp();
    emit("%s =l extuw %s", w, e); emit("%s =l mul %s, 16", o, w); emit("%s =l add $zb.errnames, %s", a, o);
    return V(slice_of(t_u8, 1), a);
  }
  if (!strcmp(b, "tagName")) {
    Val v = rv(gen(x, s, NULL)); Type *t = v.t; char *tv;
    if (t->k == TY_UNION) { tv = load(t->ct->tag, addp(addr_of(v), union_tag_off(t))); t = t->ct->tag; }
    else tv = opnd(v);
    if (qc(t) == 'l') { char *w = tmp(); emit("%s =w copy %s", w, tv); tv = w; }
    char *fnm = tagname_fn(t), *r = tmp(); emit("%s =l call $%s(w %s)", r, fnm, tv);
    return V(slice_of(t_u8, 1), r);
  }

  if (strstr(b, "WithOverflow")) {
    Val a = rv(gen(x, s, NULL)), c2 = rv(gen(y, s, NULL)); int shl = b[0] == 's' && b[1] == 'h';
    Type *t = shl ? a.t : peer(a, c2); if (t->k == TY_CINT) t = t_i64;
    a = coerce(a, t); if (!shl) c2 = coerce(c2, t);
    int sg = t->sign, bits = t->bits; char *A = opnd(a), *B2 = opnd(c2), *res, *ov = tmp();
    if (bits <= 32) {
      char *xa = tmp(), *xb = tmp(), *r = tmp(); emit("%s =l %s %s", xa, sg ? "extsw" : "extuw", A); emit("%s =l %s %s", xb, (sg && !shl) ? "extsw" : "extuw", B2);
      emit("%s =l %s %s, %s", r, b[0] == 'a' ? "add" : shl ? "shl" : b[0] == 's' ? "sub" : "mul", xa, xb);
      char *tw = tmp(); emit("%s =w copy %s", tw, r); res = norm(tw, t); char *e = tmp(); emit("%s =l %s %s", e, sg ? "extsw" : "extuw", res);
      emit("%s =w cnel %s, %s", ov, e, r);
    } else {
      char *r = tmp();
      if (b[0] == 'a') { emit("%s =l add %s, %s", r, A, B2); if (sg) { char *p1 = tmp(), *p2 = tmp(), *p3 = tmp(); emit("%s =l xor %s, %s", p1, A, r); emit("%s =l xor %s, %s", p2, B2, r); emit("%s =l and %s, %s", p3, p1, p2); emit("%s =w csltl %s, 0", ov, p3); } else emit("%s =w cultl %s, %s", ov, r, A); }
      else if (shl) { emit("%s =l shl %s, %s", r, A, B2); char *bk = tmp(); emit("%s =l %s %s, %s", bk, sg ? "sar" : "shr", r, B2); emit("%s =w cnel %s, %s", ov, bk, A); }
      else if (b[0] == 's') { emit("%s =l sub %s, %s", r, A, B2); if (sg) { char *p1 = tmp(), *p2 = tmp(), *p3 = tmp(); emit("%s =l xor %s, %s", p1, A, B2); emit("%s =l xor %s, %s", p2, A, r); emit("%s =l and %s, %s", p3, p1, p2); emit("%s =w csltl %s, 0", ov, p3); } else emit("%s =w cultl %s, %s", ov, A, B2); }
      else {
        emit("%s =l mul %s, %s", r, A, B2); char *sl = slot(t_u8), *lz = newl(), *lnz = newl(), *le = newl(), *z = tmp();
        store(t_u8, "0", sl); emit("%s =w ceql %s, 0", z, A); br(z, lz, lnz);
        label(lnz); char *q = tmp(), *d = tmp(); emit("%s =l %s %s, %s", q, sg ? "div" : "udiv", r, A); emit("%s =w cnel %s, %s", d, q, B2);
        if (sg) { char *m1 = tmp(), *m2 = tmp(), *m3 = tmp(), *m4 = tmp(); emit("%s =w ceql %s, -1", m1, A); emit("%s =w ceql %s, -9223372036854775808", m2, B2); emit("%s =w and %s, %s", m3, m1, m2); emit("%s =w or %s, %s", m4, d, m3); d = m4; }
        store(t_u8, d, sl); jmp(le); label(lz); jmp(le); label(le); ov = load(t_u8, sl);
      }
      res = r;
    }
    Vec names = {0}, types = {0}; vpush(&names, "0"); vpush(&names, "1"); vpush(&types, t); vpush(&types, t_u1);
    Type *tt = mk_anon_struct(&names, &types, 1); char *sl = slot(tt);
    store(t, res, sl); store(t_u8, ov, addp(sl, ((Field *)tt->ct->fields.a[1])->off)); return V(tt, sl);
  }
  if (!strcmp(b, "byteSwap") || !strcmp(b, "bitReverse")) {
    Val a = rv(gen(x, s, ex)); Type *t = a.t; if (t->k == TY_CINT) t = ex ? ex : t_i64; a = coerce(a, t);
    char c = qc(t); int bits = t->bits; char *A = opnd(a), *acc = "0"; int step = b[1] == 'y' ? 8 : 1; unsigned long long mk = step == 8 ? 0xff : 1;
    for (int i = 0; i < bits / step; i++) {
      char *p = tmp(), *q = tmp(), *r = tmp(), *o = tmp();
      emit("%s =%c shr %s, %d", p, c, A, i * step); emit("%s =%c and %s, %llu", q, c, p, mk);
      emit("%s =%c shl %s, %d", r, c, q, bits - step - i * step); emit("%s =%c or %s, %s", o, c, acc, r); acc = o;
    }
    return V(t, norm(acc, t));
  }
  if (!strcmp(b, "fieldParentPtr")) {
    CVal nm; if (!ceval(x, s, &nm) || nm.k != CV_STR) die("@fieldParentPtr field name must be comptime");
    if (ex && ex->k == TY_OPT) ex = ex->elem;
    if (!ex || ex->k != TY_PTR) die("%s:%d: @fieldParentPtr needs a pointer result type", n->tok->file, n->tok->line);
    char nb[256]; snprintf(nb, sizeof nb, "%.*s", nm.slen, nm.s); layout(ex->elem->ct); Field *f = find_field(ex->elem->ct, nb);
    if (!f) die("no field %s", nb); Val p = rv(gen(y, s, NULL)); char *r = tmp(); emit("%s =l sub %s, %d", r, opnd(p), f->off); return V(ex, r);
  }
  if (!strncmp(b, "atomic", 6) || !strncmp(b, "cmpxchg", 7)) {
    Type *t0 = eval_type(x, s); Val p = rv(gen(y, s, ptr_to(t0, 0))); char *P = opnd(p);
    Type *t = is_packed(t0) ? int_type(tsize(t0) * 8, 0) : t0;
    #define PKIN(v_) (t != t0 ? V(t, load(t, addr_of(coerce(v_, t0)))) : coerce(v_, t))
    #define PKOUT(v_) (t != t0 ? ({ Val o_ = (v_); char *sl_ = slot(t0); store(t, opnd(o_), sl_); V(t0, sl_); }) : (v_))
    if (!strcmp(b, "atomicLoad")) return PKOUT(V(t, load(t, P)));
    if (!strcmp(b, "atomicStore")) { Val v = PKIN(gen(n->list.a[2], s, t0)); store(t, opnd(v), P); return VOIDV(); }
    if (!strcmp(b, "atomicRmw")) {
      CVal op; if (!ceval_ex(n->list.a[2], s, bt_type_pub("AtomicRmwOp"), &op)) die("@atomicRmw op must be comptime");
      const char *on = NULL; Container *rc = bt_type_pub("AtomicRmwOp")->ct; layout(rc); if (op.k == CV_ENUMLIT) on = op.s; else for (int i = 0; i < rc->fields.n; i++) { Field *f = rc->fields.a[i]; if (f->val == (int64_t)op.i) on = f->name; }
      Val v = PKIN(gen(n->list.a[3], s, t0)); Val old = V(t, load(t, P)); Val nv;
      if (!strcmp(on, "Xchg")) nv = v;
      else if (!strcmp(on, "Max") || !strcmp(on, "Min")) nv = sel2(gen_cmp(on[1] == 'a' ? ">" : "<", v, old), v, old, t);
      else if (!strcmp(on, "Nand")) { Val a2 = gen_arith("&", old, v); char *r = tmp(); emit("%s =%c xor %s, -1", r, qc(t), opnd(a2)); nv = V(t, norm(r, t)); }
      else nv = coerce(gen_arith(!strcmp(on, "Add") ? "+%" : !strcmp(on, "Sub") ? "-%" : !strcmp(on, "And") ? "&" : !strcmp(on, "Or") ? "|" : "^", old, v), t);
      store(t, opnd(nv), P); return PKOUT(old);
    }
    if (!strncmp(b, "cmpxchg", 7)) {
      Val e = PKIN(gen(n->list.a[2], s, t0)), nv = PKIN(gen(n->list.a[3], s, t0)); Type *ot = opt_of(t0);
      Val cur = V(t, load(t, P)); Val eq = gen_cmp("==", cur, e); char *sl = slot(ot), *l1 = newl(), *l2 = newl(), *le = newl();
      br(opnd(eq), l1, l2);
      label(l1); store(t, opnd(nv), P); put(coerce(CK(cv_null_pub()), ot), ot, sl); jmp(le);
      label(l2); put(coerce(PKOUT(cur), ot), ot, sl); jmp(le); label(le);
      return is_aggr(ot) ? V(ot, sl) : V(ot, load(ot, sl));
    }
  }
  if ((!strcmp(b, "memcpy") || !strcmp(b, "memmove") || !strcmp(b, "memset")) && ct_try_store(x, n, s)) return VOIDV();
  if (!strcmp(b, "memcpy") || !strcmp(b, "memmove")) {
    Val d = rv(gen(x, s, NULL)), sv = rv(gen(y, s, NULL)); char *dp, *sp, *len = NULL; Type *et;
    if (d.t->k == TY_SLICE) { dp = load(t_u64, addr_of(d)); len = load(t_u64, addp(addr_of(d), 8)); et = d.t->elem; }
    else if (d.t->k == TY_PTR && d.t->elem->k == TY_ARRAY) { dp = opnd(d); len = fmt("%lld", (long long)d.t->elem->len); et = d.t->elem->elem; }
    else { dp = opnd(d); et = d.t->elem; }
    if (sv.t->k == TY_SLICE) { sp = load(t_u64, addr_of(sv)); if (!len) len = load(t_u64, addp(addr_of(sv), 8)); }
    else if (sv.ck && sv.cv.k == CV_STR) { sp = mat(sv); if (!len) len = fmt("%d", sv.cv.slen); }
    else if (sv.t->k == TY_PTR && sv.t->elem->k == TY_ARRAY) { sp = opnd(sv); if (!len) len = fmt("%lld", (long long)sv.t->elem->len); }
    else sp = opnd(sv);
    char *nb = tmp(); emit("%s =l mul %s, %d", nb, len, tsize(et)); emit("call $memmove(l %s, l %s, l %s)", dp, sp, nb);
    return VOIDV();
  }
  if (!strcmp(b, "memset")) {
    Val d = rv(gen(x, s, NULL)); char *dp, *len; Type *et;
    if (d.t->k == TY_SLICE) { dp = load(t_u64, addr_of(d)); len = load(t_u64, addp(addr_of(d), 8)); et = d.t->elem; }
    else { dp = opnd(d); len = fmt("%lld", (long long)d.t->elem->len); et = d.t->elem->elem; }
    Val v = coerce(gen(y, s, et), et);
    if (v.ck && v.cv.k == CV_UNDEF) return VOIDV();
    if (tsize(et) == 1) { char *w = opnd(v); emit("call $memset(l %s, w %s, l %s)", dp, w, len); return VOIDV(); }
    char *is = slot(t_usize), *lc = newl(), *lb = newl(), *le = newl(); store(t_u64, "0", is); jmp(lc); label(lc);
    char *i = load(t_u64, is), *c2 = tmp(); emit("%s =w cultl %s, %s", c2, i, len); br(c2, lb, le); label(lb);
    char *o = tmp(), *a = tmp(); emit("%s =l mul %s, %d", o, i, tsize(et)); emit("%s =l add %s, %s", a, dp, o); put(v, et, a);
    char *i2 = tmp(); emit("%s =l add %s, 1", i2, i); store(t_u64, i2, is); jmp(lc); label(le);
    return VOIDV();
  }
  if (!strcmp(b, "min") || !strcmp(b, "max")) return gen_minmax(n, s, ex, b[1] == 'i');
  if (!strcmp(b, "divTrunc") || !strcmp(b, "divExact") || !strcmp(b, "rem")) return gen_arith(b[0] == 'r' ? "%" : "/", gen(x, s, ex), gen(y, s, ex));
  if (!strcmp(b, "divFloor") || !strcmp(b, "mod")) {
    Val a = rv(gen(x, s, ex)), d = rv(gen(y, s, ex)); Type *t = peer(a, d); if (t->k == TY_CINT) t = ex ? ex : t_i64;
    a = coerce(a, t); d = coerce(d, t);
    if (is_bigf(t)) return V(t, bigf_op(b[0] == 'd' ? 24 : 5, t, opnd(a), opnd(d)));
    if (is_float(t)) { char c = qc(t), *q = tmp(), *f = tmp(); emit("%s =%c div %s, %s", q, c, opnd(a), opnd(d));
      emit("%s =%c call $%s(%c %s)", f, c, c == 's' ? "floorf" : "floor", c, q); if (b[0] == 'd') return V(t, f);
      char *m = tmp(), *r = tmp(); emit("%s =%c mul %s, %s", m, c, f, opnd(d)); emit("%s =%c sub %s, %s", r, c, opnd(a), m); return V(t, r); }
    if (!t->sign) return gen_arith(b[0] == 'm' ? "%" : "/", a, d);
    char cl = qc(t), *A = opnd(a), *D = opnd(d), *q = tmp(), *r = tmp(), *nz = tmp(), *x1 = tmp(), *neg = tmp(), *adj = tmp(), *res = tmp(), *ext = tmp();
    emit("%s =%c div %s, %s", q, cl, A, D); emit("%s =%c rem %s, %s", r, cl, A, D);
    emit("%s =w cne%c %s, 0", nz, cl, r); emit("%s =%c xor %s, %s", x1, cl, r, D); emit("%s =w cslt%c %s, 0", neg, cl, x1);
    emit("%s =w and %s, %s", adj, nz, neg);
    if (cl == 'l') emit("%s =l extuw %s", ext, adj); else emit("%s =w copy %s", ext, adj);
    if (b[0] == 'm') { char *m = tmp(); emit("%s =%c mul %s, %s", m, cl, ext, D); emit("%s =%c add %s, %s", res, cl, r, m); }
    else emit("%s =%c sub %s, %s", res, cl, q, ext);
    return V(t, res);
  }
  if (!strcmp(b, "shlExact") || !strcmp(b, "shrExact")) return gen_arith(b[1] == 'h' && b[2] == 'l' ? "<<" : ">>", gen(x, s, ex), gen(y, s, NULL));
  if (!strcmp(b, "abs")) {
    Val a = rv(gen(x, s, NULL)); Type *t = a.t;
    if (is_bigf(t)) return V(t, bigf_op(9, t, opnd(a), NULL));
    if (t->k == TY_FLOAT) { char c = qc(t), *r = tmp(); emit("%s =%c call $fabs%s(%c %s)", r, c, c == 's' ? "f" : "", c, opnd(a)); return V(t, r); }
    if (t->k == TY_INT && !t->sign) return a;
    if (is_vec(t)) { char *sl = slot(t); Val av = V(t, addr_of(a)); Type *et = t->elem; Type *ut = et->k == TY_INT ? int_type(et->bits, 0) : et;
      for (int64_t i = 0; i < t->len; i++) { Val e = vel(av, i); char *r;
        if (et->k == TY_FLOAT) { char c = qc(et); r = tmp(); emit("%s =%c call $fabs%s(%c %s)", r, c, c == 's' ? "f" : "", c, opnd(e)); }
        else if (!et->sign) r = opnd(e);
        else { char c = qc(et), *o = opnd(e), *ng = tmp(), *sg = tmp(), *x1 = tmp(); r = tmp(); emit("%s =%c sar %s, %d", sg, c, o, c == 'w' ? 31 : 63); emit("%s =%c xor %s, %s", x1, c, o, sg); emit("%s =%c sub %s, %s", ng, c, x1, sg); r = ng; }
        store(et, r, addp(sl, i * tsize(et))); }
      return V(vec_of(ut, t->len), sl); }
    if (is_wide(t)) { Type *ut = int_type(t->bits, 0); if (!t->sign) return V(ut, a.op);
      char *lo = wlo(a), *hi = whi(a), *sg = tmp(), *xl = tmp(), *xh = tmp();
      emit("%s =l sar %s, 63", sg, hi); emit("%s =l xor %s, %s", xl, lo, sg); emit("%s =l xor %s, %s", xh, hi, sg);
      Val xv = w_from_parts(ut, xl, xh), sv = w_from_parts(ut, sg, sg); return w_arith("-", ut, xv, sv); }
    char cl = qc(t), *o = opnd(a), *ng = tmp(), *c2 = tmp(), *sl = slot(t), *l1 = newl(), *l2 = newl();
    store(t, o, sl); emit("%s =w cslt%c %s, 0", c2, cl, o); br(c2, l1, l2); label(l1); emit("%s =%c neg %s", ng, cl, o); store(t, ng, sl); jmp(l2); label(l2);
    return V(int_type(t->bits, 0), load(t, sl));
  }
  if (!strcmp(b, "panic")) {
    Val m = coerce(gen(x, s, slice_of(t_u8, 1)), slice_of(t_u8, 1)); char *a = addr_of(m);
    char *p = load(t_u64, a), *l = load(t_u64, addp(a, 8)); emit("call $zb.panic(l %s, l %s)", p, l); emit("hlt"); term = 1; return NORET();
  }
  if (!strcmp(b, "trap") || !strcmp(b, "breakpoint")) { emit("hlt"); term = 1; return NORET(); }
  if (!strcmp(b, "field")) { Val base = gen(x, s, NULL); CVal nm; char *nms = ceval_force(y, s, &nm) ? cv_cstr(&nm, NULL) : NULL; if (!nms) die("%s:%d: @field name must be comptime-known string (at %s)", n->tok->file, n->tok->line, ct_fail_loc()); return gen_member(base, nms, n); }
  if (!strcmp(b, "unionInit")) {
    Type *t = eval_type(x, s); CVal nm; char *nms = ceval_force(y, s, &nm) ? cv_cstr(&nm, NULL) : NULL; if (!nms) die("%s:%d: @unionInit field name must be comptime-known (at %s)", n->tok->file, n->tok->line, ct_fail_loc());
    Field *f = find_field(t->ct, nms); if (!f) die("%s:%d: no field '%s' in union %s", n->tok->file, n->tok->line, nms, tname(t)); char *sl = slot(t);
    Val v = coerce(gen(n->list.a[2], s, f->t), f->t); put(v, f->t, sl);
    if (t->ct->tagged) store(t->ct->tag, fmt("%lld", (long long)f->val), addp(sl, union_tag_off(t)));
    return V(t, sl);
  }
  if (!strcmp(b, "setEvalBranchQuota") || !strcmp(b, "setRuntimeSafety") || !strcmp(b, "branchHint") || !strcmp(b, "setFloatMode") || !strcmp(b, "disableInstrumentation")) return VOIDV();
  if (!strcmp(b, "errorReturnTrace")) { CVal z = {0}; z.k = CV_NULL; return CK(z); }
  if (!strcmp(b, "returnAddress") || !strcmp(b, "frameAddress")) return V(t_usize, "0");
  if (!strcmp(b, "clz") || !strcmp(b, "ctz") || !strcmp(b, "popCount")) {
    Val a = rv(gen(x, s, NULL)); Type *t = a.t;
    if (is_wide(t)) {
      char *ad = addr_of(a), *lo = load(t_u64, ad), *hi = load(t_u64, addp(ad, 8)), *res = slot(t_u64);
      if (b[0] == 'p') { char *p1 = tmp(), *p2 = tmp(), *r = tmp(), *rl = tmp(); emit("%s =w call $__popcountdi2(l %s)", p1, lo); emit("%s =w call $__popcountdi2(l %s)", p2, hi); emit("%s =w add %s, %s", r, p1, p2); emit("%s =l extuw %s", rl, r); return int_conv(V(t_u64, rl), int_type(8, 0), 1); }
      int clz = b[1] == 'l'; char *first = clz ? hi : lo, *second = clz ? lo : hi;
      char *z1 = tmp(), *z2 = tmp(), *l1 = newl(), *l2 = newl(), *l3 = newl(), *l4 = newl(), *le = newl();
      int adj = clz ? 128 - t->bits : 0; const char *fn = clz ? "__clzdi2" : "__ctzdi2";
      emit("%s =w cnel %s, 0", z1, first); br(z1, l1, l2);
      label(l1); { char *r = tmp(), *r2 = tmp(), *rl = tmp(); emit("%s =w call $%s(l %s)", r, fn, first); emit("%s =w sub %s, %d", r2, r, adj); emit("%s =l extuw %s", rl, r2); store(t_u64, rl, res); jmp(le); }
      label(l2); emit("%s =w cnel %s, 0", z2, second); br(z2, l3, l4);
      label(l3); { char *r = tmp(), *r2 = tmp(), *rl = tmp(); emit("%s =w call $%s(l %s)", r, fn, second); emit("%s =w add %s, %d", r2, r, 64 - adj); emit("%s =l extuw %s", rl, r2); store(t_u64, rl, res); jmp(le); }
      label(l4); store(t_u64, fmt("%d", t->bits), res); jmp(le); label(le);
      return int_conv(V(t_u64, load(t_u64, res)), int_type(8, 0), 1);
    }
    char *o = opnd(a), *w = o;
    if (qc(t) == 'w') { w = tmp(); emit("%s =l extuw %s", w, o); }
    char *r = tmp(), *res = slot(t_u64);
    if (b[0] == 'p') { emit("%s =w call $__popcountdi2(l %s)", r, w); return V(int_type(7, 0), r); }
    char *z = tmp(), *lz = newl(), *lnz = newl(), *le = newl(); emit("%s =w ceql %s, 0", z, w); br(z, lz, lnz);
    label(lz); store(t_u64, fmt("%d", t->bits), res); jmp(le);
    label(lnz); emit("%s =w call $%s(l %s)", r, b[1] == 'l' ? "__clzdi2" : "__ctzdi2", w);
    if (b[1] == 'l' && t->bits < 64) { char *r2 = tmp(); emit("%s =w sub %s, %d", r2, r, 64 - t->bits); r = r2; }
    char *rl = tmp(); emit("%s =l extuw %s", rl, r); store(t_u64, rl, res); jmp(le); label(le);
    return int_conv(V(t_u64, load(t_u64, res)), int_type(8, 0), 1);
  }
  { static const char *tyb[] = { "Int", "Vector", "Struct", "Union", "Enum", "Pointer", "Fn", "Tuple", "Type", "Float", "Array", "Optional", "ErrorUnion", "ErrorSet", "Opaque", NULL };
    for (int i = 0; tyb[i]; i++) if (!strcmp(b, tyb[i]) && ceval_force(n, s, &c)) return CK(c); } /* type constructors: args are comptime */
  die("%s:%d: builtin @%s not supported", n->tok->file, n->tok->line, b);
}

/* ---------- control flow ---------- */
static Loop *find_loop(char *label, int forcont) {
  for (Loop *l = loops; l; l = l->up) {
    if (label) { if (l->label && !strcmp(l->label, label)) return l; }
    else if (l->kind == 0) return l;
  }
  die("break/continue target not found"); (void)forcont;
}
static Node *collect_node;
static int ex_partial(Type *t) { /* tuple hint with untyped (anytype) fields: peer-resolve instead */
  if (!t || !is_tuple_type(t)) return 0; layout(t->ct);
  for (int i = 0; i < t->ct->fields.n; i++) if (((Field *)t->ct->fields.a[i])->t->k == TY_ANYTYPE) return 1; return 0; }
static int type_incomplete(Type *t) {
  if (!t) return 1;
  if (t->k == TY_NULL || t->k == TY_UNDEF || t->k == TY_ENUMLIT || t->k == TY_NORET || t->k == TY_CINT || t->k == TY_CFLOAT) return 1;
  if (t->k == TY_TUPLE || (t->k == TY_STRUCT && is_anon(t))) { layout(t->ct); for (int i = 0; i < t->ct->fields.n; i++) if (type_incomplete(((Field *)t->ct->fields.a[i])->t)) return 1; }
  return 0;
}
static Val gen_block(Node *n, Scope *s, Type *ex) {
  Scope *bs = new_scope(s, NULL); int base = defers.n;
  if (n->label && !ex && !in_typeof) { /* peer-resolve the types of all breaks first */
    Node *sc = collect_node; collect_node = n; Type *pt = typeof_impl(n, s); collect_node = sc;
    if (pt && !type_incomplete(pt) && !type_is_ctonly(pt) && pt->k != TY_VOID) ex = pt;
  }
  Loop L; memset(&L, 0, sizeof L); Res R; memset(&R, 0, sizeof R); R.ex = ex;
  if (n == collect_node && in_typeof) { R.collect = 1; collect_node = NULL; }
  else if (in_typeof && ex_partial(ex)) R.collect = 1;
  else if (n->label && !ex && in_typeof) R.collect = 1;
  if (n->label) { L.label = n->label; L.brk = newl(); L.res = &R; L.dbase = base; L.kind = 1; L.up = loops; loops = &L; }
  for (int i = 0; i < n->list.n; i++) {
    Node *st = n->list.a[i];
    gen(st, bs, NULL);
    if (term) break; /* rest of the block is unreachable (e.g. after a comptime-pruned branch) */
  }
  int fell = !term;
  if (!term) run_defers(base, NULL);
  defers.n = base;
  if (n->label) {
    loops = L.up; if (fell && !term) { if (!R.t) { R.t = t_void; } R.has = 1; jmp(L.brk); }
    label(L.brk); return res_get(&R);
  }
  if (!fell) return NORET();
  return VOIDV();
}
static void cap_bind(Scope *s, char *name, int ref, Val payload) {
  if (!name || !strcmp(name, "_")) return;
  if (ref) { bind_val(s, name, V(ptr_to(payload.t, 0), payload.op)); return; }
  bind_val(s, name, rv(payload));
}
static Type *typeof_impl(Node *n, Scope *s);
static Type *peer_t(Type *a, Type *b) {
  if (!a) return b; if (!b) return a;
  if (a == b) return a;
  if (a->k == TY_NORET) return b; if (b->k == TY_NORET) return a;
  if (a->k == TY_ENUMLIT && b->k == TY_ENUMLIT) return a;
  if (a->k == TY_ENUMLIT && (b->k == TY_ENUM || b->k == TY_UNION || (b->k == TY_OPT && (b->elem->k == TY_ENUM || b->elem->k == TY_UNION)))) return b;
  if (b->k == TY_ENUMLIT && (a->k == TY_ENUM || a->k == TY_UNION || (a->k == TY_OPT && (a->elem->k == TY_ENUM || a->elem->k == TY_UNION)))) return a;
  if (a->k == TY_ERRSET && b->k == TY_ERRSET) return a;
  if (a->k == TY_ERRSET) return b->k == TY_ERRU ? b : erru_of(b);
  if (b->k == TY_ERRSET) return a->k == TY_ERRU ? a : erru_of(a);
  if (a->k == TY_ERRU || b->k == TY_ERRU) { Type *e = peer_t(a->k == TY_ERRU ? a->elem : a, b->k == TY_ERRU ? b->elem : b); return e ? erru_of(e) : NULL; }
  if (a->k == TY_CINT && (b->k == TY_INT)) return b; if (b->k == TY_CINT && a->k == TY_INT) return a;
  if (a->k == TY_INT && b->k == TY_INT) {
    if (a->sign == b->sign) return a->bits >= b->bits ? a : b;
    Type *sg = a->sign ? a : b, *us = a->sign ? b : a; return sg->bits > us->bits ? sg : int_type(us->bits + 1, 1);
  }
  if (a->k == TY_NULL) return b->k == TY_OPT ? b : opt_of(b); if (b->k == TY_NULL) return a->k == TY_OPT ? a : opt_of(a);
  if (a->k == TY_OPT && a->elem == b) return a; if (b->k == TY_OPT && b->elem == a) return b;
  if (a->k == TY_ERRU && a->elem == b) return a; if (b->k == TY_ERRU && b->elem == a) return b;
  if (a->k == TY_CFLOAT && b->k == TY_FLOAT) return b; if (b->k == TY_CFLOAT && a->k == TY_FLOAT) return a;
  if (a->k == TY_CINT && is_float(b)) return b; if (b->k == TY_CINT && is_float(a)) return a;
  if (a->k == TY_FLOAT && b->k == TY_FLOAT) return a->bits >= b->bits ? a : b;
  if (a->k == TY_UNDEF) return b; if (b->k == TY_UNDEF) return a;
  { /* pointers to arrays of differing lengths / slices with the same element type -> slice */
    int pa = a->k == TY_PTR && a->elem->k == TY_ARRAY, pb = b->k == TY_PTR && b->elem->k == TY_ARRAY;
    Type *ea = pa ? a->elem->elem : a->k == TY_SLICE ? a->elem : NULL, *eb = pb ? b->elem->elem : b->k == TY_SLICE ? b->elem : NULL;
    if (ea && ea == eb && (pa || pb || (!a->hassent && !b->hassent))) return slice_of(ea, a->isconst || b->isconst);
  }
  if (a->k == TY_OPT && b->k == TY_OPT) { Type *e = peer_t(a->elem, b->elem); return e ? opt_of(e) : NULL; }
  if (a->k == TY_OPT) { Type *e = peer_t(a->elem, b); return e ? opt_of(e) : NULL; }
  if (b->k == TY_OPT) { Type *e = peer_t(a, b->elem); return e ? opt_of(e) : NULL; }
  if (is_tuple_type(a) && is_tuple_type(b) && (is_anon(a) || a->k == TY_TUPLE || is_anon(b) || b->k == TY_TUPLE)) {
    layout(a->ct); layout(b->ct); if (a->ct->fields.n != b->ct->fields.n) return NULL;
    Vec names = {0}, types = {0};
    for (int i = 0; i < a->ct->fields.n; i++) { Type *e = peer_t(((Field *)a->ct->fields.a[i])->t, ((Field *)b->ct->fields.a[i])->t); if (!e) return NULL; vpush(&names, fmt("%d", i)); vpush(&types, e); }
    return mk_anon_struct(&names, &types, 1);
  }
  return NULL;
}
static Val gen_if(Node *n, Scope *s, Type *ex) {
  CVal c;
  if (!n->cap && ceval(n->a, s, &c) && c.k == CV_BOOL) {
    if (c.i) return gen(n->b, s, ex);
    return n->c ? gen(n->c, s, ex) : VOIDV();
  }
  Res R; memset(&R, 0, sizeof R); R.ex = ex;
  if (!ex && n->c && !in_typeof) { Type *t1 = typeof_impl(n->b, s), *t2 = typeof_impl(n->c, s), *p = peer_t(t1, t2); if (p && p != t1 && p->k != TY_CINT) R.ex = p; }
  if (!ex && n->c && in_typeof) R.collect = 1;
  Val cv0 = n->cap ? (Val){0} : gen(n->a, s, t_bool);
  if (!n->cap && cv0.ck && cv0.cv.k == CV_BOOL) {
    if (cv0.cv.i) return gen(n->b, s, ex);
    return n->c ? gen(n->c, s, ex) : VOIDV();
  }
  char *lt = newl(), *lf = newl(), *lx = newl();
  Scope *ts = new_scope(s, NULL), *es = new_scope(s, NULL);
  Val cv = coerce(cv0, t_bool); br(opnd(cv), lt, lf); label(lt);
  Val tv = gen(n->b, ts, n->c ? R.ex : NULL); res_put(&R, n->c || tv.t->k == TY_NORET ? tv : VOIDV()); jmp(lx);
  label(lf);
  if (n->c) { Val ev = gen(n->c, es, R.ex ? R.ex : R.collect ? NULL : R.t); res_put(&R, ev); } else res_put(&R, VOIDV());
  jmp(lx); label(lx);
  return res_get(&R);
}
static void if_peer(Res *R, Node *n, Scope *s, Type *ex) {
  if (ex || !n->c) return;
  if (in_typeof) { R->collect = 1; return; }
  Type *p = typeof_impl(n, s);
  if (p && p->k != TY_CINT && p->k != TY_NORET && p->k != TY_NULL && p->k != TY_ENUMLIT && p->k != TY_UNDEF && p->k != TY_VOID) R->ex = p;
}
static Val gen_if_erru(Node *n, Scope *s, Type *ex, Val cv) {
  Res R; memset(&R, 0, sizeof R); R.ex = ex; if_peer(&R, n, s, ex);
  char *lt = newl(), *lf = newl(), *lx = newl();
  Scope *ts = new_scope(s, NULL), *es = new_scope(s, NULL);
  char *a = addr_of(cv); char *e = load(t_u16, a); br(e, lf, lt);
  label(lt); if (n->cap && cv.t->elem != t_void) cap_bind(ts, n->cap, n->capref, LV(cv.t->elem, addp(a, erru_off(cv.t))));
  else if (n->cap && strcmp(n->cap, "_")) bind_cval(ts, n->cap, cv_void());
  Val tv = gen(n->b, ts, n->c ? ex : NULL); res_put(&R, n->c || tv.t->k == TY_NORET ? tv : VOIDV()); jmp(lx);
  label(lf); if (n->cap2) bind_val(es, n->cap2, V(t_errset, e));
  if (n->c) { Val ev = gen(n->c, es, ex ? ex : R.collect ? NULL : R.t); res_put(&R, ev); } else res_put(&R, VOIDV());
  jmp(lx); label(lx); return res_get(&R);
}
static Type *loop_peer(Node *n, Scope *s);
static Val gen_while(Node *n, Scope *s, Type *ex) {
  int always = 0, skip = 0;
  if (!ex && n->c && !in_typeof) ex = loop_peer(n, s);
  Loop L; memset(&L, 0, sizeof L); Res R; memset(&R, 0, sizeof R); R.ex = ex;
  if (n == collect_node && in_typeof) { R.collect = 1; collect_node = NULL; }
  else if (in_typeof && ex_partial(ex)) R.collect = 1;
  char *lc = newl(), *lb = newl(), *lk = newl(), *le = newl(), *lx = newl();
  L.label = n->label; L.brk = lx; L.cont = lk; L.res = &R; L.dbase = defers.n; L.kind = 0;
  jmp(lc); label(lc);
  Scope *bs = new_scope(s, NULL), *es = new_scope(s, NULL);
  if (n->cap) {
    Val cv = gen(n->a, s, NULL);
    if (cv.t->k == TY_OPT && cv.t->elem->k == TY_NORET) { jmp(le); label(lb); skip = 1; } /* ?noreturn: always null, body unanalyzed */
    else if (cv.t->k == TY_OPT) {
      char *pv = opt_is_ptr(cv.t) ? opnd(cv) : NULL;
      if (pv) { char *h = tmp(); emit("%s =w cnel %s, 0", h, pv); br(h, lb, le); } else br(opt_has(cv), lb, le);
      label(lb); cap_bind(bs, n->cap, n->capref, opt_payload(cv, pv));
    } else {
      char *a = addr_of(cv), *e = load(t_u16, a); br(e, le, lb);
      label(lb); if (cv.t->elem != t_void) cap_bind(bs, n->cap, n->capref, LV(cv.t->elem, addp(a, erru_off(cv.t)))); else if (strcmp(n->cap, "_")) bind_cval(bs, n->cap, cv_void());
      if (n->cap2) bind_val(es, n->cap2, V(t_errset, e));
    }
  } else {
    Val cv = coerce(gen(n->a, s, t_bool), t_bool);
    if (cv.ck) { jmp(cv.cv.i ? lb : le); if (cv.cv.i) always = 1; } else br(opnd(cv), lb, le);
    label(lb);
  }
  L.up = loops; loops = &L;
  if (!skip) gen(n->b, bs, NULL);
  loops = L.up;
  jmp(lk); label(lk); if (n->d && !skip) gen(n->d, bs, NULL); jmp(lc);
  label(le);
  if (n->c) { Val ev = gen(n->c, es, ex); res_put(&R, ev); }
  else if ((R.has || ex) && !always) res_put(&R, VOIDV());
  else if (always) { emit("hlt"); term = 1; }
  jmp(lx); label(lx);
  if (always && !L.brk_used) { emit("hlt"); term = 1; return NORET(); }
  if (!n->c && !R.has) return VOIDV();
  return res_get(&R);
}
static Val gen_inline_while(Node *n, Scope *s, Type *ex) {
  Loop L; memset(&L, 0, sizeof L); Res R; memset(&R, 0, sizeof R); R.ex = ex;
  char *lx = newl(); int stopped = 0, iters = 0;
  L.label = n->label; L.brk = lx; L.res = &R; L.dbase = defers.n; L.kind = 0;
  for (;;) {
    if (term) { stopped = 1; break; }
    Scope *bs = new_scope(s, NULL); CVal c;
    if (!ceval_force(n->a, s, &c)) die("%s:%d: inline while condition is not comptime-known (at %s)", n->tok->file, n->tok->line, ct_fail_loc());
    if (n->cap) { if (c.k == CV_NULL || c.k == CV_ERR) break; bind_cval(bs, n->cap, c); }
    else { if (c.k != CV_BOOL) die("%s:%d: inline while condition is not a bool", n->tok->file, n->tok->line); if (!c.i) break; }
    char *lk = newl(); L.cont = lk; L.cont_used = 0;
    L.up = loops; loops = &L; gen(n->b, bs, NULL); loops = L.up;
    if (term && !L.cont_used) { stopped = 1; break; }
    jmp(lk); label(lk);
    if (n->d) gen(n->d, bs, NULL);
    if (++iters > 1000000) die("%s:%d: inline while: too many iterations", n->tok->file, n->tok->line);
  }
  if (!stopped && n->c) res_put(&R, gen(n->c, s, ex));
  int dead = term && !L.brk_used; /* the unrolled code ends in return/noreturn */
  jmp(lx); label(lx);
  if (dead) { emit("hlt"); term = 1; return NORET(); }
  if (!R.has) return VOIDV();
  return res_get(&R);
}
static Val gen_inline_for(Node *n, Scope *s, Type *ex) {
  int ni = n->list.n; CVal *cvs = xalloc(sizeof(CVal) * ni); Val *rvs = xalloc(sizeof(Val) * ni);
  char *kind = xalloc(ni); int64_t *start = xalloc(sizeof(int64_t) * ni); int64_t len = -1;
  for (int i = 0; i < ni; i++) {
    Node *e = n->list.a[i]; int64_t l = -1;
    if (e->k == N_RANGE) {
      CVal lo, hi;
      if (!e->b && !ceval(e->a, s, &lo)) { kind[i] = 3; rvs[i] = coerce(rv(gen(e->a, s, t_usize)), t_usize); char *sl = slot(t_usize); store(t_u64, opnd(rvs[i]), sl); rvs[i] = V(t_usize, sl); continue; } /* runtime open range start */
      if (!ceval_force(e->a, s, &lo)) die("%s:%d: inline for range must be comptime-known", e->tok->file, e->tok->line);
      kind[i] = 2; start[i] = (int64_t)lo.i;
      if (e->b) { if (!ceval_force(e->b, s, &hi)) die("%s:%d: inline for range must be comptime-known", e->tok->file, e->tok->line); l = (int64_t)(hi.i - lo.i); }
    } else {
      CVal c;
      if (ceval(e, s, &c) && c.k != CV_UNDEF) {
        kind[i] = 1; cvs[i] = c;
        if (!cv_len(&c, &l)) { Type *t = cv_typeof(&c); if (t->k == TY_PTR && t->elem->k == TY_ARRAY) l = t->elem->len; else die("%s:%d: cannot iterate over %s", e->tok->file, e->tok->line, tname(t)); }
      } else {
        Val v = gen(e, s, NULL); rvs[i] = v; Type *t = v.t;
        if (v.ck && v.cv.k != CV_UNDEF && cv_len(&v.cv, &l)) { kind[i] = 1; cvs[i] = v.cv; if (len < 0 && l >= 0) len = l; continue; }
        if (t->k == TY_ARRAY) l = t->len;
        else if (t->k == TY_PTR && t->elem->k == TY_ARRAY) l = t->elem->len;
        else if ((t->k == TY_STRUCT || t->k == TY_TUPLE) && t->ct) { layout(t->ct); l = t->ct->fields.n; }
        else if (t->k == TY_PTR && (t->elem->k == TY_STRUCT || t->elem->k == TY_TUPLE) && t->elem->ct) { layout(t->elem->ct); l = t->elem->ct->fields.n; v = rv(v); rvs[i] = LV(t->elem, opnd(v)); }
        else die("%s:%d: inline for needs a comptime-known length (%s)", e->tok->file, e->tok->line, tname(t));
      }
    }
    if (len < 0 && l >= 0) len = l;
  }
  if (len < 0) die("%s:%d: inline for needs a bounded iterable", n->tok->file, n->tok->line);
  Loop L; memset(&L, 0, sizeof L); Res R; memset(&R, 0, sizeof R); R.ex = ex;
  char *lx = newl(); int stopped = 0;
  L.label = n->label; L.brk = lx; L.res = &R; L.dbase = defers.n; L.kind = 0;
  for (int64_t k = 0; k < len; k++) {
    if (term) { stopped = 1; break; }
    Scope *bs = new_scope(s, NULL);
    for (int i = 0; i < ni && i < n->list2.n; i++) {
      Node *cp = n->list2.a[i]; if (!strcmp(cp->s, "_")) continue;
      if (kind[i] == 2) { bind_cval(bs, cp->s, cv_int(start[i] + k, t_usize)); continue; }
      if (kind[i] == 3) { char *r = tmp(); emit("%s =l add %s, %lld", r, load(t_u64, rvs[i].op), (long long)k); char *sl = slot(t_usize); store(t_u64, r, sl); bind_local(bs, cp->s, t_usize, sl); continue; }
      if (kind[i] == 1) { bind_cval(bs, cp->s, cv_elem(&cvs[i], k)); continue; }
      Val v = rvs[i]; Type *t = v.t; Val e;
      if ((t->k == TY_STRUCT || t->k == TY_TUPLE) && t->ct) { Field *f = t->ct->fields.a[k]; e = f->is_ct ? CK(*(CVal *)f->defcv) : LV(f->t, addp(addr_of(v), f->off)); }
      else e = gen_index(v, CK(cv_int(k, t_usize)));
      cap_bind(bs, cp->s, cp->flags & F_REF, e);
    }
    char *lk = newl(); L.cont = lk; L.cont_used = 0;
    L.up = loops; loops = &L; gen(n->b, bs, NULL); loops = L.up;
    if (term && !L.cont_used) { stopped = 1; break; }
    jmp(lk); label(lk);
  }
  if (!stopped && n->c) res_put(&R, gen(n->c, s, ex));
  int dead = term && !L.brk_used; jmp(lx); label(lx);
  if (dead) { emit("hlt"); term = 1; return NORET(); }
  if (!R.has) return VOIDV();
  return res_get(&R);
}
typedef struct { int range; char *start; char *base; Type *et; char *len; } Iter;
static Type *loop_peer(Node *n, Scope *s) { /* peer-resolve break/else types of a loop expression */
  Node *sc = collect_node; collect_node = n; Type *pt = typeof_impl(n, s); collect_node = sc;
  if (pt && !type_incomplete(pt) && !type_is_ctonly(pt) && pt->k != TY_VOID && pt->k != TY_NORET) return pt;
  return NULL;
}
static Val gen_for(Node *n, Scope *s, Type *ex) {
  if (!ex && n->c && !in_typeof) ex = loop_peer(n, s);
  int ni = n->list.n; Iter *it = xalloc(sizeof(Iter) * ni); char *len = NULL;
  for (int i = 0; i < ni; i++) {
    Node *e = n->list.a[i];
    if (e->k == N_RANGE) {
      it[i].range = 1; it[i].start = opnd(coerce(gen(e->a, s, t_usize), t_usize));
      CVal clo, chi;
      if (e->b && ceval(e->a, s, &clo) && clo.k == CV_INT && ceval(e->b, s, &chi) && chi.k == CV_INT) it[i].len = fmt("%lld", (long long)(chi.i - clo.i));
      else if (e->b) { char *hi = opnd(coerce(gen(e->b, s, t_usize), t_usize)), *l = tmp(); emit("%s =l sub %s, %s", l, hi, it[i].start); it[i].len = l; }
    } else {
      Val v = gen(e, s, NULL); Type *t = v.t;
      if (v.ck && v.cv.k == CV_STR) { it[i].base = mat(v); it[i].et = t_u8; it[i].len = fmt("%d", v.cv.slen); }
      else if (t->k == TY_ARRAY) { it[i].base = addr_of(v); it[i].et = t->elem; it[i].len = fmt("%lld", (long long)t->len); }
      else if (t->k == TY_PTR && t->elem->k == TY_ARRAY) { it[i].base = opnd(v); it[i].et = t->elem->elem; it[i].len = fmt("%lld", (long long)t->elem->len); }
      else if (t->k == TY_SLICE) { char *a = addr_of(v); it[i].base = load(t_u64, a); it[i].len = load(t_u64, addp(a, 8)); it[i].et = t->elem; }
      else if (t->k == TY_MPTR) { it[i].base = opnd(v); it[i].et = t->elem; }
      else die("%s:%d: cannot iterate over %s", e->tok->file, e->tok->line, tname(t));
    }
    if (!len && it[i].len) len = it[i].len;
  }
  if (!len) die("for loop needs a bounded iterable");
  if (!strcmp(len, "0")) return n->c ? gen(n->c, s, ex) : VOIDV(); /* comptime-known empty: body not analyzed */
  Loop L; memset(&L, 0, sizeof L); Res R; memset(&R, 0, sizeof R); R.ex = ex;
  if (n == collect_node && in_typeof) { R.collect = 1; collect_node = NULL; }
  else if (in_typeof && ex_partial(ex)) R.collect = 1;
  char *lc = newl(), *lb = newl(), *lk = newl(), *le = newl(), *lx = newl();
  L.label = n->label; L.brk = lx; L.cont = lk; L.res = &R; L.dbase = defers.n; L.kind = 0;
  char *is = slot(t_usize); store(t_u64, "0", is); jmp(lc); label(lc);
  char *i = load(t_u64, is), *c = tmp(); emit("%s =w cultl %s, %s", c, i, len); br(c, lb, le); label(lb);
  Scope *bs = new_scope(s, NULL);
  for (int k = 0; k < ni && k < n->list2.n; k++) {
    Node *cp = n->list2.a[k];
    if (!strcmp(cp->s, "_")) continue;
    if (it[k].range) { char *v = tmp(); emit("%s =l add %s, %s", v, it[k].start, i); bind_val(bs, cp->s, V(t_usize, v)); continue; }
    char *o = tmp(), *a = tmp(); emit("%s =l mul %s, %d", o, i, tsize(it[k].et)); emit("%s =l add %s, %s", a, it[k].base, o);
    cap_bind(bs, cp->s, cp->flags & F_REF, LV(it[k].et, a));
  }
  L.up = loops; loops = &L; gen(n->b, bs, NULL); loops = L.up;
  jmp(lk); label(lk); { char *i2 = load(t_u64, is), *i3 = tmp(); emit("%s =l add %s, 1", i3, i2); store(t_u64, i3, is); } jmp(lc);
  label(le);
  if (n->c) { Val ev = gen(n->c, s, ex); res_put(&R, ev); }
  jmp(lx); label(lx);
  if (!n->c && !R.has) return VOIDV();
  return res_get(&R);
}
static int item_match_ct(Node *it, Scope *s, CVal *cond, Type *ct) {
  CVal v;
  if (it->k == N_RANGE) { CVal lo, hi; ceval_force(it->a, s, &lo); ceval_force(it->b, s, &hi); return cond->i >= lo.i && cond->i <= hi.i; }
  Type *rt = cond->k == CV_INT ? cv_typeof(cond) : NULL; (void)ct;
  if (!ceval_rt(it, s, rt, &v)) die("%s:%d: switch item not comptime-known", it->tok->file, it->tok->line);
  return cv_match(cond, &v);
}
static void ct_prong_bind(Node *pr, Scope *ps, CVal *cc) {
  int isu = cc->k == CV_AGG && cc->t->k == TY_UNION;
  if (pr->cap) bind_cval(ps, pr->cap, isu ? *cc->el[0] : *cc);
  if (pr->cap2) { if (isu) { Field *f = cc->t->ct->fields.a[cc->i]; CVal tv = {0}; tv.k = CV_INT; tv.i = f->val; tv.t = cc->t->ct->tag; bind_cval(ps, pr->cap2, tv); } else bind_cval(ps, pr->cap2, *cc); }
}
static Val gen_switch(Node *n, Scope *s, Type *ex) {
  CVal cc; Val pre = {0}; int has_pre = 0, known = ceval(n->a, s, &cc);
  if (!known && n->a->k == N_CALL) { /* inline calls can yield comptime-known results */
    pre = rv(gen(n->a, s, NULL)); has_pre = 1;
    if (pre.ck && pre.cv.k != CV_UNDEF) { cc = pre.cv; known = 1; }
  }
  if (known && (!n->label || type_is_ctonly(cv_typeof(&cc)))) {
    Type *ct = cc.t; Node *sel = NULL, *els = NULL;
    for (int i = 0; i < n->list.n && !sel; i++) {
      Node *pr = n->list.a[i]; if (pr->flags & F_ELSE) { els = pr; continue; }
      for (int j = 0; j < pr->list.n; j++) if (item_match_ct(pr->list.a[j], s, &cc, ct)) { sel = pr; break; }
    }
    if (!sel) sel = els;
    if (!sel) die("comptime switch: no prong matched");
    Scope *ps = new_scope(s, NULL); ct_prong_bind(sel, ps, &cc);
    if (!n->label) return gen(sel->b, ps, ex);
    /* labeled switch on a comptime-only operand: behaves like a labeled block around the chosen prong */
    Loop L; memset(&L, 0, sizeof L); Res R; memset(&R, 0, sizeof R); R.ex = ex;
    L.label = n->label; L.brk = newl(); L.res = &R; L.dbase = defers.n; L.kind = 1; L.up = loops; loops = &L;
    Val v = gen(sel->b, ps, ex);
    loops = L.up;
    if (!term && v.t->k != TY_NORET) res_put(&R, v);
    jmp(L.brk); label(L.brk); return res_get(&R);
  }
  int anyref = 0; for (int i = 0; i < n->list.n; i++) if (((Node *)n->list.a[i])->capref) anyref = 1;
  Val lvv = {0}; int uselv = 0;
  if (has_pre) lvv = pre; else { lvv = gen(n->a, s, NULL); if (anyref && !n->label && lvv.lv && !lvv.bf && !lvv.ck) uselv = 1; }
  Val cv = uselv ? lvv : rv(lvv); Type *ct = cv.t;
  if (ct->k == TY_CINT) { cv = coerce(cv, t_i64); ct = t_i64; }
  Res R; memset(&R, 0, sizeof R); R.ex = ex;
  if ((!ex || ex_partial(ex)) && in_typeof) R.collect = 1;
  else if (!ex) { Type *pt = typeof_impl(n, s); if (pt && !type_incomplete(pt) && !type_is_ctonly(pt) && pt->k != TY_VOID) R.ex = ex = pt; }
  Loop L; memset(&L, 0, sizeof L);
  char *sw = uselv ? cv.op : slot(ct), *ld = newl(), *lx = newl();
  if (!uselv) put(cv, ct, sw);
  jmp(ld); label(ld);
  L.label = n->label; L.kind = 2; L.swslot = sw; L.swdisp = ld; L.swt = ct; L.brk = lx; L.res = &R; L.dbase = defers.n;
  int isu = ct->k == TY_UNION; Type *tagt = isu ? ct->ct->tag : ct;
  char *x = isu ? load(tagt, addp(sw, union_tag_off(ct))) : load(ct, sw);
  /* expand prongs into cases; inline prongs get one case per (comptime-known) value */
  typedef struct { Node *pr; int isct; CVal v; char *lab; } Case;
  Vec cases = {0}; int elsei = -1;
  for (int i = 0; i < n->list.n; i++) {
    Node *pr = n->list.a[i];
    if (pr->flags & F_INLINE) {
      if (pr->flags & F_ELSE) {
        int nvals; if (tagt->k == TY_ENUM) { layout(tagt->ct); nvals = tagt->ct->fields.n; }
        else if (tagt->k == TY_BOOL) nvals = 2;
        else if (tagt->k == TY_INT && tagt->bits <= 10) nvals = 1 << tagt->bits;
        else die("%s:%d: inline else needs an enum, bool, small int or tagged union operand", pr->tok->file, pr->tok->line);
        for (int k = 0; k < nvals; k++) {
          Field fb = {0}; Field *f = &fb;
          if (tagt->k == TY_ENUM) f = tagt->ct->fields.a[k]; else fb.val = (tagt->k == TY_INT && tagt->sign) ? k - (1 << (tagt->bits - 1)) : k;
          int covered = 0;
          for (int j = 0; j < n->list.n && !covered; j++) {
            Node *op = n->list.a[j]; if (op->flags & F_ELSE) continue;
            for (int m = 0; m < op->list.n; m++) { Node *it = op->list.a[m]; CVal iv; if (it->k == N_RANGE) continue; if (ceval_rt(it, s, tagt, &iv) && iv.k == CV_INT && iv.i == f->val) { covered = 1; break; } }
          }
          if (covered) continue;
          Case *c = xalloc(sizeof *c); c->pr = pr; c->isct = 1; c->v = tagt->k == TY_BOOL ? cv_bool((int)f->val) : cv_int(f->val, tagt); vpush(&cases, c);
        }
      } else for (int m = 0; m < pr->list.n; m++) {
        Node *it = pr->list.a[m];
        if (it->k == N_RANGE) { CVal lo, hi;
          if (!ceval_rt(it->a, s, NULL, &lo) || !ceval_rt(it->b, s, NULL, &hi) || lo.k != CV_INT || hi.k != CV_INT) die("%s:%d: inline prong range must be comptime-known", it->tok->file, it->tok->line);
          if (hi.i - lo.i > 100000) die("%s:%d: inline prong range too large", it->tok->file, it->tok->line);
          for (i128 q = lo.i; q <= hi.i; q++) { Case *c = xalloc(sizeof *c); c->pr = pr; c->isct = 1; c->v = cv_int(q, tagt); vpush(&cases, c); }
          continue; }
        Case *c = xalloc(sizeof *c); c->pr = pr; c->isct = 1;
        if (!ceval_rt(it, s, tagt, &c->v)) die("%s:%d: inline prong items must be comptime-known values", it->tok->file, it->tok->line);
        c->v = ccoerce(c->v, tagt); vpush(&cases, c);
      }
      continue;
    }
    Case *c = xalloc(sizeof *c); c->pr = pr; if (pr->flags & F_ELSE) elsei = cases.n; vpush(&cases, c);
  }
  for (int i = 0; i < cases.n; i++) {
    Case *c = cases.a[i]; Node *pr = c->pr; c->lab = newl();
    if (i == elsei) continue;
    if (c->isct) {
      char *nx = newl(), *cmp = tmp(); emit("%s =w ceq%c %s, %lld", cmp, qc(tagt), x, (long long)c->v.i); br(cmp, c->lab, nx); label(nx); continue;
    }
    for (int j = 0; j < pr->list.n; j++) {
      Node *it = pr->list.a[j]; char *nx = newl(), *cmp = tmp();
      if (it->k == N_RANGE) {
        Val lo = coerce(gen(it->a, s, tagt), tagt), hi = coerce(gen(it->b, s, tagt), tagt); char *c1 = tmp(), *c2 = tmp(); int sg = tagt->k == TY_INT && tagt->sign;
        emit("%s =w c%s%c %s, %s", c1, sg ? "sge" : "uge", qc(tagt), x, opnd(lo)); emit("%s =w c%s%c %s, %s", c2, sg ? "sle" : "ule", qc(tagt), x, opnd(hi));
        emit("%s =w and %s, %s", cmp, c1, c2);
      } else {
        Val iv = coerce(gen(it, s, tagt), tagt);
        emit("%s =w ceq%c %s, %s", cmp, qc(tagt), x, opnd(iv));
      }
      br(cmp, c->lab, nx); label(nx);
    }
  }
  if (elsei >= 0) jmp(((Case *)cases.a[elsei])->lab); else { emit("hlt"); term = 1; }
  L.up = loops; loops = &L;
  for (int i = 0; i < cases.n; i++) {
    Case *c = cases.a[i]; Node *pr = c->pr; label(c->lab); Scope *ps = new_scope(s, NULL);
    if (pr->cap) {
      if (isu) {
        Field *f = NULL;
        if (c->isct) { for (int k = 0; k < ct->ct->fields.n; k++) { Field *ff = ct->ct->fields.a[k]; if (ff->val == (int64_t)c->v.i) f = ff; } }
        else if (!(pr->flags & F_ELSE)) { Node *it = pr->list.a[0]; CVal iv; ceval(it, s, &iv); f = iv.k == CV_ENUMLIT ? find_field(ct->ct, iv.s) : NULL;
          if (!f && iv.k == CV_INT) for (int k = 0; k < ct->ct->fields.n; k++) { Field *ff = ct->ct->fields.a[k]; if (ff->val == (int64_t)iv.i) f = ff; } }
        if (f && f->t->k == TY_NORET) { emit("hlt"); term = 1; continue; } /* payload of type noreturn: prong unreachable */
        if (f) cap_bind(ps, pr->cap, pr->capref, LV(f->t, sw)); else cap_bind(ps, pr->cap, pr->capref, LV(ct, sw));
      } else if (c->isct && !pr->capref) bind_cval(ps, pr->cap, c->v);
      else cap_bind(ps, pr->cap, pr->capref, LV(ct, sw));
    }
    if (pr->cap2) { if (c->isct) bind_cval(ps, pr->cap2, c->v); else bind_val(ps, pr->cap2, V(tagt, x)); }
    Val v = gen(pr->b, ps, ex); res_put(&R, v); jmp(lx);
  }
  loops = L.up;
  label(lx);
  return res_get(&R);
}
static Val ret_val(Val v, int noval);
static Val gen_return(Node *n, Scope *s) {
  Val v;
  if (n->a) v = gen(n->a, s, fret);
  else v = VOIDV();
  return ret_val(v, !n->a);
}
static Val ret_val(Val v, int noval) {
  if (v.t->k == TY_NORET) return v;
  if (inl && in_typeof > inl->level) { term = 1; return NORET(); } /* dry run inside an inline body: don't touch the frame */
  if (inl) {
    if (noval && fret->k == TY_ERRU) { char *sl = slot(fret); store(t_u16, "0", sl); v = V(fret, sl); }
    else v = coerce(v, fret);
    if (v.ck && v.cv.k != CV_UNDEF) { if (inl->nret && !cval_eq(&inl->ckv, &v.cv)) inl->allck = 0; inl->ckv = v.cv; } else inl->allck = 0;
    inl->nret++;
    run_defers(inl->dbase, NULL); if (!term) { res_put(inl->res, v); jmp(inl->lx); }
    term = 1; return NORET();
  }
  if (noval && fret->k == TY_ERRU) { char *sl = slot(fret); store(t_u16, "0", sl); v = V(fret, sl); }
  else v = coerce(v, fret);
  if (is_aggr(fret)) {
    put(v, fret, fsret);
    if (fret->k == TY_ERRU && have_errdefer(0)) {
      char *e = load(t_u16, fsret), *le = newl(), *lo = newl(); br(e, le, lo);
      label(le); run_defers(0, e); if (!term) emit("ret"); term = 1;
      label(lo); run_defers(0, NULL); if (!term) emit("ret"); term = 1;
    } else { run_defers(0, NULL); if (!term) emit("ret"); }
  } else if (fret->k == TY_VOID || tsize(fret) == 0) { run_defers(0, NULL); if (!term) emit("ret"); }
  else { char *o = opnd(v); run_defers(0, NULL); if (!term) emit("ret %s", o); }
  term = 1; return NORET();
}
static Val gen_try(Node *n, Scope *s, Type *ex) {
  Val v = gen(n->a, s, ex && ex->k != TY_ERRU && ex->k != TY_ANYTYPE ? erru_of(ex) : NULL);
  if (v.t->k == TY_ERRSET) { char *e = opnd(v); store(t_u16, e, fsret); run_defers(0, e); emit("ret"); term = 1; return NORET(); }
  if (v.t->k != TY_ERRU) return v; /* lenient: only reachable in code real Zig would not analyze (e.g. catch of an empty inferred error set) */
  char *a = addr_of(v), *e = load(t_u16, a), *le = newl(), *lo = newl();
  br(e, le, lo); label(le);
  if (fret->k == TY_ERRU) { store(t_u16, e, fsret); run_defers(0, e); if (!term) emit("ret"); }
  else if (fret->k == TY_ERRSET) { run_defers(0, e); if (!term) emit("ret %s", e); }
  else die("try in function that does not return an error");
  term = 1; label(lo);
  if (v.t->elem == t_void) return VOIDV();
  return LV(v.t->elem, addp(a, erru_off(v.t)));
}
static Val gen_catch(Node *n, Scope *s, Type *ex) {
  Val v = gen(n->a, s, ex && ex->k != TY_ERRU && ex->k != TY_ANYTYPE ? erru_of(ex) : NULL);
  if (v.t->k != TY_ERRU && v.ck) { /* comptime-known error union value */
    if (v.cv.k == CV_ERR) { Scope *cs = new_scope(s, NULL); if (n->cap) bind_cval(cs, n->cap, v.cv); return gen(n->b, cs, ex); }
    return ex ? coerce(v, ex) : v;
  }
  if (v.t->k != TY_ERRU) die("%s:%d: catch on non error union %s (ck=%d)", n->tok->file, n->tok->line, tname(v.t), v.ck);
  Res R; memset(&R, 0, sizeof R); R.ex = ex ? ex : v.t->elem;
  int discard = !ex && n->b->k == N_BLOCK && n->b->list.n == 0 && !n->b->label; /* `x catch {}`: result is void */
  if (discard) R.ex = t_void;
  else if (!ex && in_typeof) { R.ex = NULL; R.collect = 1; }
  else if (!ex) { Scope *cs0 = new_scope(s, NULL); if (n->cap) bind_val(cs0, n->cap, V(t_errset, "0")); Type *bt = typeof_impl(n->b, cs0), *p = bt && bt->k != TY_NORET ? peer_t(v.t->elem, bt) : NULL; if (p && p->k != TY_CINT && p->k != TY_VOID) R.ex = p; }
  char *a = addr_of(v), *e = load(t_u16, a), *le = newl(), *lo = newl(), *lx = newl();
  br(e, le, lo); label(lo);
  res_put(&R, v.t->elem == t_void || discard ? VOIDV() : rv(LV(v.t->elem, addp(a, erru_off(v.t))))); jmp(lx);
  label(le); Scope *cs = new_scope(s, NULL); if (n->cap) bind_val(cs, n->cap, V(t_errset, e));
  res_put(&R, gen(n->b, cs, R.collect ? NULL : R.t ? R.t : R.ex)); jmp(lx);
  label(lx); return res_get(&R);
}
static Val gen_orelse(Node *n, Scope *s, Type *ex) {
  Val v = gen(n->a, s, ex ? opt_of(ex) : NULL);
  if (v.ck && v.cv.k == CV_NULL && v.cv.slen <= 0) return gen(n->b, s, ex);
  if (v.ck && v.t->k != TY_OPT) return v; /* comptime-known non-null payload */
  if (v.t->k != TY_OPT) die("%s:%d: orelse on non optional", n->tok->file, n->tok->line);
  Res R; memset(&R, 0, sizeof R); R.ex = ex ? ex : v.t->elem;
  if (!ex && in_typeof) { R.ex = NULL; R.collect = 1; }
  else if (!ex) { Type *bt = typeof_impl(n->b, s), *p = bt && bt->k != TY_NORET ? peer_t(v.t->elem, bt) : NULL; if (p && p->k != TY_CINT) R.ex = p; }
  char *pv = opt_is_ptr(v.t) ? opnd(v) : NULL, *lh = newl(), *ln = newl(), *lx = newl();
  if (pv) { char *h = tmp(); emit("%s =w cnel %s, 0", h, pv); br(h, lh, ln); } else br(opt_has(v), lh, ln);
  label(lh); res_put(&R, rv(opt_payload(v, pv))); jmp(lx);
  label(ln); res_put(&R, gen(n->b, s, R.collect ? NULL : R.t ? R.t : R.ex)); jmp(lx);
  label(lx); return res_get(&R);
}
static Sym *last_sym(Scope *s) { return s->syms.a[s->syms.n - 1]; }
static void gen_vardecl(Node *n, Scope *s) {
  Type *t = n->a ? eval_type(n->a, s) : NULL;
  if (n->flags & F_COMPTIME) {
    CVal c;
    if (!n->b) { memset(&c, 0, sizeof c); c.k = CV_UNDEF; c.t = t ? t : t_undef; }
    else if (!ceval_rt(n->b, s, t, &c)) die("%s:%d: comptime variable initializer is not comptime-known (at %s)", n->tok->file, n->tok->line, ct_fail_loc());
    if (t) c = ccoerce(c, t);
    bind_cval(s, n->s, cv_copy(c)); last_sym(s)->mut = !(n->flags & F_CONST); return;
  }
  if ((n->flags & F_CONST) && n->b) {
    CVal c;
    if (n->b->k == N_CONTAINER) { c = cv_ty(container_from(n->b, s, n->s)->type); bind_cval(s, n->s, c); return; }
    if (ceval_ex(n->b, s, t, &c) && c.k != CV_UNDEF && c.k != CV_NONE) {
      if (t) c = ccoerce(c, t);
      if ((!t || ck_ok(&c, t)) && !(t && t->k == TY_ERRU && c.k == CV_VOID)) { bind_cval(s, n->s, c); last_sym(s)->t = t; return; }
    }
  }
  Val v = n->b ? gen(n->b, s, t) : CK((CVal){ .k = CV_UNDEF, .t = t_undef });
  if (v.t->k == TY_NORET) return;
  if ((n->flags & F_CONST) && v.ck && v.cv.k != CV_UNDEF && v.cv.k != CV_NONE && (!t || ck_ok(&v.cv, t))) { /* comptime-known const */
    CVal c = t ? ccoerce(v.cv, t) : v.cv; bind_cval(s, n->s, c); last_sym(s)->t = t; return; }
  if (!t) t = v.t;
  if (t->k == TY_CINT) t = t_i64;
  if (v.ck && v.cv.k == CV_STR && !n->a) t = v.t;
  if (type_is_ctonly(t)) { if (v.ck) { bind_cval(s, n->s, v.cv); last_sym(s)->mut = !(n->flags & F_CONST); return; } die("%s:%d: variable of comptime-only type needs comptime", n->tok->file, n->tok->line); }
  v = coerce(v, t);
  char *sl = slot(t); put(v, t, sl); bind_local(s, n->s, t, sl);
}
static void gen_assign(Node *n, Scope *s) {
  if (n->a->k == N_IDENT && !strcmp(n->a->s, "_")) { discarding++; gen(n->b, s, NULL); discarding--; return; }
  if (ct_try_assign(n, s)) return;
  Val l = gen(n->a, s, NULL);
  if (!l.lv) die("%s:%d: cannot assign to rvalue", n->tok->file, n->tok->line);
  if (!strcmp(n->s, "=")) { Val v = coerce(gen(n->b, s, l.t), l.t); if (v.t->k == TY_NORET) return; put_lv(v, l); return; }
  char op[8]; strcpy(op, n->s); op[strlen(op) - 1] = 0;
  Val r = gen(n->b, s, l.t);
  Val v = coerce(gen_arith(op, rv(l), r), l.t); put_lv(v, l);
}
static void gen_destruct(Node *n, Scope *s) {
  Type *ext = NULL;
  { int allc = n->list.n > 0; for (int i = 0; i < n->list.n && allc; i++) { Node *tg = n->list.a[i]; if (!((tg->k == N_VAR && (tg->flags & F_CONST)) || (tg->k == N_IDENT && !strcmp(tg->s, "_")))) allc = 0; }
    CVal c; int64_t l;
    if (allc && ceval_ex(n->b, s, NULL, &c) && c.k == CV_AGG && cv_len(&c, &l) && l == n->list.n) {
      for (int i = 0; i < n->list.n; i++) { Node *tg = n->list.a[i]; if (tg->k != N_VAR) continue;
        CVal e = cv_elem(&c, i); Type *t = tg->a ? eval_type(tg->a, s) : NULL; if (t) e = ccoerce(e, t);
        bind_cval(s, tg->s, e); if (t) last_sym(s)->t = t; }
      return; } }
  { int ok = 1; Vec names = {0}, types = {0};
    for (int i = 0; i < n->list.n && ok; i++) { Node *tg = n->list.a[i]; if (tg->k == N_VAR && tg->a) { vpush(&names, fmt("%d", i)); vpush(&types, eval_type(tg->a, s)); } else if (tg->k != N_VAR && !(tg->k == N_IDENT && !strcmp(tg->s, "_"))) { Type *lt = typeof_impl(tg, s); if (lt) { vpush(&names, fmt("%d", i)); vpush(&types, lt); } else ok = 0; } else ok = 0; }
    if (!ok && n->list.n) { /* some untyped targets: take their types from the (dry-run) rhs tuple */
      Vec hn = {0}, ht = {0};
      for (int i = 0; i < n->list.n; i++) { Node *tg = n->list.a[i]; vpush(&hn, fmt("%d", i)); vpush(&ht, tg->k == N_VAR && tg->a ? eval_type(tg->a, s) : t_anytype); }
      int anyt = 0; for (int i = 0; i < ht.n; i++) if (ht.a[i] != t_anytype) anyt = 1;
      Type *rt = anyt ? typeof_ex(n->b, s, mk_anon_struct(&hn, &ht, 1)) : typeof_impl(n->b, s); ok = rt && is_tuple_type(rt) && (layout(rt->ct), rt->ct->fields.n == n->list.n); names.n = types.n = 0;
      for (int i = 0; i < n->list.n && ok; i++) { Node *tg = n->list.a[i]; Type *ft = ((Field *)rt->ct->fields.a[i])->t; Type *tt;
        if (tg->k == N_VAR && tg->a) tt = eval_type(tg->a, s);
        else if (tg->k == N_VAR || (tg->k == N_IDENT && !strcmp(tg->s, "_"))) tt = ft;
        else tt = typeof_impl(tg, s);
        if (!tt || type_incomplete(tt) || type_is_ctonly(tt)) { ok = 0; break; }
        vpush(&names, fmt("%d", i)); vpush(&types, tt); }
    }
    if (ok && n->list.n) ext = mk_anon_struct(&names, &types, 1); }
  Val v = gen(n->b, s, ext); Type *t = v.t; if (t->k == TY_NORET) return;
  if (ext && t != ext && t->k != TY_ARRAY) { v = coerce(v, ext); t = v.t; }
  if (t->k != TY_ARRAY && !t->ct) die("%s:%d: cannot destructure %s", n->tok->file, n->tok->line, tname(t));
  char *a = addr_of(v);
  for (int i = 0; i < n->list.n; i++) {
    Node *tg = n->list.a[i]; Val e;
    if (t->k == TY_ARRAY) e = LV(t->elem, addp(a, (int64_t)i * tsize(t->elem)));
    else { Field *f = t->ct->fields.a[i]; e = LV(f->t, addp(a, f->off)); }
    if (tg->k == N_VAR) { Type *tt = tg->a ? eval_type(tg->a, s) : e.t; Val c = coerce(rv(e), tt); char *sl = slot(tt); put(c, tt, sl); bind_local(s, tg->s, tt, sl); continue; }
    if (tg->k == N_IDENT && !strcmp(tg->s, "_")) continue;
    Val l = gen(tg, s, NULL); put_lv(coerce(rv(e), l.t), l);
  }
}

/* ---------- dispatcher ---------- */

/* ---------- inline asm: only `syscall` is supported (via libc syscall(), errno -> -errno) ---------- */
static int sys_helper_done;
static Val gen(Node *n, Scope *s, Type *ex);

/* general inline asm: each site becomes a stub function in the side file <out>.asm.s.
   The stub gets a buffer pointer (rdi) holding 8-byte slots [inputs..., outputs...]; it saves callee-saved
   registers, loads inputs into their constraint registers, runs the template, and stores outputs back. */
FILE *asm_out; static int asm_n;
static const char *areg[16][4] = { {"rax","eax","ax","al"}, {"rbx","ebx","bx","bl"}, {"rcx","ecx","cx","cl"}, {"rdx","edx","dx","dl"},
  {"rsi","esi","si","sil"}, {"rdi","edi","di","dil"}, {"rbp","ebp","bp","bpl"}, {"r8","r8d","r8w","r8b"}, {"r9","r9d","r9w","r9b"},
  {"r10","r10d","r10w","r10b"}, {"r11","r11d","r11w","r11b"}, {"r12","r12d","r12w","r12b"}, {"r13","r13d","r13w","r13b"},
  {"r14","r14d","r14w","r14b"}, {"r15","r15d","r15w","r15b"}, {"rsp","esp","sp","spl"} };
static int areg_find(const char *nm) { for (int r = 0; r < 16; r++) for (int k = 0; k < 4; k++) if (!strcmp(nm, areg[r][k])) return r; return -1; }
static int asz_idx(Type *t) { int64_t z = tsize(t); return z >= 8 ? 0 : z == 4 ? 1 : z == 2 ? 2 : 3; }
static Val gen_asm_stub(Node *n, Scope *s, CVal *tpl, Type *rt) {
  Val none = {0}; if (!asm_out) return none;
  int m = n->list.n; if (m > 24) return none;
  int reg[24], dir[24], rw[24]; Type *ty[24]; Val lvs[24]; char *ins[24]; int used = 0;
  for (int i = 0; i < m; i++) {
    Node *o = n->list.a[i]; char con[64]; const char *L = o->label;
    if (L[0] == '"') snprintf(con, sizeof con, "%.*s", (int)strlen(L) - 2, L + 1); else snprintf(con, sizeof con, "%s", L);
    char *c = con; dir[i] = o->ival; rw[i] = 0; reg[i] = -1;
    if (*c == '=') c++; else if (*c == '+') { c++; rw[i] = 1; }
    if (*c == '&') c++;
    if (*c == '{') { char nm[16]; snprintf(nm, sizeof nm, "%.*s", (int)strcspn(c + 1, "}"), c + 1); reg[i] = areg_find(nm); if (reg[i] < 0) return none; used |= 1 << reg[i]; }
    else if (strcmp(c, "r")) return none;
  }
  for (int i = 0; i < m; i++) if (reg[i] < 0) { static const int pool[] = { 0, 2, 3, 4, 5, 7, 8, 9, 10, 1, 11, 12, 13, 14 };
    for (int k = 0; k < 14; k++) if (!(used & (1 << pool[k]))) { reg[i] = pool[k]; used |= 1 << pool[k]; break; } if (reg[i] < 0) return none; }
  /* evaluate operands */
  for (int i = 0; i < m; i++) { Node *o = n->list.a[i]; ins[i] = NULL;
    if (dir[i] == 0) { if (o->flags & F_REF) ty[i] = rt; else { lvs[i] = gen(o->a, s, NULL); if (!lvs[i].lv || lvs[i].bf) return none; ty[i] = lvs[i].t; }
      if (is_float(ty[i])) return none;
      if (rw[i]) { Val v = rv(lvs[i]); ins[i] = opnd(v); if (qc(v.t) == 'w') { char *e = tmp(); emit("%s =l extuw %s", e, ins[i]); ins[i] = e; } } }
    else { Val v = rv(gen(o->a, s, NULL)); if (v.t->k == TY_CINT) v = coerce(v, t_u64); if (is_float(v.t)) return none; ty[i] = v.t;
      ins[i] = opnd(v); if (qc(v.t) == 'w') { char *e = tmp(); emit("%s =l extuw %s", e, ins[i]); ins[i] = e; } } }
  int id = asm_n++; char *buf = tmp(); emit("%s =l alloc8 %d", buf, 8 * (m ? m : 1));
  for (int i = 0; i < m; i++) if (ins[i]) emit("storel %s, %s", ins[i], addp(buf, 8 * i));
  emit("call $zb_asm_%d(l %s)", id, buf);
  FILE *f = asm_out; fprintf(f, "\t.text\n\t.globl zb_asm_%d\nzb_asm_%d:\n\tpush %%rbx\n\tpush %%rbp\n\tpush %%r12\n\tpush %%r13\n\tpush %%r14\n\tpush %%r15\n\tpush %%rdi\n", id, id);
  int rdi_in = -1;
  for (int i = 0; i < m; i++) if (ins[i]) { if (reg[i] == 5) rdi_in = i; else fprintf(f, "\tmovq %d(%%rdi), %%%s\n", 8 * i, areg[reg[i]][0]); }
  if (rdi_in >= 0) fprintf(f, "\tmovq %d(%%rdi), %%rdi\n", 8 * rdi_in);
  fputc('\t', f);
  for (int k = 0; k < tpl->slen; k++) { char ch = tpl->s[k];
    if (ch == '%' && k + 1 < tpl->slen && tpl->s[k + 1] == '%') { fputc('%', f); k++; continue; }
    if (ch == '%' && k + 1 < tpl->slen && tpl->s[k + 1] == '[') { int e = k + 2; while (e < tpl->slen && tpl->s[e] != ']') e++;
      char nm[64]; snprintf(nm, sizeof nm, "%.*s", e - k - 2, tpl->s + k + 2); char *mod = strchr(nm, ':'); if (mod) *mod++ = 0;
      int hit = -1; for (int i = 0; i < m; i++) if (!strcmp(((Node *)n->list.a[i])->s, nm)) { hit = i; break; }
      if (hit < 0) die("%s:%d: asm: unknown operand %%[%s]", n->tok->file, n->tok->line, nm);
      int zi = asz_idx(ty[hit]); if (mod && *mod == 'q') zi = 0; else if (mod && *mod == 'k') zi = 1; else if (mod && *mod == 'w') zi = 2; else if (mod && *mod == 'b') zi = 3;
      fprintf(f, "%%%s", areg[reg[hit]][zi]); k = e; continue; }
    fputc(ch, f); if (ch == '\n') fputc('\t', f); }
  fputc('\n', f);
  int nout = 0; for (int i = 0; i < m; i++) if (dir[i] == 0) { fprintf(f, "\tpush %%%s\n", areg[reg[i]][0]); nout++; }
  fprintf(f, "\tmovq %d(%%rsp), %%r11\n", 8 * nout);
  for (int i = m - 1; i >= 0; i--) if (dir[i] == 0) fprintf(f, "\tpop %%rax\n\tmovq %%rax, %d(%%r11)\n", 8 * i);
  fprintf(f, "\tadd $8, %%rsp\n\tpop %%r15\n\tpop %%r14\n\tpop %%r13\n\tpop %%r12\n\tpop %%rbp\n\tpop %%rbx\n\tret\n");
  Val ret = VOIDV();
  for (int i = 0; i < m; i++) if (dir[i] == 0) { char *a = addp(buf, 8 * i);
    if (((Node *)n->list.a[i])->flags & F_REF) ret = V(ty[i], load(ty[i], a)); else put(V(ty[i], load(ty[i], a)), ty[i], lvs[i].op); }
  return ret;
}
static Val gen_asm(Node *n, Scope *s) {
  CVal tpl; if (!ceval(n->a, s, &tpl) || tpl.k != CV_STR) die("%s:%d: asm template must be a string", n->tok->file, n->tok->line);
  Type *rt = t_void;
  for (int i = 0; i < n->list.n; i++) { Node *o = n->list.a[i]; if (o->ival == 0 && (o->flags & F_REF)) rt = eval_type(o->a, s); }
  if (tpl.slen == 7 && !memcmp(tpl.s, "syscall", 7)) {
    static const char *regs[] = { "{rax}", "{rdi}", "{rsi}", "{rdx}", "{r10}", "{r8}", "{r9}" };
    char *a[7] = { "0", "0", "0", "0", "0", "0", "0" };
    for (int i = 0; i < n->list.n; i++) {
      Node *o = n->list.a[i]; if (o->ival != 1) continue;
      char con[32]; if (o->label[0] == '"') snprintf(con, sizeof con, "%.*s", (int)strlen(o->label) - 2, o->label + 1); else snprintf(con, sizeof con, "%s", o->label);
      for (int r = 0; r < 7; r++) if (!strcmp(con, regs[r])) { Val v = rv(gen(o->a, s, t_u64)); if (v.t->k == TY_CINT) v = coerce(v, t_u64); if (qc(v.t) == 'w') { char *e = tmp(); emit("%s =l extuw %s", e, opnd(v)); a[r] = e; } else a[r] = opnd(v); }
    }
    if (!sys_helper_done) {
      sys_helper_done = 1;
      fprintf(xb, "function l $zb.syscall(l %%n, l %%a, l %%b, l %%c, l %%d, l %%e, l %%f) {\n@start\n\t%%r =l call $syscall(l %%n, ..., l %%a, l %%b, l %%c, l %%d, l %%e, l %%f)\n"
        "\t%%m =w ceql %%r, -1\n\tjnz %%m, @err, @ok\n@err\n\t%%p =l call $__errno_location()\n\t%%x =w loadsw %%p\n\t%%y =l extsw %%x\n\t%%z =l neg %%y\n\tret %%z\n@ok\n\tret %%r\n}\n");
    }
    char *r = tmp(); emit("%s =l call $zb.syscall(l %s, l %s, l %s, l %s, l %s, l %s, l %s)", r, a[0], a[1], a[2], a[3], a[4], a[5], a[6]);
    if (rt == t_void) return VOIDV();
    return coerce(V(t_u64, r), rt);
  }
  Val gv = gen_asm_stub(n, s, &tpl, rt); if (gv.t) return gv;
  fprintf(stderr, "zb: warning: %s:%d: unsupported inline asm \"%.*s\" compiled as a trap\n", n->tok->file, n->tok->line, tpl.slen > 40 ? 40 : tpl.slen, tpl.s);
  emit("hlt"); term = 1; return NORET();
}

static Node *gen_cur;
static Type *typeof_impl(Node *n, Scope *s);
Node *gen_cur_pub(void) { return gen_cur; }
static Val gen(Node *n, Scope *s, Type *ex) {
  CVal c; if (n->tok) gen_cur = n;
  switch (n->k) {
  case N_INT: case N_CHAR: case N_TRUE: case N_FALSE: case N_NULL: case N_UNDEF: case N_ENUMLIT: case N_ERRVAL: case N_STR:
  case N_TPTR: case N_TARRAY: case N_TOPT: case N_TERRU: case N_TFN: case N_CONTAINER: case N_ERRSET:
    if (!ceval(n, s, &c)) die("%s:%d: bad constant", n->tok->file, n->tok->line);
    return CK(c);
  case N_IDENT: {
    if (!strcmp(n->s, "_")) return VOIDV();
    Type *pt = n->tok && n->tok->k == TK_ID && n->tok->ival ? NULL : prim_type(n->s); if (pt) { c.k = CV_TYPE; c.t = pt; return CK(c); }
    Sym *y; Decl *d;
    if (!lookup(s, n->s, &y, &d)) die("%s:%d: use of undeclared identifier '%s'", n->tok->file, n->tok->line, n->s);
    if (y) { if (y->k == S_CVAL) { Val r = CK(y->cv); if (y->t && r.ck) r.t = y->t; return r; } if (!y->addr && in_typeof && y->t) return V(y->t, "0"); if (!y->addr) die("%s:%d: '%s' is not available here", n->tok->file, n->tok->line, n->s); return LV(y->t, y->addr); }
    resolve_decl(d);
    if (d->kind == D_VAR) return LV(d->t, fmt("$%s", d->sym));
    { Val r = CK(d->cv); if (d->t && r.ck) r.t = d->t; return r; }
  }
  case N_FIELD: {
    if (ceval(n, s, &c)) return CK(c);
    Val b = gen(n->a, s, NULL); Val r = gen_member(b, n->s, n);
    if (!r.ck && r.t && (r.t->k == TY_NULL || r.t->k == TY_VOID)) return CK(r.t->k == TY_NULL ? cv_null_pub() : (CVal){ .k = CV_VOID, .t = t_void });
    return r;
  }
  case N_DEREF: { Val v = rv(gen(n->a, s, NULL)); Val r = LV(v.t->elem, opnd(v)); if (v.t->k == TY_PTR && v.t->len > 0) { r.bf = 1; r.hbytes = (int)v.t->len; r.bitoff = (int)v.t->sent; } return r; }
  case N_UNWRAP: { Val v = gen(n->a, s, NULL);
    if (v.ck && v.cv.k == CV_NULL) { if (!term) emit("hlt"); term = 1; return NORET(); }
    if (v.ck && v.t->k != TY_OPT) return v;
    if (v.t->k != TY_OPT) die("%s:%d: .? on non-optional %s", n->tok->file, n->tok->line, tname(v.t));
    return opt_payload(v, NULL); }
  case N_INDEX: { if (ceval(n, s, &c)) return CK(c); Val b = gen(n->a, s, NULL); Val i = gen(n->b, s, t_usize); return gen_index(b, i); }
  case N_SLICE: return gen_slice(n, s);
  case N_CALL: return gen_call(n, s, ex);
  case N_BUILTIN: return gen_builtin(n, s, ex);
  case N_INIT:
    if (ex && is_tuple_type(ex) && (layout(ex->ct), 1)) { int any = 0; for (int i = 0; i < ex->ct->fields.n; i++) if (((Field *)ex->ct->fields.a[i])->t->k == TY_ANYTYPE) any = 1; if (any) return gen_init(n, s, ex); }
    if (ceval_ex(n, s, ex, &c)) { Val r = CK(c); if (ex && ck_ok(&c, ex)) r.t = ex; return r; }
    return gen_init(n, s, ex);
  case N_UN: {
    const char *op = n->s;
    if (!strcmp(op, "&")) {
      Node *a = n->a;
      if (a->k == N_INIT && !a->a && ex && (ex->k == TY_SLICE || ex->k == TY_MPTR || (ex->k == TY_PTR && ex->elem->k == TY_ARRAY))) {
        Type *et = ex->k == TY_PTR ? ex->elem->elem : ex->elem; Type *at = array_of(et, a->list.n, 0, 0);
        Val v = gen_init(a, s, at); return V(ptr_to(at, 1), addr_of(v));
      }
      Val v;
      if (a->k == N_ENUMLIT && ex && ex->k == TY_PTR && ex->elem->ct && (ex->elem->k == TY_STRUCT || ex->elem->k == TY_UNION) && find_decl(ex->elem->ct, a->s)) {
        CVal tv = {0}; tv.k = CV_TYPE; tv.t = ex->elem; v = gen_member(CK(tv), a->s, a); /* &.decl_literal */
      } else v = gen(a, s, ex && ex->k == TY_PTR ? ex->elem : NULL);
      if (v.ck && v.cv.k == CV_FN) { FnInst *fi = plain_inst(v.cv.fn); return V(ptr_to(fn_type(&fi->ptypes, fi->ret, 0), 1), fmt("$%s", fi->sym)); }
      if (v.lv && v.bf) return V(bitptr_to(v.t, 0, v.hbytes, v.bitoff), v.op);
      if (v.lv) return V(ptr_to(v.t, 0), v.op);
      if (v.ck && v.cv.k == CV_STR) return V(v.t, mat(v));
      if (v.ck && v.cv.k == CV_AGG && is_tuple_type(v.t) && ex && (ex->k == TY_SLICE || ex->k == TY_MPTR || (ex->k == TY_PTR && ex->elem->k == TY_ARRAY))) {
        layout(v.t->ct); Type *at = ex->k == TY_PTR ? ex->elem : array_of(ex->elem, v.t->ct->fields.n, ex->hassent, ex->sent);
        if (at->elem->k != TY_ANYTYPE) v = coerce(v, at);
      }
      if (is_aggr(v.t)) return V(ptr_to(v.t, 1), addr_of(v));
      if (v.t->k == TY_CINT) v = coerce(v, t_i64); else if (v.t->k == TY_CFLOAT) v = coerce(v, t_f64);
      char *sl = slot(v.t); put(v, v.t, sl); return V(ptr_to(v.t, 1), sl);
    }
    Val v = rv(gen(n->a, s, ex));
    if (is_vec(v.t)) return vec_un(op, v);
    if (!strcmp(op, "!")) { v = coerce(v, t_bool); if (v.ck) { v.cv.i = !v.cv.i; return v; } char *r = tmp(); emit("%s =w ceqw %s, 0", r, opnd(v)); return V(t_bool, r); }
    if (v.ck && v.cv.k == CV_FLOAT) { v.cv.f = -v.cv.f; return v; }
    if (v.ck && v.cv.k == CV_INT) { if (op[0] == '~') { if (ex && v.t->k == TY_CINT) v = coerce(v, ex); v.cv.i = wrap_int(~v.cv.i, v.t); } else v.cv.i = wrap_int(-v.cv.i, v.t); return v; }
    if (is_wide(v.t)) { if (op[0] == '~') { char *a = tmp(), *b2 = tmp(); emit("%s =l xor %s, -1", a, wlo(v)); emit("%s =l xor %s, -1", b2, whi(v)); return w_from_parts(v.t, a, b2); } CVal z = {0}; z.k = CV_INT; z.t = v.t; return w_arith("-", v.t, CK(z), v); }
    if (is_bigf(v.t)) return V(v.t, bigf_op(8, v.t, opnd(v), NULL));
    char *r = tmp();
    if (op[0] == '~') { emit("%s =%c xor %s, -1", r, qc(v.t), opnd(v)); return V(v.t, norm(r, v.t)); }
    emit("%s =%c neg %s", r, qc(v.t), opnd(v)); return V(v.t, norm(r, v.t));
  }
  case N_BIN: {
    const char *op = n->s;
    if (!strcmp(op, "and") || !strcmp(op, "or")) return gen_logic(n, s);
    if (ceval(n, s, &c)) return CK(c);
    if (!strcmp(op, "||")) { c.k = CV_TYPE; c.t = t_errset; return CK(c); }
    if (!strcmp(op, "**")) { /* runtime repetition of a tuple / array */
      CVal cn; if (!ceval(n->b, s, &cn) || cn.k != CV_INT) die("%s:%d: ** count must be comptime-known", n->tok->file, n->tok->line);
      int64_t cnt = (int64_t)cn.i;
      Val a = rv(gen(n->a, s, NULL)); Type *t = a.t;
      if (is_tuple_type(t)) {
        layout(t->ct); int m = t->ct->fields.n; Vec names = {0}, types = {0}; int nct = 0; CVal **cts = xalloc(sizeof(CVal *) * (m * cnt + 1));
        for (int64_t r = 0; r < cnt; r++) for (int i = 0; i < m; i++) { Field *f = t->ct->fields.a[i]; int j = names.n;
          if (f->is_ct) { cts[j] = f->defcv; nct++; } vpush(&types, f->t); vpush(&names, fmt("%d", j)); }
        Type *rt = nct ? mk_anon_struct_cv(&names, &types, 1, cts) : mk_anon_struct(&names, &types, 1); char *sl = slot(rt);
        for (int64_t r = 0; r < cnt; r++) for (int i = 0; i < m; i++) { Field *f = t->ct->fields.a[i], *g = rt->ct->fields.a[r * m + i]; if (g->is_ct) continue;
          blit(addp(addr_of(a), f->off), addp(sl, g->off), (int)tsize(f->t)); }
        return V(rt, sl);
      }
      Type *at = t->k == TY_PTR ? t->elem : t; if (at->k != TY_ARRAY) die("%s:%d: runtime ** needs an array or tuple operand", n->tok->file, n->tok->line);
      char *src = t->k == TY_PTR ? opnd(a) : addr_of(a); int64_t bytes = tsize(at);
      Type *rt = array_of(at->elem, at->len * cnt, 0, 0); char *sl = slot(rt);
      for (int64_t r = 0; r < cnt; r++) blit(src, addp(sl, r * bytes), (int)bytes);
      return V(rt, sl);
    }
    if (!strcmp(op, "++")) {
      Val a = rv(gen(n->a, s, NULL)), b = rv(gen(n->b, s, NULL)); Type *et = NULL; Val *vs[2] = { &a, &b }; int64_t ln[2];
      for (int k = 0; k < 2; k++) { Type *t = vs[k]->t; if (t->k == TY_ARRAY) et = t->elem; else if (t->k == TY_PTR && t->elem->k == TY_ARRAY) et = t->elem->elem; }
      if (!et && is_tuple_type(a.t) && is_tuple_type(b.t)) { /* runtime tuple concatenation */
        Vec names = {0}, types = {0}, vals = {0}; layout(a.t->ct); layout(b.t->ct);
        int tot = a.t->ct->fields.n + b.t->ct->fields.n, nct = 0; CVal **cts = xalloc(sizeof(CVal *) * (tot + 1));
        for (int k = 0; k < 2; k++) { Container *c = vs[k]->t->ct;
          for (int i = 0; i < c->fields.n; i++) { Field *f = c->fields.a[i]; Val fv = rv(gen_member(*vs[k], f->name, n)); int j = names.n;
            if (fv.ck && (fv.cv.k == CV_ENUMLIT || fv.cv.k == CV_TYPE)) { cts[j] = xalloc(sizeof(CVal)); *cts[j] = fv.cv; nct++; }
            Val *pv = xalloc(sizeof *pv); *pv = fv; vpush(&vals, pv); vpush(&types, f->t); vpush(&names, fmt("%d", j)); } }
        Type *t = nct ? mk_anon_struct_cv(&names, &types, 1, cts) : mk_anon_struct(&names, &types, 1); char *sl = slot(t);
        for (int i = 0; i < vals.n; i++) { Field *f = t->ct->fields.a[i]; if (f->is_ct) continue; put(*(Val *)vals.a[i], f->t, addp(sl, f->off)); }
        return V(t, sl);
      }
      if (!et) die("%s:%d: runtime ++ needs array operands", n->tok->file, n->tok->line);
      char *src[2];
      for (int k = 0; k < 2; k++) { Type *t = vs[k]->t;
        if (t->k == TY_PTR && t->elem->k == TY_ARRAY) { ln[k] = t->elem->len; src[k] = opnd(*vs[k]); }
        else if (t->k == TY_ARRAY) { ln[k] = t->len; src[k] = addr_of(*vs[k]); }
        else { int64_t m = t->ct ? (layout(t->ct), t->ct->fields.n) : 0; Val c2 = coerce(*vs[k], array_of(et, m, 0, 0)); ln[k] = m; src[k] = addr_of(c2); } }
      Type *rt = array_of(et, ln[0] + ln[1], 0, 0); char *sl = slot(rt);
      blit(src[0], sl, (int)(ln[0] * tsize(et))); blit(src[1], addp(sl, ln[0] * tsize(et)), (int)(ln[1] * tsize(et)));
      return V(rt, sl);
    }
    int cmp = !strcmp(op, "==") || !strcmp(op, "!=") || !strcmp(op, "<") || !strcmp(op, ">") || !strcmp(op, "<=") || !strcmp(op, ">=");
    Val a = rv(gen(n->a, s, cmp ? NULL : ex));
    Type *bh = cmp ? (a.t->k == TY_CINT || a.t->k == TY_ENUMLIT ? NULL : a.t) : (a.t->k == TY_CINT ? ex : (a.t->k == TY_MPTR ? t_usize : a.t));
    if (bh && !cmp && (n->b->k == N_SWITCH || n->b->k == N_IF) && !in_typeof) { Type *bt = typeof_impl(n->b, s); if (bt && (bt->k == TY_INT || bt->k == TY_FLOAT) && bt != bh) bh = NULL; }
    Val b = rv(gen(n->b, s, bh));
    if (a.ck && a.t->k == TY_CINT && b.t->k == TY_CINT && !b.ck) a = coerce(a, t_i64);
    if (cmp && !a.ck && a.t->k == TY_INT && b.ck && b.cv.k == CV_INT) { CVal raw; if (ceval(n->b, s, &raw) && raw.k == CV_INT && cv_typeof(&raw)->k == TY_CINT) b = CK(raw); }
    if (cmp) return gen_cmp(op, a, b);
    if (a.t->k == TY_CINT && b.t->k == TY_CINT && ex && ex->k == TY_INT) { a = coerce(a, ex); b = coerce(b, ex); }
    return gen_arith(op, a, b);
  }
  case N_ASSIGN: gen_assign(n, s); return VOIDV();
  case N_DESTRUCT: gen_destruct(n, s); return VOIDV();
  case N_UNREACHABLE: emit("hlt"); term = 1; return NORET();
  case N_TRY: return gen_try(n, s, ex);
  case N_CATCH: return gen_catch(n, s, ex);
  case N_ORELSE: return gen_orelse(n, s, ex);
  case N_IF: {
    CVal cc;
    if (!n->cap && ceval(n->a, s, &cc) && cc.k == CV_BOOL) return gen_if(n, s, ex);
    if (n->cap && !n->capref && ceval(n->a, s, &cc) && cc.k != CV_UNDEF) {
      Scope *bs = new_scope(s, NULL);
      if (cc.k == CV_NULL) return n->c ? gen(n->c, s, ex) : VOIDV();
      if (cc.k == CV_ERR) { if (n->cap2) bind_cval(bs, n->cap2, cc); return n->c ? gen(n->c, bs, ex) : VOIDV(); }
      bind_cval(bs, n->cap, cc); return gen(n->b, bs, ex);
    }
    if (!n->cap && n->cap2) { Val cv = gen(n->a, s, NULL); if (cv.t->k == TY_ERRU) return gen_if_erru(n, s, ex, cv); }
    if (n->cap) { Val cv = gen(n->a, s, NULL); if (cv.t->k == TY_ERRU) return gen_if_erru(n, s, ex, cv);
      /* optional: re-dispatch with the already evaluated condition */
      Res R; memset(&R, 0, sizeof R); R.ex = ex; char *lt = newl(), *lf = newl(), *lx = newl();
      if_peer(&R, n, s, ex);
      Scope *ts = new_scope(s, NULL); char *pv = opt_is_ptr(cv.t) ? opnd(cv) : NULL;
      if (cv.t->k != TY_OPT) die("%s:%d: if capture needs optional or error union", n->tok->file, n->tok->line);
      if (cv.t->elem->k == TY_NORET) { if (n->c) return gen(n->c, s, ex); return VOIDV(); } /* ?noreturn is always null */
      if (pv) { char *h = tmp(); emit("%s =w cnel %s, 0", h, pv); br(h, lt, lf); } else br(opt_has(cv), lt, lf);
      label(lt); cap_bind(ts, n->cap, n->capref, opt_payload(cv, pv));
      { Val tv = gen(n->b, ts, n->c ? ex : NULL); res_put(&R, n->c || tv.t->k == TY_NORET ? tv : VOIDV()); } jmp(lx);
      label(lf); if (n->c) res_put(&R, gen(n->c, s, ex ? ex : R.collect ? NULL : R.t)); else res_put(&R, VOIDV());
      jmp(lx); label(lx); return res_get(&R);
    }
    return gen_if(n, s, ex);
  }
  case N_WHILE: if (n->flags & F_INLINE) return gen_inline_while(n, s, ex); return gen_while(n, s, ex);
  case N_FOR: if (n->flags & F_INLINE) return gen_inline_for(n, s, ex); return gen_for(n, s, ex);
  case N_SWITCH: return gen_switch(n, s, ex);
  case N_BLOCK: return gen_block(n, s, ex);
  case N_BREAK: {
    Loop *L = find_loop(n->label, 0);
    if (in_typeof) { int outer = 0; for (Loop *p = typeof_outer; p; p = p->up) if (p == L) outer = 1;
      if (outer) { if (n->a) { Val v = gen(n->a, s, L->res->ex ? L->res->ex : L->res->t); if (v.t->k == TY_NORET) return v; } jmp(L->brk); return NORET(); } }
    if (n->a) { Type *bx = L->res->ex ? L->res->ex : (L->res->collect || type_incomplete(L->res->t)) ? NULL : L->res->t; Val v = gen(n->a, s, bx); if (v.t->k == TY_NORET) return v; res_put(L->res, v); }
    else if (L->res) res_put(L->res, VOIDV());
    L->brk_used = 1; run_defers(L->dbase, NULL); jmp(L->brk); return NORET();
  }
  case N_CONTINUE: {
    Loop *L = n->label ? find_loop(n->label, 1) : find_loop(NULL, 1);
    if (L->kind == 2) { Val v = coerce(gen(n->a, s, L->swt), L->swt); put(v, L->swt, L->swslot); run_defers(L->dbase, NULL); jmp(L->swdisp); return NORET(); }
    L->cont_used = 1; run_defers(L->dbase, NULL); jmp(L->cont); return NORET();
  }
  case N_RETURN: return gen_return(n, s);
  case N_VAR: gen_vardecl(n, s); return VOIDV();
  case N_DEFER: case N_ERRDEFER: {
    Defer *d = xalloc(sizeof *d); d->n = n->a; d->err = n->k == N_ERRDEFER; d->s = s; d->cap = n->cap; vpush(&defers, d); return VOIDV();
  }
  case N_COMPTIME:
    if (n->a->k == N_UNREACHABLE) { if (!term) emit("hlt"); term = 1; return NORET(); }
    { int returned = 0; if (!ceval_ret(n->a, s, ex, fret, &c, &returned)) {
        /* lenient: valid Zig guarantees this is comptime-known; zb may lose comptime-ness (e.g. destructured
           comptime tuple fields), so evaluate plain calls/asserts at runtime instead */
        if (n->a->k == N_CALL || n->a->k == N_BUILTIN) { if (getenv("ZB_DBG")) fprintf(stderr, "zb: note: %s:%d: comptime expression evaluated at runtime\n", n->tok->file, n->tok->line); return gen(n->a, s, ex); }
        die("%s:%d: unable to evaluate comptime expression (at %s)", n->tok->file, n->tok->line, ct_fail_loc()); }
      if (returned) return ret_val(CK(c), c.k == CV_VOID); }
    { Val r = CK(c); if (ex && ck_ok(&c, ex)) r.t = ex; return r; }
  case N_FLOAT: { CVal fc = cv_float(n->fval, t_cfloat); Val fv = CK(fc); return ex && (is_float(ex) || (ex->k == TY_OPT && is_float(ex->elem))) ? coerce(fv, ex) : fv; }
  case N_ASM: return gen_asm(n, s);
  case N_FN: return VOIDV();
  default: die("%s:%d: cannot generate node kind %d", n->tok->file, n->tok->line, n->k);
  }
}

/* ---------- typeof via dry run ---------- */
static Type *typeof_ex(Node *n, Scope *s, Type *ex) {
  FILE *sfb = fb, *sab = ab; int st = term; Loop *sl = loops; int sdn = defers.n;
  if (!devnull) devnull = fopen("/dev/null", "w");
  Loop *sto = typeof_outer; typeof_outer = loops;
  in_typeof++; fb = ab = devnull; Val v = gen(n, s, ex); fb = sfb; ab = sab; term = st; loops = sl; defers.n = sdn; in_typeof--; typeof_outer = sto;
  return v.t;
}
static Type *typeof_impl(Node *n, Scope *s) {
  FILE *sfb = fb, *sab = ab; int st = term; Loop *sl = loops; int sdn = defers.n;
  if (!devnull) devnull = fopen("/dev/null", "w");
  Loop *sto = typeof_outer; typeof_outer = loops;
  in_typeof++; fb = ab = devnull; Val v = gen(n, s, NULL); fb = sfb; ab = sab; term = st; loops = sl; defers.n = sdn; in_typeof--; typeof_outer = sto;
  return v.t;
}

/* ---------- globals ---------- */
void gen_global(Decl *d) {
  Node *n = d->node; if (n->flags & F_EXTERN) return;
  CVal v = d->has_init ? d->cv : (CVal){ .k = CV_UNDEF };
  char *buf; size_t bsz; FILE *f = open_memstream(&buf, &bsz); int first = 1;
  ser(f, &first, &v, d->t); if (first) fputs("z 1", f); fclose(f);
  int al = talign(d->t); if (al < 1) al = 1; if (al > 16) al = 16;
  fprintf(db, "%sdata $%s = align %d { %s }\n", (n->flags & F_EXPORT) ? "export " : "", d->sym, al, buf); free(buf);
}

/* ---------- functions ---------- */
void queue_fn(FnInst *fi) { if (fi->queued || (fi->node->flags & F_EXTERN) || !fi->node->b) return; fi->queued = 1; vpush(&queue, fi); }
FnInst *gen_cur_fi;
void gen_fn(FnInst *fi) {
  { static int tr = -1; if (tr < 0) tr = getenv("ZB_TRACE_FN") != NULL; if (tr) { static int cnt; fprintf(stderr, "genfn %s\n", fi->sym);
#ifdef ZB_GC
    if (++cnt % 2000 == 0) { extern size_t GC_get_heap_size(void), GC_get_memory_use(void); struct mallinfo2 mi = mallinfo2(); fprintf(stderr, "mem fns=%d gcheap=%zuM gcuse=%zuM malloc=%zuM queue=%d\n", cnt, GC_get_heap_size() >> 20, GC_get_memory_use() >> 20, (mi.uordblks + mi.hblkhd) >> 20, queue.n); }
#endif
  } }
  gen_cur_fi = fi;
  if (dbg_on < 0) dbg_on = getenv("ZB_DBG") != NULL;
  dbg_line = 0; dbg_file = fi->node->tok ? fi->node->tok->file : NULL;
  char *fbuf, *abuf; size_t fsz, asz;
  fb = open_memstream(&fbuf, &fsz); ab = open_memstream(&abuf, &asz);
  term = 0; defers.n = 0; loops = NULL; fret = fi->ret; fsret = NULL;
  Node *f = fi->node; Scope *fs = new_scope(fi->scope, NULL);
  char params[4096]; int m = 0; params[0] = 0;
  if (is_aggr(fret)) { fsret = "%sret"; m += snprintf(params + m, sizeof params - m, "l %%sret"); }
  for (int i = 0; i < f->list.n; i++) {
    Node *p = f->list.a[i]; Type *t = fi->ptypes.a[i];
    if (!t || (p->flags & F_VARARGS)) continue;
    char *pn = fmt("%%p%d", i);
    if (tsize(t) == 0) { if (p->s) bind_local(fs, p->s, t, "0"); continue; }
    m += snprintf(params + m, sizeof params - m, "%s%c %s", m ? ", " : "", qc(t), pn);
    if (!p->s) continue;
    if (is_aggr(t)) bind_local(fs, p->s, t, pn);
    else { char *sl = slot(t); store(t, pn, sl); bind_local(fs, p->s, t, sl); }
  }
  gen_block(f->b, fs, NULL);
  if (!term) {
    if (fret->k == TY_ERRU) { store(t_u16, "0", fsret); emit("ret"); }
    else if (fret->k == TY_VOID || is_aggr(fret) || tsize(fret) == 0) emit("ret");
    else emit("hlt");
  }
  fclose(fb); fclose(ab);
  char rc = (fret->k == TY_VOID || fret->k == TY_NORET || is_aggr(fret) || tsize(fret) == 0) ? 0 : qc(fret);
  if (dbg_on && dbg_file) { char *rp = realpath(dbg_file, NULL); fprintf(outf, "dbgfile \"%s\"\n", rp ? rp : dbg_file); free(rp); }
  fprintf(outf, "%sfunction %s%c $%s(%s) {\n@start\n%s%s}\n\n", (f->flags & F_EXPORT) ? "export " : "", rc ? "" : "", rc ? rc : ' ', fi->sym, params, abuf, fbuf);
  free(fbuf); free(abuf);
}
void gen_init_buffers(void) { fprintf(outf, "type :zbw = { l, l }\n"); db = tmpfile(); xb = tmpfile(); if (!db || !xb) die("cannot create temp files"); typeof_hook = typeof_impl; }
void gen_all(void) { for (int i = 0; i < queue.n; i++) { FnInst *fi = queue.a[i]; if (!fi->done) { fi->done = 1; gen_fn(fi); } } }
void gen_main_wrapper(FnInst *mi, int glue) {
  Type *r = mi->ret;
  if (glue) { fprintf(outf, "export function w $main(w %%argc, l %%argv, l %%envp) {\n@start\n\tstorew %%argc, $zb.argc\n\tstorel %%argv, $zb.argv\n\t%%a =l extsw %%argc\n\t%%r =w call $%s(l %%a, l %%argv, l %%envp)\n\tret %%r\n}\n", mi->sym); return; }
  fprintf(outf, "export function w $main(w %%argc, l %%argv) {\n@start\n\tstorew %%argc, $zb.argc\n\tstorel %%argv, $zb.argv\n");
  if (r->k == TY_VOID || r->k == TY_NORET) fprintf(outf, "\tcall $%s()\n\tret 0\n}\n", mi->sym);
  else if (r->k == TY_INT) fprintf(outf, "\t%%r =w call $%s()\n\tret %%r\n}\n", mi->sym);
  else if (r->k == TY_ERRU) {
    fprintf(outf, "\t%%e =l alloc8 %d\n\tcall $%s(l %%e)\n\t%%c =w loaduh %%e\n\tjnz %%c, @err, @ok\n@err\n\tcall $zb.errexit(w %%c)\n\tret 1\n@ok\n", tsize(r) < 8 ? 8 : tsize(r), mi->sym);
    if (r->elem->k == TY_INT) fprintf(outf, "\t%%p =l add %%e, %d\n\t%%v =w loadub %%p\n\tret %%v\n}\n", erru_off(r)); else fprintf(outf, "\tret 0\n}\n");
  } else die("unsupported main return type %s", tname(r));
}
void gen_finish(void) {
  fprintf(db, "export data $zb.argc = align 4 { w 0 }\nexport data $zb.argv = align 8 { l 0 }\n");
  char **syms = xalloc(sizeof(char *) * (errnames.n + 1));
  for (int i = 0; i < errnames.n; i++) { char *s = errnames.a[i]; syms[i] = strdata(s, strlen(s)); }
  fprintf(db, "data $zb.errnames = align 8 { l 0, l 0");
  for (int i = 0; i < errnames.n; i++) fprintf(db, ", l %s, l %d", syms[i], (int)strlen((char *)errnames.a[i]));
  fprintf(db, " }\n");
  fprintf(db, "data $zb.pm = { b \"panic: \" }\ndata $zb.em = { b \"error: \" }\ndata $zb.nl = { b 10 }\n");
  fprintf(xb, "function $zb.panic(l %%p, l %%n) {\n@start\n\tcall $write(w 2, l $zb.pm, l 7)\n\tcall $write(w 2, l %%p, l %%n)\n\tcall $write(w 2, l $zb.nl, l 1)\n\tcall $abort()\n\thlt\n}\n");
  fprintf(xb, "function $zb.errexit(w %%c) {\n@start\n\t%%w =l extuw %%c\n\t%%o =l mul %%w, 16\n\t%%a =l add $zb.errnames, %%o\n\t%%p =l loadl %%a\n\t%%a2 =l add %%a, 8\n\t%%n =l loadl %%a2\n\tcall $write(w 2, l $zb.em, l 7)\n\tcall $write(w 2, l %%p, l %%n)\n\tcall $write(w 2, l $zb.nl, l 1)\n\tret\n}\n");
  { FILE *fs[2] = { xb, db }; char buf[65536]; size_t k;
    for (int i = 0; i < 2; i++) { rewind(fs[i]); while ((k = fread(buf, 1, sizeof buf, fs[i])) > 0) fwrite(buf, 1, k, outf); fclose(fs[i]); } }
}
