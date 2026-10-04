#include "gen_int.h"

void emit(const char *f, ...) {
  if (term) {
    fprintf(fb, "@L%d\n", ++lblc);
    term = 0;
  }
  if (dbg_on) {
    Node *cn = gen_cur_pub();
    if (cn && cn->tok && cn->tok->file == dbg_file && cn->tok->line != dbg_line) {
      dbg_line = cn->tok->line;
      fprintf(fb, "\tdbgloc %d\n", dbg_line);
    }
  }
  if (!strcmp(f, "hlt") && getenv("ZB_TRAPLOC")) {
    Node *cn = gen_cur_pub();
    char *m = fmt("trap at %s:%d\n", cn ? cn->tok->file : "?", cn ? cn->tok->line : 0);
    fprintf(fb, "\tcall $zb_trapbt(l %s, l %d)\n", strdata(m, (int)strlen(m)), (int)strlen(m));
  }
  va_list ap;
  va_start(ap, f);
  fputc('\t', fb);
  vfprintf(fb, f, ap);
  fputc('\n', fb);
  va_end(ap);
}
char *newl(void) {
  return fmt("L%d", ++lblc);
}
void label(char *l) {
  fprintf(fb, "@%s\n", l);
  term = 0;
}
void jmp(char *l) {
  if (!term) emit("jmp @%s", l);
  term = 1;
}
void br(char *c, char *a, char *b) {
  emit("jnz %s, @%s, @%s", c, a, b);
  term = 1;
}
char *tmp(void) {
  return fmt("%%t%d", ++tmpc);
}
char qc(Type *t) {
  if (t->k == TY_FLOAT) {
    if (t->bits == 32) return 's';
    if (t->bits == 64) return 'd';
    return t->bits == 16 ? 's' : 'l'; /* f16 in 's', f80/f128 in 'd' registers; memory via zbrt shims */
  }
  if (t->k == TY_CFLOAT) return 'd';
  if (is_aggr(t)) return 'l';
  return tsize(t) == 8 ? 'l' : 'w';
}
char *slot(Type *t) {
  char *n = tmp();
  int a = talign(t), s = tsize(t);
  if (s < 1) s = 1;
  fprintf(ab, "\t%s =l alloc%d %d\n", n, a >= 16 ? 16 : a > 4 ? 8 : 4, s);
  return n;
}
void blit(char *src, char *dst, int n) {
  if (n > 0) emit("blit %s, %s, %d", src, dst, n);
}
char *load(Type *t, char *addr) {
  int s = tsize(t);
  if (!s) return "0";
  int sg = t->k == TY_INT && t->sign;
  char *r = tmp();
  const char *ins = s == 1   ? (sg ? "loadsb" : "loadub")
                    : s == 2 ? (sg ? "loadsh" : "loaduh")
                    : s == 4 ? "loadw"
                             : "loadl";
  if (t->k == TY_FLOAT && t->bits > 64) {
    char *sl = slot(t);
    blit(addr, sl, 16);
    return sl;
  }
  if (t->k == TY_FLOAT && t->bits != 32 && t->bits != 64) {
    emit("%s =%c call $zb_ldf%d(l %s)", r, qc(t), t->bits, addr);
    return r;
  }
  if (t->k == TY_FLOAT) ins = qc(t) == 's' ? "loads" : "loadd";
  emit("%s =%c %s %s", r, qc(t), ins, addr);
  return r;
}
void store(Type *t, char *v, char *addr) {
  int s = tsize(t);
  if (!s) return;
  if (t->k == TY_FLOAT && t->bits > 64) {
    blit(v, addr, 16);
    return;
  }
  if (t->k == TY_FLOAT && t->bits != 32 && t->bits != 64) {
    emit("call $zb_stf%d(l %s, %c %s)", t->bits, addr, qc(t), v);
    return;
  }
  if (t->k == TY_FLOAT) {
    emit("store%c %s, %s", qc(t), v, addr);
    return;
  }
  emit("store%s %s, %s", s == 1 ? "b" : s == 2 ? "h" : s == 4 ? "w" : "l", v, addr);
}
char *addp(char *a, int64_t off) {
  if (!off) return a;
  char *r = tmp();
  emit("%s =l add %s, %lld", r, a, (long long)off);
  return r;
}
char *norm(char *v, Type *t) {
  if (t->k != TY_INT) return v;
  int b = t->bits;
  char c = qc(t);
  if (b == 32 || b == 64) return v;
  char *r = tmp();
  if (b == 8)
    emit("%s =w %s %s", r, t->sign ? "extsb" : "extub", v);
  else if (b == 16)
    emit("%s =w %s %s", r, t->sign ? "extsh" : "extuh", v);
  else if (!t->sign)
    emit("%s =%c and %s, %llu", r, c, v, (unsigned long long)((1ULL << b) - 1));
  else {
    char *q = tmp();
    int sh = (c == 'w' ? 32 : 64) - b;
    emit("%s =%c shl %s, %d", q, c, v, sh);
    emit("%s =%c sar %s, %d", r, c, q, sh);
  }
  return r;
}

/* ---------- values ---------- */
Val V(Type *t, char *op) {
  Val v;
  memset(&v, 0, sizeof v);
  v.t = t;
  v.op = op;
  return v;
}
Val LV(Type *t, char *a) {
  Val v = V(t, a);
  v.lv = 1;
  return v;
}
Val VOIDV(void) {
  return V(t_void, "0");
}
Val NORET(void) {
  return V(t_noret, "0");
}
Val CK(CVal c) {
  Val v;
  memset(&v, 0, sizeof v);
  v.ck = 1;
  v.cv = c;
  v.t = cv_typeof(&c);
  if (c.k == CV_VOID) {
    v.ck = 0;
    v.op = "0";
  }
  return v;
}
int is_ctonly(Type *t) {
  return t->k == TY_CINT || t->k == TY_CFLOAT || t->k == TY_TYPE || t->k == TY_ENUMLIT || t->k == TY_NULL ||
         t->k == TY_UNDEF || t->k == TY_ANYTYPE;
}

void data_bytes(FILE *f, const char *s, int n) {
  int instr = 0, any = 0;
  for (int i = 0; i < n; i++) {
    unsigned char c = s[i];
    if (c >= 32 && c < 127 && c != '"' && c != '\\') {
      if (!instr) {
        fprintf(f, "%sb \"", any ? ", " : "");
        instr = 1;
      }
      fputc(c, f);
    } else {
      if (instr) {
        fputc('"', f);
        instr = 0;
      }
      fprintf(f, "%sb %d", any ? ", " : "", c);
    }
    any = 1;
  }
  if (instr) fputc('"', f);
}
char *strdata(const char *s, int n) {
  char *nm = fmt("$zbs%d", ++strc);
  fprintf(db, "data %s = { ", nm);
  data_bytes(db, s, n);
  fprintf(db, "%sb 0 }\n", n ? ", " : "");
  return nm;
}
char *pm_get(void *k) {
  if (!pm_cap) return NULL;
  unsigned h = (unsigned)(((uintptr_t)k >> 4) * 2654435761u) & (pm_cap - 1);
  while (pm_k[h]) {
    if (pm_k[h] == k) return pm_v[h];
    h = (h + 1) & (pm_cap - 1);
  }
  return NULL;
}
void pm_put(void *k, char *v) {
  if (pm_n * 2 >= pm_cap) {
    int oc = pm_cap;
    void **ok = pm_k;
    char **ov = pm_v;
    pm_cap = oc ? oc * 2 : 256;
    pm_k = xalloc(sizeof(void *) * pm_cap);
    pm_v = xalloc(sizeof(char *) * pm_cap);
    pm_n = 0;
    for (int i = 0; i < oc; i++)
      if (ok[i]) pm_put(ok[i], ov[i]);
  }
  unsigned h = (unsigned)(((uintptr_t)k >> 4) * 2654435761u) & (pm_cap - 1);
  while (pm_k[h]) h = (h + 1) & (pm_cap - 1);
  pm_k[h] = k;
  pm_v[h] = v;
  pm_n++;
}
void ditem(FILE *f, int *first, const char *fm, ...) {
  if (!*first) fputs(", ", f);
  *first = 0;
  va_list ap;
  va_start(ap, fm);
  vfprintf(f, fm, ap);
  va_end(ap);
}
void dz(FILE *f, int *first, int64_t n) {
  if (n > 0) ditem(f, first, "z %lld", (long long)n);
}
void ser_int(FILE *f, int *first, int sz, i128 v) {
  if (sz <= 0) return;
  if (sz <= 8) {
    ditem(f, first, "%c %lld", sz == 1 ? 'b' : sz == 2 ? 'h' : sz == 4 ? 'w' : 'l', (long long)(int64_t)v);
    return;
  }
  for (int i = 0; i < sz / 8; i++)
    ditem(f, first, "l %lld", (long long)(int64_t)(i < 2 ? (v >> (64 * i)) : (v < 0 ? -1 : 0)));
}
char *str_sym(CVal *sc) {
  char *nm = pm_get(sc);
  if (nm) return nm;
  nm = strdata(sc->s, sc->slen);
  pm_put(sc, nm);
  return nm;
}
/* address of a comptime pointer as symbol + offset */
char *ptr_parts(CVal *p, int64_t *off) {
  *off = 0;
  if (p->k == CV_STR) return strdata(p->s, p->slen);
  if (!p->base) {
    if (p->s) {
      *off = (int64_t)p->i;
      return fmt("$%s", p->s);
    }
    return NULL;
  }
  CVal *b = p->base;
  if (b->k == CV_STR) {
    *off = p->idx < 0 ? 0 : p->idx;
    return str_sym(b);
  }
  Type *bt = cv_typeof(b);
  if (bt->k == TY_CINT || bt->k == TY_UNDEF)
    bt = p->t && (p->t->k == TY_PTR || p->t->k == TY_MPTR || p->t->k == TY_SLICE) ? p->t->elem : t_i64;
  if (p->idx >= 0) {
    Type *et = bt->k == TY_ARRAY ? bt->elem : bt;
    *off = p->idx * tsize(et);
  }
  int fi;
  CVal *par;
  while ((par = cell_parent(b, &fi))) {
    Type *pt = cv_typeof(par);
    if (!pt || (pt->k != TY_STRUCT && pt->k != TY_UNION)) break;
    if (fi >= 0) {
      layout(pt->ct);
      *off += ((Field *)pt->ct->fields.a[fi])->off;
    }
    b = par;
    bt = pt;
  }
  return cell_sym(b, bt);
}
void ser_ptr(FILE *f, int *first, CVal *v) {
  int64_t off;
  char *sym;
  switch (v->k) {
  case CV_PTR:
  case CV_SLICE:
  case CV_STR:
    sym = ptr_parts(v, &off);
    if (!sym) {
      ditem(f, first, "l 0");
      return;
    }
    if (off)
      ditem(f, first, "l %s + %lld", sym, (long long)off);
    else
      ditem(f, first, "l %s", sym);
    return;
  case CV_FN: ditem(f, first, "l $%s", plain_inst(v->fn)->sym); return;
  case CV_INT:
  case CV_NULL:
  case CV_UNDEF: ditem(f, first, "l %lld", (long long)(int64_t)v->i); return;
  default: die("cannot materialize comptime value kind %d as a pointer", v->k);
  }
}
void ser(FILE *f, int *first, CVal *v, Type *t) {
  int sz = tsize(t);
  if (sz <= 0 || type_is_ctonly(t)) return;
  if (v->k == CV_UNDEF || v->k == CV_NONE) {
    dz(f, first, sz);
    return;
  }
  switch (t->k) {
  case TY_INT:
  case TY_BOOL:
  case TY_ERRSET:
  case TY_ENUM:
    if (v->k == CV_AGG && t->k == TY_ENUM && v->t->k == TY_UNION) {
      ser_int(f, first, sz, ((Field *)v->t->ct->fields.a[v->i])->val);
      return;
    }
    ser_int(f, first, sz, v->i);
    return;
  case TY_PTR:
  case TY_MPTR:
  case TY_FN: ser_ptr(f, first, v); return;
  case TY_FLOAT: ser_int(f, first, sz, f_to_bits(v->k == CV_FLOAT ? v->f : (f128)v->i, t->bits)); return;
  case TY_OPT:
    if (v->k == CV_NULL) {
      dz(f, first, sz);
      return;
    }
    if (opt_is_ptr(t)) {
      ser_ptr(f, first, v);
      return;
    }
    ser(f, first, v, t->elem);
    ditem(f, first, "b 1");
    dz(f, first, sz - tsize(t->elem) - 1);
    return;
  case TY_ERRU:
    if (v->k == CV_ERR) {
      ser_int(f, first, 2, v->i);
      dz(f, first, sz - 2);
      return;
    }
    ser_int(f, first, 2, 0);
    dz(f, first, erru_off(t) - 2);
    ser(f, first, v, t->elem);
    dz(f, first, sz - erru_off(t) - tsize(t->elem));
    return;
  case TY_SLICE: {
    int64_t len = v->k == CV_STR ? v->slen : v->k == CV_SLICE ? v->slen : 0;
    if (v->k == CV_PTR && v->t && v->t->k == TY_PTR && v->t->elem->k == TY_ARRAY) len = v->t->elem->len;
    ser_ptr(f, first, v);
    ditem(f, first, "l %lld", (long long)len);
    return;
  }
  case TY_ARRAY: {
    int es = tsize(t->elem);
    int64_t w = 0;
    if (v->k == CV_STR) {
      int n = v->slen < t->len ? v->slen : (int)t->len;
      if (n > 0) {
        if (!*first) fputs(", ", f);
        *first = 0;
        data_bytes(f, v->s, n);
      }
      w = n;
    } else if (v->k == CV_AGG) {
      for (int i = 0; i < v->n && i < t->len; i++) ser(f, first, v->el[i], t->elem);
      w = (int64_t)(v->n < t->len ? v->n : t->len) * es;
    } else if (v->k == CV_INT || v->k == CV_BOOL) {
      for (int64_t i = 0; i < t->len; i++) ser(f, first, v, t->elem);
      w = t->len * es;
    } else
      die("cannot materialize comptime value kind %d as %s", v->k, tname(t));
    if (t->hassent && w == t->len * es) {
      ser_int(f, first, es, t->sent);
      w += es;
    }
    dz(f, first, sz - w);
    return;
  }
  case TY_STRUCT:
  case TY_TUPLE: {
    if (v->k != CV_AGG) die("cannot materialize comptime value kind %d as %s", v->k, tname(t));
    layout(t->ct);
    if (is_packed(t)) {
      ser_int(f, first, sz, cv_pack(v));
      return;
    }
    int pos = 0;
    for (int i = 0; i < t->ct->fields.n && i < v->n; i++) {
      Field *fl = t->ct->fields.a[i];
      if (type_is_ctonly(fl->t) || !tsize(fl->t)) continue;
      dz(f, first, fl->off - pos);
      ser(f, first, v->el[i], fl->t);
      pos = fl->off + tsize(fl->t);
    }
    dz(f, first, sz - pos);
    return;
  }
  case TY_UNION: {
    if (v->k != CV_AGG || v->i < 0) {
      dz(f, first, sz);
      return;
    }
    layout(t->ct);
    Field *fl = t->ct->fields.a[v->i];
    int ps = type_is_ctonly(fl->t) ? 0 : tsize(fl->t);
    if (ps) ser(f, first, v->el[0], fl->t);
    if (t->ct->tagged) {
      int to = union_tag_off(t);
      dz(f, first, to - ps);
      ser_int(f, first, tsize(t->ct->tag), fl->val);
      dz(f, first, sz - to - tsize(t->ct->tag));
    } else
      dz(f, first, sz - ps);
    return;
  }
  default: dz(f, first, sz); return;
  }
}
char *emit_data(CVal *v, Type *t, char *nm) {
  char *buf;
  size_t bsz;
  FILE *f = open_memstream(&buf, &bsz);
  int first = 1;
  ser(f, &first, v, t);
  if (first) fputs("z 1", f);
  fclose(f);
  int al = talign(t);
  if (al < 1) al = 1;
  if (al > 16) al = 16;
  fprintf(db, "data %s = align %d { %s }\n", nm, al, buf);
  free(buf);
  return nm;
}
char *cell_sym(CVal *cell, Type *t) {
  char *nm = pm_get(cell);
  if (nm) return nm;
  nm = fmt("$zbc%d", ++datac);
  pm_put(cell, nm);
  return emit_data(cell, t, nm);
}
char *cv_data(CVal *v, Type *t) {
  return emit_data(v, t, fmt("$zbc%d", ++datac));
}
int ck_ok(CVal *r, Type *to) {
  if (r->k == CV_UNDEF) return 1;
  switch (to->k) {
  case TY_OPT: return r->k == CV_NULL || ck_ok(r, to->elem);
  case TY_ERRU: return r->k == CV_ERR || ck_ok(r, to->elem);
  case TY_INT:
  case TY_CINT: return r->k == CV_INT;
  case TY_FLOAT:
  case TY_CFLOAT: return r->k == CV_FLOAT;
  case TY_ENUM: return r->k == CV_INT;
  case TY_BOOL: return r->k == CV_BOOL;
  case TY_ERRSET: return r->k == CV_ERR;
  case TY_TYPE: return r->k == CV_TYPE;
  case TY_VOID: return r->k == CV_VOID;
  case TY_PTR:
  case TY_MPTR:
    return r->k == CV_PTR || r->k == CV_STR || r->k == CV_INT || r->k == CV_FN ||
           (r->k == CV_SLICE && to->k == TY_MPTR);
  case TY_SLICE:
    return r->k == CV_SLICE || r->k == CV_STR ||
           (r->k == CV_PTR && r->t && r->t->k == TY_PTR && r->t->elem->k == TY_ARRAY);
  case TY_ARRAY:
  case TY_STRUCT:
  case TY_UNION:
  case TY_TUPLE: return r->k == CV_AGG && (r->t == to || (tsize(r->t) == tsize(to) && r->t->k == to->k));
  case TY_FN: return r->k == CV_FN;
  case TY_ENUMLIT: return r->k == CV_ENUMLIT;
  case TY_NULL: return r->k == CV_NULL;
  default: return 0;
  }
}
FnInst *plain_inst(Decl *d) {
  Vec c = {0};
  for (int i = 0; i < d->node->list.n; i++) vpush(&c, NULL);
  FnInst *fi = fn_instance(d, &c);
  queue_fn(fi);
  return fi;
}
char *mat(Val v) {
  if (!v.ck) return v.op;
  if (v.t && v.t->k == TY_FLOAT && v.t->bits > 64 && (v.cv.k == CV_FLOAT || v.cv.k == CV_INT))
    return cv_data(&v.cv, v.t);
  switch (v.cv.k) {
  case CV_INT:
  case CV_BOOL:
  case CV_ERR: return fmt("%lld", (long long)v.cv.i);
  case CV_NULL:
  case CV_UNDEF: return "0";
  case CV_FLOAT: {
    Type *t = v.t && v.t->k == TY_FLOAT ? v.t : t_f64;
    return qc(t) == 's' ? fmt("s_%a", (double)(float)v.cv.f) : fmt("d_%a", (double)v.cv.f);
  }
  case CV_FN: return fmt("$%s", plain_inst(v.cv.fn)->sym);
  case CV_STR: return strdata(v.cv.s, v.cv.slen);
  case CV_PTR:
  case CV_SLICE: {
    int64_t off;
    char *sym = ptr_parts(&v.cv, &off);
    if (!sym) return fmt("%lld", (long long)off);
    return addp(sym, off);
  }
  case CV_ENUMLIT: die("enum literal .%s has no result type", v.cv.s);
  case CV_TYPE: die("type %s used as a runtime value", tname(v.cv.t));
  default: {
    Node *cn = gen_cur_pub();
    die("%s:%d: cannot use comptime value (kind %d, %s) at runtime", cn ? cn->tok->file : "?", cn ? cn->tok->line : 0,
        v.cv.k, tname(v.t));
  }
  }
}
Type *host_int(int bytes) {
  return int_type(bytes * 8, 0);
}
