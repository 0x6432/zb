#include "gen_int.h"

int param_ct(Node *p) {
  return (p->flags & F_COMPTIME) || (p->a && p->a->k == N_IDENT && !strcmp(p->a->s, "type"));
}
char *argtxt(Val v, Type *t) {
  if (tsize(t) == 0) return NULL;
  if (is_aggr(t)) return fmt("l %s", addr_of(v));
  return fmt("%c %s", qc(t), opnd(v));
}
Val do_call(char *callee, Vec *args, Type *ret, int ext) {
  char buf[4096];
  int m = 0;
  buf[0] = 0;
  char *sl = NULL;
  if (is_aggr(ret)) {
    sl = slot(ret);
    m += snprintf(buf + m, sizeof buf - m, "l %s", sl);
  }
  for (int i = 0; i < args->n; i++)
    if (args->a[i]) m += snprintf(buf + m, sizeof buf - m, "%s%s", m ? ", " : "", (char *)args->a[i]);
  if (ret->k == TY_VOID || ret->k == TY_NORET || sl || tsize(ret) == 0) {
    emit("call %s(%s)", callee, buf);
    if (ret->k == TY_NORET) {
      emit("hlt");
      term = 1;
      return NORET();
    }
    if (sl) return V(ret, sl);
    return ret->k == TY_VOID ? VOIDV() : V(ret, "0");
  }
  char *r = tmp();
  emit("%s =%c call %s(%s)", r, qc(ret), callee, buf);
  if (ext && (ret->k == TY_BOOL || (ret->k == TY_INT && ret->bits < 32))) r = norm(r, ret->k == TY_BOOL ? t_u8 : ret);
  return V(ret, r);
}
Val gen_inline_body(FnInst *fi, Val *vals) {
  if (getenv("ZB_INLDBG")) fprintf(stderr, "inline %s\n", fi->d->name);
  Node *f = fi->node;
  Scope *fs = new_scope(fi->scope, NULL);
  for (int i = 0; i < f->list.n; i++) {
    Node *p = f->list.a[i];
    Type *t = fi->ptypes.a[i];
    if (!t || !p->s) continue;
    Val v = vals[i];
    if (v.ck && v.cv.k != CV_UNDEF) {
      bind_cval(fs, p->s, ccoerce(v.cv, t));
      continue;
    }
    v = rv(v);
    if (tsize(t) == 0) {
      bind_local(fs, p->s, t, "0");
      continue;
    }
    char *sl = slot(t);
    put(v, t, sl);
    bind_local(fs, p->s, t, sl);
  }
  Type *sfret = fret;
  Loop *sl = loops;
  Inl *si = inl;
  int sdn = defers.n;
  Res R;
  memset(&R, 0, sizeof R);
  R.ex = fi->ret;
  Inl I;
  memset(&I, 0, sizeof I);
  I.res = &R;
  I.lx = newl();
  I.dbase = defers.n;
  I.allck = 1;
  I.level = in_typeof;
  fret = fi->ret;
  loops = NULL;
  inl = &I;
  gen_block(f->b, fs, NULL);
  if (!term) {
    run_defers(I.dbase, NULL);
    if (!term) {
      if (fret->k == TY_ERRU) {
        char *e = slot(fret);
        store(t_u16, "0", e);
        res_put(&R, V(fret, e));
        I.allck = 0;
        I.nret++;
      } else if (fret->k == TY_VOID) {
        res_put(&R, VOIDV());
        I.nret++;
        if (I.nret > 1) I.allck = 0;
        I.ckv = cv_void();
      } else
        emit("hlt");
      jmp(I.lx);
    }
  }
  fret = sfret;
  loops = sl;
  inl = si;
  defers.n = sdn;
  label(I.lx);
  if (!R.has) {
    if (!term) emit("hlt");
    term = 1;
    return NORET();
  }
  term = 0;
  Val r = res_get(&R);
  if (I.allck && I.nret > 0 && fi->ret->k != TY_VOID && I.ckv.k != CV_VOID) {
    Val c = CK(I.ckv);
    c.t = fi->ret;
    return c;
  }
  return r;
}
Val gen_call(Node *n, Scope *s, Type *ex) {
  Node *cal = n->a;
  Decl *fd = NULL;
  Val self;
  int has_self = 0;
  Val fnv;
  memset(&fnv, 0, sizeof fnv);
  memset(&self, 0, sizeof self);
  if (cal->k == N_FIELD) {
    Val base;
    int got = 0;
    { /* method with a comptime self parameter: evaluate the receiver at comptime instead of generating it */
      Type *bt = typeof_impl(cal->a, s);
      if (bt && bt->k == TY_PTR) bt = bt->elem;
      if (bt && bt->k != TY_TYPE && bt->ct) {
        Decl *d = find_decl(bt->ct, cal->s);
        if (d) {
          resolve_decl(d);
          Decl *fdd = d->kind == D_FN || (d->kind == D_CONST && d->cv.k == CV_FN) ? d->cv.fn : NULL;
          if (fdd && fdd->node && fdd->node->list.n && param_ct(fdd->node->list.a[0])) {
            CVal cv;
            if (ceval_force(cal->a, s, &cv)) {
              base = CK(cv);
              got = 1;
            }
          }
        }
      }
    }
    if (!got) base = gen(cal->a, s, NULL);
    if (base.ck && base.cv.k == CV_TYPE) {
      CVal m;
      if (!ceval_member(base.cv, cal->s, &m))
        die("%s:%d: no decl '%s' in %s", n->tok->file, n->tok->line, cal->s, tname(base.cv.t));
      fnv = CK(m);
    } else {
      Type *ct = base.t->k == TY_PTR ? base.t->elem : base.t;
      Decl *d = ct->ct ? find_decl(ct->ct, cal->s) : NULL;
      if (d) {
        resolve_decl(d);
        if (d->kind == D_FN || (d->kind == D_CONST && d->cv.k == CV_FN)) {
          fd = d->cv.fn;
          has_self = 1;
          self = base;
        } else
          fnv = gen_member(base, cal->s, cal);
      } else
        fnv = gen_member(base, cal->s, cal);
    }
  } else if (cal->k == N_ENUMLIT && ex) {
    Type *bt = ex;
    while (bt->k == TY_OPT || bt->k == TY_ERRU || bt->k == TY_PTR) bt = bt->elem;
    Decl *d = bt->ct ? find_decl(bt->ct, cal->s) : NULL;
    if (!d) die("%s:%d: no decl '%s' in %s", n->tok->file, n->tok->line, cal->s, tname(bt));
    resolve_decl(d);
    fnv = CK(d->cv);
  } else
    fnv = gen(cal, s, NULL);
  if (!fd && fnv.ck && fnv.cv.k == CV_FN) fd = fnv.cv.fn;
  if (fd) {
    Node *f = fd->node;
    if (fn_returns_ctonly(fd)) {
      CVal r;
      if (!ceval_force(n, s, &r))
        die("%s:%d: cannot evaluate call to %s at comptime (at %s)", n->tok->file, n->tok->line, fd->name,
            ct_fail_loc());
      return CK(r);
    }
    if (fn_takes_ctonly(fd)) {
      CVal r;
      if (ceval_force(n, s, &r)) return CK(r);
      if (getenv("ZB_CT_TRACE"))
        fprintf(stderr, "ctonly call failed %s:%d (%s)\n", n->tok->file, n->tok->line, ct_fail_loc());
    }
    Scope *pscope = new_scope(fd->ct->scope, NULL);
    Vec cargs = {0};
    int np = f->list.n;
    Val *pre = xalloc(sizeof(Val) * (np + n->list.n + 2));
    char *haspre = xalloc(np + n->list.n + 2);
    for (int i = 0; i < np; i++) {
      Node *p = f->list.a[i];
      int ai = i - has_self;
      if (p->flags & F_VARARGS) {
        vpush(&cargs, NULL);
        break;
      }
      if (i == 0 && has_self) {
        if (p->flags & F_ANYTYPE) {
          CVal *c = xalloc(sizeof *c);
          c->k = CV_TYPE;
          c->t = self.t;
          c->slen = -1;
          vpush(&cargs, c);
          pre[i] = self;
          haspre[i] = 1;
          if (p->s) bind_placeholder(pscope, p->s, self.t);
        } else if (param_ct(p)) { /* comptime self parameter */
          CVal *c = xalloc(sizeof *c);
          Type *pt = NULL;
          if (p->a) {
            CVal tv;
            if (ceval_force(p->a, pscope, &tv) && tv.k == CV_TYPE) pt = tv.t;
          }
          if (self.ck)
            *c = self.cv;
          else if (!ceval_force(cal->a, s, c))
            die("%s:%d: comptime self argument is not comptime-known (at %s)", n->tok->file, n->tok->line,
                ct_fail_loc());
          if (pt && pt->k == TY_PTR && c->k != CV_PTR) {
            CVal pv = {0};
            pv.k = CV_PTR;
            pv.base = xalloc(sizeof(CVal));
            *pv.base = *c;
            pv.idx = -1;
            pv.t = pt;
            *c = pv;
          } else if (pt && pt->k != TY_PTR && c->k == CV_PTR) {
            CVal pv;
            if (ceval_force(cal->a, s, &pv)) *c = pv;
          }
          if (pt) *c = ccoerce(*c, pt);
          if (p->s) bind_cval(pscope, p->s, *c);
          vpush(&cargs, c);
        } else
          vpush(&cargs, NULL);
        continue;
      }
      Node *an = n->list.a[ai];
      if (param_ct(p)) {
        CVal *c = xalloc(sizeof *c);
        Type *pt = NULL;
        if (p->a) {
          CVal tv;
          if (ceval_force(p->a, pscope, &tv) && tv.k == CV_TYPE) pt = tv.t;
        }
        if (!ceval_rt(an, s, pt, c))
          die("%s:%d: comptime argument is not comptime-known (at %s)", an->tok->file, an->tok->line, ct_fail_loc());
        if (pt) *c = ccoerce(*c, pt);
        if (p->s) bind_cval(pscope, p->s, *c);
        vpush(&cargs, c);
        continue;
      }
      if (p->flags & F_ANYTYPE) {
        Val v = rv(gen(an, s, NULL));
        CVal *c = xalloc(sizeof *c);
        if (getenv("ZB_DBGA") && p->s && !strcmp(p->s, getenv("ZB_DBGA"))) {
          fprintf(stderr, "anyarg ck=%d k=%d t=%s at %s:%d:", v.ck, v.cv.k, tname(v.t), an->tok->file, an->tok->line);
          if (v.t->ct) {
            layout(v.t->ct);
            for (int q = 0; q < v.t->ct->fields.n; q++) {
              Field *f = v.t->ct->fields.a[q];
              fprintf(stderr, " %s:%d:%s", f->name, f->is_ct, tname(f->t));
            }
          }
          fprintf(stderr, "\n");
        }
        if (v.ck && (type_is_ctonly(v.t) || v.cv.k == CV_FN || all_ct_fields(v.t)))
          *c = v.cv;
        else {
          if (v.t->k == TY_CINT)
            v = coerce(v, t_i64);
          else if (v.t->k == TY_CFLOAT)
            v = coerce(v, t_f64);
          c->k = CV_TYPE;
          c->t = v.t;
          c->slen = -1;
          pre[i] = v;
          haspre[i] = 1;
        }
        if (p->s) {
          if (c->k == CV_TYPE && c->slen == -1)
            bind_placeholder(pscope, p->s, c->t);
          else
            bind_cval(pscope, p->s, *c);
        }
        vpush(&cargs, c);
        continue;
      }
      vpush(&cargs, NULL);
    }
    while (cargs.n < np) vpush(&cargs, NULL);
    FnInst *fi = fn_instance(fd, &cargs);
    if (fi->ret && type_is_ctonly(fi->ret)) {
      CVal r;
      if (!ceval_force(n, s, &r))
        die("%s:%d: cannot evaluate call to %s (returns comptime-only %s) at comptime (at %s)", n->tok->file,
            n->tok->line, fd->name, tname(fi->ret), ct_fail_loc());
      return CK(r);
    }
    Vec args = {0};
    int va = 0;
    Val *inl_vals = NULL;
    static int inl_depth;
    static int noinl = -1;
    if (noinl < 0) noinl = !!getenv("ZB_NOINLINE");
    if (!noinl && (f->flags & F_INLINE) && !(f->flags & F_EXTERN) && f->b && inl_depth < 48) {
      inl_vals = xalloc(sizeof(Val) * (np + 1));
      for (int i = 0; i < np; i++)
        if (((Node *)f->list.a[i])->flags & F_VARARGS) inl_vals = NULL;
    }
    for (int i = 0; i < np; i++) {
      Node *p = f->list.a[i];
      Type *pt = fi->ptypes.a[i];
      if (p->flags & F_VARARGS) {
        va = 1;
        break;
      }
      if (!pt) continue;
      Val v;
      if (haspre[i])
        v = pre[i];
      else if (i == 0 && has_self) {
        v = self;
        if (pt->k == TY_PTR && self.t->k != TY_PTR)
          v = V(ptr_to(self.t, 0), addr_of(self));
        else if (pt->k != TY_PTR && self.t->k == TY_PTR)
          v = LV(self.t->elem, opnd(self));
      } else
        v = gen(n->list.a[i - has_self], s, pt);
      v = coerce(v, pt);
      if (v.t->k == TY_NORET) return v;
      if (inl_vals) {
        if (!v.ck && !(i == 0 && has_self)) {
          CVal c;
          if (ceval(n->list.a[i - has_self], s, &c) && c.k != CV_UNDEF && c.k != CV_VOID) {
            Val cv = CK(c);
            cv.t = pt;
            v = cv;
          }
        }
        inl_vals[i] = v;
        continue;
      }
      if ((f->flags & F_EXTERN) && is_packed(pt) && tsize(pt) <= 8) {
        Type *h = int_type(tsize(pt) * 8, 0);
        vpush(&args, fmt("%c %s", qc(h), load(h, addr_of(v))));
        continue;
      }
      char *a = argtxt(v, pt);
      if (a) vpush(&args, a);
    }
    if (va) {
      vpush(&args, "...");
      for (int j = np - 1 - has_self; j < n->list.n; j++) {
        Val v = rv(gen(n->list.a[j], s, NULL));
        if (v.t->k == TY_CINT) v = coerce(v, (v.cv.i > 2147483647LL || v.cv.i < -2147483648LL) ? t_i64 : t_i32);
        if (v.ck && v.cv.k == CV_STR) v = coerce(v, mptr_to(t_u8, 1, 1, 0));
        if (v.t->k == TY_CFLOAT)
          v = coerce(v, t_f64);
        else if (v.t->k == TY_FLOAT && v.t->bits < 64)
          v = float_conv(v, t_f64);
        Type *t = v.t;
        if (t->k == TY_BOOL || (t->k == TY_INT && t->bits < 32)) {
          v = coerce(v, t->k == TY_INT && t->sign ? t_i32 : t_u32);
          t = v.t;
        }
        vpush(&args, argtxt(v, t));
      }
    }
    if (inl_vals) {
      inl_depth++;
      Val r = gen_inline_body(fi, inl_vals);
      inl_depth--;
      return r;
    }
    queue_fn(fi);
    return do_call(fmt("$%s", fi->sym), &args, fi->ret, !!(f->flags & F_EXTERN));
  }
  /* indirect call through function pointer */
  Val fp = rv(fnv);
  Type *ft = fp.t->k == TY_PTR ? fp.t->elem : fp.t;
  if (ft->k == TY_OPT) ft = ft->elem->k == TY_PTR ? ft->elem->elem : ft->elem;
  if (ft->k != TY_FN) die("%s:%d: call of non-function %s", n->tok->file, n->tok->line, tname(fp.t));
  Vec args = {0};
  char *callee = opnd(fp);
  for (int i = 0; i < n->list.n; i++) {
    Type *pt = i < ft->params.n ? ft->params.a[i] : NULL;
    Val v = gen(n->list.a[i], s, pt);
    if (pt)
      v = coerce(v, pt);
    else
      v = rv(v);
    char *a = argtxt(v, pt ? pt : v.t);
    if (a) vpush(&args, a);
  }
  return do_call(callee, &args, ft->ret, 0);
}
