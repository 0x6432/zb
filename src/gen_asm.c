#include "gen_int.h"

int areg_find(const char *nm) {
  for (int r = 0; r < 16; r++)
    for (int k = 0; k < 4; k++)
      if (!strcmp(nm, areg[r][k])) return r;
  return -1;
}
int asz_idx(Type *t) {
  int64_t z = tsize(t);
  return z >= 8 ? 0 : z == 4 ? 1 : z == 2 ? 2 : 3;
}
Val gen_asm_stub(Node *n, Scope *s, CVal *tpl, Type *rt) {
  Val none = {0};
  if (!asm_out) return none;
  int m = n->list.n;
  if (m > 24) return none;
  int reg[24], dir[24], rw[24];
  Type *ty[24];
  Val lvs[24];
  char *ins[24];
  int used = 0;
  for (int i = 0; i < m; i++) {
    Node *o = n->list.a[i];
    char con[64];
    const char *L = o->label;
    if (L[0] == '"')
      snprintf(con, sizeof con, "%.*s", (int)strlen(L) - 2, L + 1);
    else
      snprintf(con, sizeof con, "%s", L);
    char *c = con;
    dir[i] = o->ival;
    rw[i] = 0;
    reg[i] = -1;
    if (*c == '=')
      c++;
    else if (*c == '+') {
      c++;
      rw[i] = 1;
    }
    if (*c == '&') c++;
    if (*c == '{') {
      char nm[16];
      snprintf(nm, sizeof nm, "%.*s", (int)strcspn(c + 1, "}"), c + 1);
      reg[i] = areg_find(nm);
      if (reg[i] < 0) return none;
      used |= 1 << reg[i];
    } else if (strcmp(c, "r"))
      return none;
  }
  for (int i = 0; i < m; i++)
    if (reg[i] < 0) {
      static const int pool[] = {0, 2, 3, 4, 5, 7, 8, 9, 10, 1, 11, 12, 13, 14};
      for (int k = 0; k < 14; k++)
        if (!(used & (1 << pool[k]))) {
          reg[i] = pool[k];
          used |= 1 << pool[k];
          break;
        }
      if (reg[i] < 0) return none;
    }
  /* evaluate operands */
  for (int i = 0; i < m; i++) {
    Node *o = n->list.a[i];
    ins[i] = NULL;
    if (dir[i] == 0) {
      if (o->flags & F_REF)
        ty[i] = rt;
      else {
        lvs[i] = gen(o->a, s, NULL);
        if (!lvs[i].lv || lvs[i].bf) return none;
        ty[i] = lvs[i].t;
      }
      if (is_float(ty[i])) return none;
      if (rw[i]) {
        Val v = rv(lvs[i]);
        ins[i] = opnd(v);
        if (qc(v.t) == 'w') {
          char *e = tmp();
          emit("%s =l extuw %s", e, ins[i]);
          ins[i] = e;
        }
      }
    } else {
      Val v = rv(gen(o->a, s, NULL));
      if (v.t->k == TY_CINT) v = coerce(v, t_u64);
      if (is_float(v.t)) return none;
      ty[i] = v.t;
      ins[i] = opnd(v);
      if (qc(v.t) == 'w') {
        char *e = tmp();
        emit("%s =l extuw %s", e, ins[i]);
        ins[i] = e;
      }
    }
  }
  int id = asm_n++;
  char *buf = tmp();
  emit("%s =l alloc8 %d", buf, 8 * (m ? m : 1));
  for (int i = 0; i < m; i++)
    if (ins[i]) emit("storel %s, %s", ins[i], addp(buf, 8 * i));
  emit("call $zb_asm_%d(l %s)", id, buf);
  FILE *f = asm_out;
  fprintf(f,
          "\t.text\n\t.globl zb_asm_%d\nzb_asm_%d:\n\tpush %%rbx\n\tpush %%rbp\n\tpush %%r12\n\tpush %%r13\n\tpush "
          "%%r14\n\tpush %%r15\n\tpush %%rdi\n",
          id, id);
  int rdi_in = -1;
  for (int i = 0; i < m; i++)
    if (ins[i]) {
      if (reg[i] == 5)
        rdi_in = i;
      else
        fprintf(f, "\tmovq %d(%%rdi), %%%s\n", 8 * i, areg[reg[i]][0]);
    }
  if (rdi_in >= 0) fprintf(f, "\tmovq %d(%%rdi), %%rdi\n", 8 * rdi_in);
  fputc('\t', f);
  for (int k = 0; k < tpl->slen; k++) {
    char ch = tpl->s[k];
    if (ch == '%' && k + 1 < tpl->slen && tpl->s[k + 1] == '%') {
      fputc('%', f);
      k++;
      continue;
    }
    if (ch == '%' && k + 1 < tpl->slen && tpl->s[k + 1] == '[') {
      int e = k + 2;
      while (e < tpl->slen && tpl->s[e] != ']') e++;
      char nm[64];
      snprintf(nm, sizeof nm, "%.*s", e - k - 2, tpl->s + k + 2);
      char *mod = strchr(nm, ':');
      if (mod) *mod++ = 0;
      int hit = -1;
      for (int i = 0; i < m; i++)
        if (!strcmp(((Node *)n->list.a[i])->s, nm)) {
          hit = i;
          break;
        }
      if (hit < 0) die("%s:%d: asm: unknown operand %%[%s]", n->tok->file, n->tok->line, nm);
      int zi = asz_idx(ty[hit]);
      if (mod && *mod == 'q')
        zi = 0;
      else if (mod && *mod == 'k')
        zi = 1;
      else if (mod && *mod == 'w')
        zi = 2;
      else if (mod && *mod == 'b')
        zi = 3;
      fprintf(f, "%%%s", areg[reg[hit]][zi]);
      k = e;
      continue;
    }
    fputc(ch, f);
    if (ch == '\n') fputc('\t', f);
  }
  fputc('\n', f);
  int nout = 0;
  for (int i = 0; i < m; i++)
    if (dir[i] == 0) {
      fprintf(f, "\tpush %%%s\n", areg[reg[i]][0]);
      nout++;
    }
  fprintf(f, "\tmovq %d(%%rsp), %%r11\n", 8 * nout);
  for (int i = m - 1; i >= 0; i--)
    if (dir[i] == 0) fprintf(f, "\tpop %%rax\n\tmovq %%rax, %d(%%r11)\n", 8 * i);
  fprintf(f, "\tadd $8, %%rsp\n\tpop %%r15\n\tpop %%r14\n\tpop %%r13\n\tpop %%r12\n\tpop %%rbp\n\tpop %%rbx\n\tret\n");
  Val ret = VOIDV();
  for (int i = 0; i < m; i++)
    if (dir[i] == 0) {
      char *a = addp(buf, 8 * i);
      if (((Node *)n->list.a[i])->flags & F_REF)
        ret = V(ty[i], load(ty[i], a));
      else
        put(V(ty[i], load(ty[i], a)), ty[i], lvs[i].op);
    }
  return ret;
}
Val gen_asm(Node *n, Scope *s) {
  CVal tpl;
  if (!ceval(n->a, s, &tpl) || tpl.k != CV_STR) die("%s:%d: asm template must be a string", n->tok->file, n->tok->line);
  Type *rt = t_void;
  for (int i = 0; i < n->list.n; i++) {
    Node *o = n->list.a[i];
    if (o->ival == 0 && (o->flags & F_REF)) rt = eval_type(o->a, s);
  }
  if (tpl.slen == 7 && !memcmp(tpl.s, "syscall", 7)) {
    static const char *regs[] = {"{rax}", "{rdi}", "{rsi}", "{rdx}", "{r10}", "{r8}", "{r9}"};
    char *a[7] = {"0", "0", "0", "0", "0", "0", "0"};
    for (int i = 0; i < n->list.n; i++) {
      Node *o = n->list.a[i];
      if (o->ival != 1) continue;
      char con[32];
      if (o->label[0] == '"')
        snprintf(con, sizeof con, "%.*s", (int)strlen(o->label) - 2, o->label + 1);
      else
        snprintf(con, sizeof con, "%s", o->label);
      for (int r = 0; r < 7; r++)
        if (!strcmp(con, regs[r])) {
          Val v = rv(gen(o->a, s, t_u64));
          if (v.t->k == TY_CINT) v = coerce(v, t_u64);
          if (qc(v.t) == 'w') {
            char *e = tmp();
            emit("%s =l extuw %s", e, opnd(v));
            a[r] = e;
          } else
            a[r] = opnd(v);
        }
    }
    if (!sys_helper_done) {
      sys_helper_done = 1;
      fprintf(xb, "function l $zb.syscall(l %%n, l %%a, l %%b, l %%c, l %%d, l %%e, l %%f) {\n@start\n\t%%r =l call "
                  "$syscall(l %%n, ..., l %%a, l %%b, l %%c, l %%d, l %%e, l %%f)\n"
                  "\t%%m =w ceql %%r, -1\n\tjnz %%m, @err, @ok\n@err\n\t%%p =l call $__errno_location()\n\t%%x =w "
                  "loadsw %%p\n\t%%y =l extsw %%x\n\t%%z =l neg %%y\n\tret %%z\n@ok\n\tret %%r\n}\n");
    }
    char *r = tmp();
    emit("%s =l call $zb.syscall(l %s, l %s, l %s, l %s, l %s, l %s, l %s)", r, a[0], a[1], a[2], a[3], a[4], a[5],
         a[6]);
    if (rt == t_void) return VOIDV();
    return coerce(V(t_u64, r), rt);
  }
  Val gv = gen_asm_stub(n, s, &tpl, rt);
  if (gv.t) return gv;
  fprintf(stderr, "zb: warning: %s:%d: unsupported inline asm \"%.*s\" compiled as a trap\n", n->tok->file,
          n->tok->line, tpl.slen > 40 ? 40 : tpl.slen, tpl.s);
  emit("hlt");
  term = 1;
  return NORET();
}
