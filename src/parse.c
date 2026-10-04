#include "zb.h"

static Tok *T;
static int P;
static Tok *cur(void) {
  return &T[P];
}
static Tok *ahead(int i) {
  return &T[P + i];
}
static int tis(Tok *t, const char *s) {
  return (t->k == TK_P || t->k == TK_KW) && !strcmp(t->s, s);
}
static int is(const char *s) {
  return tis(cur(), s);
}
static int accept(const char *s) {
  if (is(s)) {
    P++;
    return 1;
  }
  return 0;
}
static _Noreturn void perr(const char *m) {
  die("%s:%d: parse error: %s (at '%s')", cur()->file, cur()->line, m, cur()->s);
}
static void expect(const char *s) {
  if (!accept(s)) perr(fmt("expected '%s'", s));
}
static char *ident(void) {
  if (cur()->k != TK_ID) perr("expected identifier");
  return T[P++].s;
}
static Node *mk(int k) {
  Node *n = xalloc(sizeof *n);
  n->k = k;
  n->tok = cur();
  return n;
}

static Node *parse_expr(void);
static int no_curly;
static Node *parse_expr_nc(void);
static Node *parse_type_expr(void);
static Node *parse_block(void);
static Node *parse_assign_expr(void);
static Node *parse_bin(int minp);
static Node *parse_primary(void);
static void parse_members(Node *c);

static int is_labeled(void) {
  return cur()->k == TK_ID && tis(ahead(1), ":") &&
         (tis(ahead(2), "{") || tis(ahead(2), "while") || tis(ahead(2), "for") || tis(ahead(2), "inline") ||
          tis(ahead(2), "switch"));
}
static void skip_paren_expr(void) {
  expect("(");
  parse_expr();
  expect(")");
}

static void parse_capture(char **name, int *ref, char **name2) {
  if (!accept("|")) return;
  *ref = accept("*");
  *name = ident();
  if (accept(",")) {
    accept("*");
    char *n2 = ident();
    if (name2) *name2 = n2;
  }
  expect("|");
}
static int no_assign;
static Node *parse_body(void) {
  if (is("{")) return parse_block();
  if (no_assign) return parse_expr();
  Node *e = parse_assign_expr();
  int dest = 0;
  if (e->k != N_ASSIGN && is(",")) {
    int depth = 0;
    for (int i = 1;; i++) {
      Tok *t = ahead(i);
      if (t->k == TK_EOF) break;
      if (tis(t, "(") || tis(t, "[") || tis(t, "{"))
        depth++;
      else if (tis(t, ")") || tis(t, "]") || tis(t, "}")) {
        if (--depth < 0) break;
      } else if (depth == 0 && (tis(t, ";") || tis(t, "=>") || tis(t, "pub") || tis(t, "const") || tis(t, "var") ||
                                tis(t, "fn") || tis(t, "test") || tis(t, "comptime")))
        break;
      else if (depth == 0 && tis(t, ".") && ahead(i + 1)->k == TK_ID && tis(ahead(i + 2), "="))
        break;
      else if (depth == 0 && tis(t, "=")) {
        dest = 1;
        break;
      }
    }
  }
  if (dest) {
    int save = P;
    Node *d = mk(N_DESTRUCT);
    vpush(&d->list, e);
    while (accept(",")) vpush(&d->list, parse_expr());
    if (is("=")) {
      P++;
      d->b = parse_expr();
      return d;
    }
    P = save;
  }
  return e;
}

static Node *parse_if(void) {
  Node *n = mk(N_IF);
  expect("if");
  expect("(");
  n->a = parse_expr_nc();
  expect(")");
  parse_capture(&n->cap, &n->capref, NULL);
  n->b = parse_body();
  if (accept("else")) {
    int r;
    parse_capture(&n->cap2, &r, NULL);
    n->c = parse_body();
  }
  return n;
}
static Node *parse_while(char *label) {
  Node *n = mk(N_WHILE);
  n->label = label;
  if (accept("inline")) n->flags |= F_INLINE;
  expect("while");
  expect("(");
  n->a = parse_expr_nc();
  expect(")");
  parse_capture(&n->cap, &n->capref, NULL);
  if (accept(":")) {
    expect("(");
    n->d = parse_assign_expr();
    expect(")");
  }
  n->b = parse_body();
  if (accept("else")) {
    int r;
    parse_capture(&n->cap2, &r, NULL);
    n->c = parse_body();
  }
  return n;
}
static Node *parse_for(char *label) {
  Node *n = mk(N_FOR);
  n->label = label;
  if (accept("inline")) n->flags |= F_INLINE;
  expect("for");
  expect("(");
  do {
    if (is(")")) break;
    Node *e = parse_expr_nc();
    if (accept("..")) {
      Node *r = mk(N_RANGE);
      r->a = e;
      if (!is(")") && !is(",")) r->b = parse_expr_nc();
      e = r;
    }
    vpush(&n->list, e);
  } while (accept(","));
  expect(")");
  expect("|");
  do {
    if (is("|")) break;
    Node *c = mk(N_IDENT);
    if (accept("*")) c->flags |= F_REF;
    c->s = ident();
    vpush(&n->list2, c);
  } while (accept(","));
  expect("|");
  n->b = parse_body();
  if (accept("else")) n->c = parse_body();
  return n;
}
static Node *parse_switch(void) {
  Node *n = mk(N_SWITCH);
  expect("switch");
  expect("(");
  n->a = parse_expr_nc();
  expect(")");
  expect("{");
  while (!accept("}")) {
    Node *pr = mk(N_PRONG);
    if (accept("inline")) pr->flags |= F_INLINE;
    if (is("else") && tis(ahead(1), "=>")) {
      P++;
      pr->flags |= F_ELSE;
    } else if (cur()->k == TK_ID && !cur()->ival && !strcmp(cur()->s, "_") && tis(ahead(1), "=>")) {
      P++;
      pr->flags |= F_ELSE;
    } else
      do {
        if (is("=>")) break;
        Node *e = parse_expr();
        if (accept("...")) {
          Node *r = mk(N_RANGE);
          r->a = e;
          r->b = parse_expr();
          e = r;
        }
        vpush(&pr->list, e);
      } while (accept(","));
    int unnamed =
        0; /* `_` item: matches the unnamed values of a non-exhaustive enum -> split into an extra else prong */
    for (int i = 0; i < pr->list.n; i++) {
      Node *it = pr->list.a[i];
      if (it->k == N_IDENT && !strcmp(it->s, "_")) {
        unnamed = 1;
        for (int j = i; j + 1 < pr->list.n; j++) pr->list.a[j] = pr->list.a[j + 1];
        pr->list.n--;
        i--;
      }
    }
    expect("=>");
    parse_capture(&pr->cap, &pr->capref, &pr->cap2);
    pr->b = parse_assign_expr();
    if (unnamed && !pr->list.n) pr->flags |= F_ELSE;
    vpush(&n->list, pr);
    if (unnamed && pr->list.n) {
      Node *p2 = xalloc(sizeof *p2);
      *p2 = *pr;
      memset(&p2->list, 0, sizeof p2->list);
      p2->flags = (pr->flags & ~F_INLINE) | F_ELSE;
      vpush(&n->list, p2);
    }
    if (!accept(",")) {
      expect("}");
      break;
    }
  }
  return n;
}
static Node *parse_init(Node *type) {
  int sv = no_curly;
  no_curly = 0;
  Node *n = mk(N_INIT);
  n->a = type;
  expect("{");
  if (is(".") && ahead(1)->k == TK_ID && tis(ahead(2), "=")) {
    n->flags |= F_FIELDS;
    while (!accept("}")) {
      expect(".");
      Node *nm = mk(N_IDENT);
      nm->s = ident();
      expect("=");
      vpush(&n->list2, nm);
      vpush(&n->list, parse_expr());
      if (!accept(",")) {
        expect("}");
        break;
      }
    }
  } else {
    while (!accept("}")) {
      vpush(&n->list, parse_expr());
      if (!accept(",")) {
        expect("}");
        break;
      }
    }
  }
  no_curly = sv;
  return n;
}
static Node *parse_fn_proto(Node *n) {
  expect("fn");
  if (cur()->k == TK_ID) n->s = ident();
  expect("(");
  while (!accept(")")) {
    Node *p = mk(N_PARAM);
    if (accept("comptime")) p->flags |= F_COMPTIME;
    accept("noalias");
    if (accept("...")) {
      p->flags |= F_VARARGS;
      n->flags |= F_VARARGS;
    } else {
      if ((cur()->k == TK_ID) && tis(ahead(1), ":")) {
        p->s = ident();
        P++;
      }
      if (accept("anytype"))
        p->flags |= F_ANYTYPE;
      else
        p->a = parse_type_expr();
    }
    vpush(&n->list, p);
    if (!accept(",")) {
      expect(")");
      break;
    }
  }
  if (accept("align")) skip_paren_expr();
  if (accept("addrspace")) skip_paren_expr();
  if (accept("linksection")) skip_paren_expr();
  if (accept("callconv")) {
    expect("(");
    n->c = parse_expr();
    expect(")");
  }
  if (accept("!")) n->flags |= F_INFERR;
  int sv = no_curly;
  no_curly = 1;
  n->a = parse_type_expr();
  no_curly = sv;
  return n;
}
static Node *parse_container(void) {
  Node *n = mk(N_CONTAINER);
  if (accept("extern")) n->flags |= F_EXTERN;
  if (accept("packed")) n->flags |= F_PACKED;
  n->s = T[P++].s; /* struct enum union opaque */
  if (accept("(")) {
    if (accept("enum")) {
      n->flags |= F_TAGGED;
      if (accept("(")) {
        n->a = parse_expr();
        expect(")");
        n->flags |= F_ALLOWZERO;
      }
    } else
      n->a = parse_expr();
    expect(")");
    if (!strcmp(n->s, "union") && n->a && !(n->flags & F_PACKED)) n->flags |= F_TAGGED;
  }
  int sv = no_curly;
  no_curly = 0;
  expect("{");
  parse_members(n);
  expect("}");
  no_curly = sv;
  return n;
}
static Node *parse_primary_type(void) {
  Tok *t = cur();
  Node *n;
  switch (t->k) {
  case TK_BUILTIN:
    n = mk(N_BUILTIN);
    n->s = t->s;
    P++;
    expect("(");
    while (!accept(")")) {
      vpush(&n->list, parse_expr_nc());
      if (!accept(",")) {
        expect(")");
        break;
      }
    }
    return n;
  case TK_INT:
    n = mk(N_INT);
    n->ival = t->ival;
    P++;
    return n;
  case TK_FLOAT:
    n = mk(N_FLOAT);
    n->s = t->s;
    n->fval = t->fval;
    P++;
    return n;
  case TK_CHAR:
    n = mk(N_CHAR);
    n->ival = t->ival;
    P++;
    return n;
  case TK_STR:
    n = mk(N_STR);
    n->s = t->s;
    n->slen = t->len;
    P++;
    return n;
  case TK_ID:
    if (is_labeled()) return parse_primary();
    P++;
    if (!t->ival && !strcmp(t->s, "true")) return mk(N_TRUE);
    if (!t->ival && !strcmp(t->s, "false")) return mk(N_FALSE);
    if (!t->ival && !strcmp(t->s, "null")) return mk(N_NULL);
    if (!t->ival && !strcmp(t->s, "undefined")) return mk(N_UNDEF);
    n = mk(N_IDENT);
    n->tok = t;
    n->s = t->s;
    return n;
  default: break;
  }
  if (is(".") && ahead(1)->k == TK_ID) {
    P++;
    n = mk(N_ENUMLIT);
    n->s = ident();
    return n;
  }
  if (is(".") && tis(ahead(1), "{")) {
    P++;
    return parse_init(NULL);
  }
  if (accept("error")) {
    if (accept(".")) {
      n = mk(N_ERRVAL);
      n->s = ident();
      return n;
    }
    n = mk(N_ERRSET);
    expect("{");
    while (!accept("}")) {
      Node *e = mk(N_IDENT);
      e->s = ident();
      vpush(&n->list, e);
      if (!accept(",")) {
        expect("}");
        break;
      }
    }
    return n;
  }
  if (is("fn")) {
    n = mk(N_TFN);
    return parse_fn_proto(n);
  }
  if (accept("(")) {
    n = parse_expr_nc();
    expect(")");
    return n;
  }
  if (is("struct") || is("enum") || is("union") || is("opaque") || is("extern") || is("packed"))
    return parse_container();
  if (is("unreachable")) {
    P++;
    return mk(N_UNREACHABLE);
  }
  if (is("if") || is("switch") || is("comptime") || is("for") || is("while") || is("inline") || is("{")) {
    if (is("switch")) return parse_switch();
    return parse_primary();
  }
  if (is("anytype")) {
    P++;
    n = mk(N_IDENT);
    n->s = "anytype";
    return n;
  }
  perr("expected expression");
}
static Node *suffix_ops(Node *n);
static Node *parse_suffix(void) {
  return suffix_ops(parse_primary_type());
}
static Node *suffix_ops(Node *n) {
  for (;;) {
    if (accept("[")) {
      Node *i = parse_expr_nc();
      if (accept("..")) {
        Node *s = mk(N_SLICE);
        s->a = n;
        s->b = i;
        if (!is("]") && !is(":")) s->c = parse_expr();
        if (accept(":")) s->d = parse_expr();
        expect("]");
        n = s;
      } else {
        expect("]");
        Node *x = mk(N_INDEX);
        x->a = n;
        x->b = i;
        n = x;
      }
    } else if (accept(".")) {
      Node *f = mk(N_FIELD);
      f->a = n;
      f->s = ident();
      n = f;
    } else if (accept(".*")) {
      Node *f = mk(N_DEREF);
      f->a = n;
      n = f;
    } else if (accept(".?")) {
      Node *f = mk(N_UNWRAP);
      f->a = n;
      n = f;
    } else if (is("(")) {
      P++;
      Node *c = mk(N_CALL);
      c->a = n;
      while (!accept(")")) {
        vpush(&c->list, parse_expr_nc());
        if (!accept(",")) {
          expect(")");
          break;
        }
      }
      n = c;
    } else
      return n;
  }
}
static void ptr_attrs(Node *n) {
  for (;;) {
    if (accept("const"))
      n->flags |= F_CONST;
    else if (accept("volatile"))
      ;
    else if (accept("allowzero"))
      n->flags |= F_ALLOWZERO;
    else if (accept("align")) {
      expect("(");
      parse_expr();
      while (accept(":")) parse_expr();
      expect(")");
    } else if (accept("addrspace"))
      skip_paren_expr();
    else
      break;
  }
}
static Node *parse_type_expr0(void);
static Node *parse_type_expr(void) {
  no_assign++;
  Node *n = parse_type_expr0();
  no_assign--;
  return n;
}
static Node *parse_type_expr0(void) {
  Node *n;
  if (accept("?")) {
    n = mk(N_TOPT);
    n->a = parse_type_expr();
    return n;
  }
  if (is("*") || is("**")) {
    int dbl = is("**");
    P++;
    n = mk(N_TPTR);
    n->s = "*";
    ptr_attrs(n);
    n->a = parse_type_expr();
    if (dbl) {
      Node *o = mk(N_TPTR);
      o->s = "*";
      o->a = n;
      return o;
    }
    return n;
  }
  if (is("[")) {
    P++;
    if (accept("*")) {
      n = mk(N_TPTR);
      n->s = "[*]";
      if (cur()->k == TK_ID && !strcmp(cur()->s, "c")) P++;
      if (accept(":")) n->b = parse_expr();
      expect("]");
      ptr_attrs(n);
      n->a = parse_type_expr();
      return n;
    }
    if (accept("]")) {
      n = mk(N_TPTR);
      n->s = "[]";
      ptr_attrs(n);
      n->a = parse_type_expr();
      return n;
    }
    if (accept(":")) {
      n = mk(N_TPTR);
      n->s = "[]";
      n->b = parse_expr();
      expect("]");
      ptr_attrs(n);
      n->a = parse_type_expr();
      return n;
    }
    n = mk(N_TARRAY);
    if (cur()->k == TK_ID && !strcmp(cur()->s, "_") && (tis(ahead(1), "]") || tis(ahead(1), ":")))
      P++;
    else
      n->a = parse_expr();
    if (accept(":")) n->c = parse_expr();
    expect("]");
    n->b = parse_type_expr();
    return n;
  }
  n = parse_suffix();
  if (accept("!")) {
    Node *e = mk(N_TERRU);
    e->a = n;
    e->b = parse_type_expr();
    return e;
  }
  return n;
}
static Node *parse_expr_nc(void) {
  int s = no_curly;
  no_curly = 0;
  Node *n = parse_expr();
  no_curly = s;
  return n;
}
static Node *parse_curly(void) {
  Node *t = parse_type_expr();
  if (is("{") && !no_curly) return parse_init(t);
  return t;
}
static int binprec(Tok *t);
static int can_start_expr(void) {
  if (binprec(cur()) >= 0 && !is("-") && !is("&") && !is("*") && !is("-%")) return 0;
  return !(is(";") || is(")") || is("}") || is(",") || is("]") || is("else") || is(":") || is("=>") || is("=") ||
           is("+="));
}
static Node *parse_primary(void) {
  Node *n;
  if (accept("break")) {
    n = mk(N_BREAK);
    if (accept(":")) n->label = ident();
    if (can_start_expr()) n->a = parse_expr();
    return n;
  }
  if (accept("continue")) {
    n = mk(N_CONTINUE);
    if (accept(":")) n->label = ident();
    if (can_start_expr()) n->a = parse_expr();
    return n;
  }
  if (accept("return")) {
    n = mk(N_RETURN);
    if (can_start_expr()) n->a = parse_expr();
    return n;
  }
  if (accept("comptime")) {
    n = mk(N_COMPTIME);
    n->a = parse_expr();
    return n;
  }
  if (accept("nosuspend")) return parse_expr();
  if (is_labeled()) {
    char *l = ident();
    expect(":");
    if (is("{")) {
      n = parse_block();
      n->label = l;
      return suffix_ops(n);
    }
    if (is("switch")) {
      n = parse_switch();
      n->label = l;
      return suffix_ops(n);
    }
    if (is("inline")) {
      if (tis(ahead(1), "for")) return parse_for(l);
      return parse_while(l);
    }
    if (is("while")) return parse_while(l);
    return parse_for(l);
  }
  if (is("{")) return parse_block();
  if (is("if")) return parse_if();
  if (is("inline")) {
    if (tis(ahead(1), "for")) return parse_for(NULL);
    return parse_while(NULL);
  }
  if (is("while")) return parse_while(NULL);
  if (is("for")) return parse_for(NULL);
  if (accept("asm")) {
    n = mk(N_ASM);
    accept("volatile");
    expect("(");
    n->a = parse_expr();
    for (int sec = 0; sec < 3 && accept(":"); sec++) {
      while (!is(":") && !is(")")) {
        if (sec == 2) {
          vpush(&n->list2, parse_expr());
          if (!accept(",")) break;
          continue;
        }
        Node *o = mk(N_PARAM);
        expect("[");
        o->s = ident();
        expect("]");
        o->label = T[P].s;
        P++; /* constraint str */
        expect("(");
        if (accept("->")) {
          o->flags |= F_REF;
          o->a = parse_type_expr();
        } else
          o->a = parse_expr();
        expect(")");
        o->ival = sec;
        vpush(&n->list, o);
        if (!accept(",")) break;
      }
    }
    expect(")");
    return n;
  }
  return parse_curly();
}
static Node *parse_prefix(void) {
  Node *n;
  if (accept("try")) {
    n = mk(N_TRY);
    n->a = parse_prefix();
    return n;
  }
  if (is("!") || is("-") || is("~") || is("-%") || is("&")) {
    n = mk(N_UN);
    n->s = T[P++].s;
    n->a = parse_prefix();
    return n;
  }
  return parse_primary();
}
static int binprec(Tok *t) {
  static const char *ops[][8] = {{"or"},
                                 {"and"},
                                 {"==", "!=", "<", ">", "<=", ">="},
                                 {"&", "^", "|", "orelse", "catch"},
                                 {"<<", ">>", "<<|"},
                                 {"+", "-", "++", "+%", "-%", "+|", "-|"},
                                 {"*", "/", "%", "**", "*%", "*|", "||"}};
  if (t->k != TK_P && t->k != TK_KW) return -1;
  for (int i = 0; i < 7; i++)
    for (int j = 0; j < 8 && ops[i][j]; j++)
      if (!strcmp(ops[i][j], t->s)) return i + 1;
  return -1;
}
static Node *parse_bin(int minp) {
  Node *l = parse_prefix();
  for (;;) {
    int p = binprec(cur());
    if (p < minp) return l;
    char *op = T[P++].s;
    Node *n;
    if (!strcmp(op, "catch")) {
      n = mk(N_CATCH);
      int r;
      parse_capture(&n->cap, &r, NULL);
    } else if (!strcmp(op, "orelse"))
      n = mk(N_ORELSE);
    else {
      n = mk(N_BIN);
      n->s = op;
    }
    n->a = l;
    n->b = parse_bin(p + 1);
    l = n;
  }
}
static Node *parse_expr(void) {
  return parse_bin(1);
}
static const char *assignops[] = {"=",   "+=",  "-=",  "*=",  "/=",  "%=",  "&=",  "|=",   "^=", "<<=",
                                  ">>=", "+%=", "-%=", "*%=", "+|=", "-|=", "*|=", "<<|=", 0};
static Node *parse_assign_expr(void) {
  Node *l = parse_expr();
  for (int i = 0; assignops[i]; i++)
    if (is(assignops[i])) {
      Node *n = mk(N_ASSIGN);
      n->s = T[P++].s;
      n->a = l;
      n->b = parse_expr();
      return n;
    }
  return l;
}
static Node *parse_vardecl(int flags) {
  Node *n = mk(N_VAR);
  n->flags = flags;
  if (accept("const"))
    n->flags |= F_CONST;
  else
    expect("var");
  n->s = ident();
  if (accept(":")) n->a = parse_type_expr();
  if (accept("align")) skip_paren_expr();
  if (accept("addrspace")) skip_paren_expr();
  if (accept("linksection")) skip_paren_expr();
  if (accept("=")) n->b = parse_expr();
  return n;
}
static Node *parse_stmt(void) {
  Node *n;
  if (is("comptime") && (tis(ahead(1), "const") || tis(ahead(1), "var"))) {
    P++;
    n = parse_vardecl(F_COMPTIME);
    expect(";");
    return n;
  }
  if (is("const") || is("var")) {
    int save = P;
    P += 2;
    if (accept(":")) parse_type_expr();
    int d = is(",");
    P = save;
    if (d) goto destruct;
  }
  if (is("const") || is("var")) {
    n = parse_vardecl(0);
    expect(";");
    return n;
  }
  if (accept("defer")) {
    n = mk(N_DEFER);
    n->a = parse_body();
    accept(";");
    return n;
  }
  if (accept("errdefer")) {
    n = mk(N_ERRDEFER);
    int r;
    parse_capture(&n->cap, &r, NULL);
    n->a = parse_body();
    accept(";");
    return n;
  }
  if (is("comptime") && tis(ahead(1), "{")) {
    P++;
    n = mk(N_COMPTIME);
    n->a = parse_block();
    accept(";");
    return n;
  }
  if (is("if") || is("while") || is("for") || is("switch") || is("{") || is("inline") || is_labeled()) {
    n = is("switch") ? parse_switch() : parse_primary();
    if (n->k != N_SWITCH) { /* may be followed by binop/assign in rare cases; assume not */
    }
    accept(";");
    return n;
  }
  {
    int save = P;
    Node *first = NULL;
    if (0) {
    destruct:
      save = P;
    }
    /* try destructure: target (, target)+ = expr */
    Node *d = mk(N_DESTRUCT);
    for (;;) {
      Node *t;
      if (is("const") || is("var")) {
        t = mk(N_VAR);
        if (accept("const"))
          t->flags |= F_CONST;
        else
          P++;
        t->s = ident();
        if (accept(":")) t->a = parse_type_expr();
      } else
        t = parse_expr();
      if (!first) first = t;
      vpush(&d->list, t);
      if (!accept(",")) break;
    }
    if (d->list.n > 1) {
      expect("=");
      d->b = parse_expr();
      expect(";");
      return d;
    }
    P = save;
  }
  n = parse_assign_expr();
  expect(";");
  return n;
}
static Node *parse_block(void) {
  int sv = no_curly;
  no_curly = 0;
  int sna = no_assign;
  no_assign = 0;
  Node *n = mk(N_BLOCK);
  expect("{");
  while (!accept("}")) vpush(&n->list, parse_stmt());
  no_curly = sv;
  no_assign = sna;
  return n;
}
static void skip_doc(void) {}
static void parse_members(Node *c) {
  for (;;) {
    skip_doc();
    if (is("}") || cur()->k == TK_EOF) return;
    int flags = 0;
    if (accept("test")) {
      if (cur()->k == TK_STR || cur()->k == TK_ID) P++;
      parse_block();
      continue;
    }
    if (is("comptime") && tis(ahead(1), "{")) {
      static int cbn;
      Node *cb = mk(N_COMPTIME);
      P++;
      cb->a = parse_block();
      cb->s = fmt("comptime#%d", ++cbn);
      vpush(&c->list2, cb);
      continue;
    }
    if (accept("pub")) flags |= F_PUB;
    if (accept("usingnamespace")) {
      parse_expr();
      expect(";");
      continue;
    }
    for (;;) {
      if (accept("export"))
        flags |= F_EXPORT;
      else if (accept("extern")) {
        flags |= F_EXTERN;
        if (cur()->k == TK_STR) P++;
      } else if (accept("inline"))
        flags |= F_INLINE;
      else if (accept("noinline") || accept("threadlocal"))
        ;
      else
        break;
    }
    if (is("fn")) {
      Node *f = mk(N_FN);
      f->flags |= flags;
      parse_fn_proto(f);
      f->flags |= flags;
      if (is("{"))
        f->b = parse_block();
      else
        expect(";");
      vpush(&c->list2, f);
      continue;
    }
    if (is("const") || is("var")) {
      Node *v = parse_vardecl(flags);
      expect(";");
      vpush(&c->list2, v);
      continue;
    }
    /* field */
    Node *f = mk(N_FIELDDECL);
    accept("comptime");
    int is_struct = !strcmp(c->s, "struct");
    if (cur()->k == TK_ID &&
        (tis(ahead(1), ":") || (!is_struct && (tis(ahead(1), ",") || tis(ahead(1), "=") || tis(ahead(1), "}"))))) {
      f->s = ident();
      if (accept(":")) f->a = parse_type_expr();
    } else {
      f->s = fmt("%d", c->list.n);
      f->a = parse_type_expr();
      f->flags |= F_ANYTYPE; /* tuple field */
    }
    if (accept("align")) {
      expect("(");
      f->c = parse_expr();
      expect(")");
    }
    if (accept("=")) f->b = parse_expr();
    vpush(&c->list, f);
    if (!accept(",")) {
      if (!is("}") && cur()->k != TK_EOF) perr("expected , after field");
    }
  }
}
Node *parse_zon(const char *path) { /* a .zon file: a single expression */
  long len;
  char *src = read_file(path, &len);
  if (!src) die("cannot open %s", path);
  int n;
  Tok *sv = T;
  int sp = P;
  T = lex(path, src, &n);
  P = 0;
  Node *e = parse_expr();
  if (cur()->k != TK_EOF) perr("expected end of zon file");
  T = sv;
  P = sp;
  return e;
}
Node *parse_file(const char *path) {
  long len;
  char *src = read_file(path, &len);
  if (!src) die("cannot open %s", path);
  int n;
  T = lex(path, src, &n);
  P = 0;
  Node *c = mk(N_CONTAINER);
  c->s = "struct";
  parse_members(c);
  if (cur()->k != TK_EOF) perr("expected end of file");
  return c;
}
