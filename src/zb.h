#pragma once
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <stdint.h>
#include <ctype.h>
#include <math.h>

typedef struct { void **a; int n, cap; } Vec;
void vpush(Vec *v, void *x);
void *xalloc(size_t n);
void *xalloc_atomic(size_t n);
char *xstrndup(const char *s, size_t n);
char *fmt(const char *f, ...);
_Noreturn void die(const char *f, ...);
char *read_file(const char *path, long *len);

/* ---------- lexer ---------- */
enum { TK_EOF, TK_ID, TK_KW, TK_INT, TK_FLOAT, TK_CHAR, TK_STR, TK_BUILTIN, TK_P };
typedef __float128 f128;
f128 parse_f128(const char *s);
typedef struct Tok { int k; char *s; int len; int line; union { unsigned __int128 ival; f128 fval; }; const char *file; } Tok;
Tok *lex(const char *file, const char *src, int *ntok);

/* ---------- AST ---------- */
enum {
  N_INT, N_CHAR, N_STR, N_IDENT, N_TRUE, N_FALSE, N_NULL, N_UNDEF, N_UNREACHABLE,
  N_ENUMLIT, N_ERRVAL, N_ERRSET, N_BIN, N_UN, N_DEREF, N_UNWRAP, N_FIELD, N_INDEX,
  N_SLICE, N_CALL, N_BUILTIN, N_INIT, N_TRY, N_CATCH, N_ORELSE, N_IF, N_WHILE, N_FOR,
  N_SWITCH, N_PRONG, N_RANGE, N_BLOCK, N_BREAK, N_CONTINUE, N_RETURN, N_VAR, N_ASSIGN,
  N_DEFER, N_ERRDEFER, N_FN, N_PARAM, N_CONTAINER, N_FIELDDECL, N_TPTR, N_TARRAY,
  N_TOPT, N_TERRU, N_TFN, N_COMPTIME, N_DISCARD, N_NOP, N_FLOAT, N_ASM, N_DESTRUCT
};
enum { F_CONST = 1, F_PUB = 2, F_EXTERN = 4, F_EXPORT = 8, F_COMPTIME = 16, F_REF = 32,
       F_ELSE = 64, F_FIELDS = 128, F_TAGGED = 256, F_PACKED = 512, F_ANYTYPE = 1024,
       F_VARARGS = 2048, F_INLINE = 4096, F_ALLOWZERO = 8192, F_INFERR = 16384 };
typedef struct Node Node;
struct Node {
  int k; Tok *tok;
  char *s; int slen;
  unsigned __int128 ival; f128 fval;
  Node *a, *b, *c, *d;
  Vec list, list2;
  int flags;
  char *label, *cap, *cap2; int capref;
};
Node *parse_file(const char *path);
Node *parse_zon(const char *path);

/* ---------- types ---------- */
enum { TY_VOID, TY_BOOL, TY_NORET, TY_INT, TY_CINT, TY_PTR, TY_MPTR, TY_SLICE, TY_ARRAY,
       TY_STRUCT, TY_ENUM, TY_UNION, TY_OPT, TY_ERRU, TY_ERRSET, TY_TYPE, TY_FN, TY_NULL,
       TY_UNDEF, TY_ENUMLIT, TY_ANYTYPE, TY_OPAQUE, TY_TUPLE, TY_FLOAT, TY_CFLOAT };
typedef struct Type Type;
typedef struct Container Container;
typedef struct Scope Scope;
typedef struct Field { char *name; Type *t; int off; Node *def; int64_t val; void *defcv; /* CVal* default (from @Struct) */ int bitoff; int is_ct; int align; /* explicit align(N), 0 = natural */ /* comptime field: value in defcv */ } Field;
struct Container {
  Node *node; Scope *scope; char *name; Type *type;
  Vec fields; /* Field* */
  Vec decls;  /* Decl* */
  Type *tag; int tagged; int laid; int laying; int packed; int is_tuple; int nonexh; int layout_kind; /* 0 auto 1 extern 2 packed */
  char *tagnames_sym;
};
struct Type {
  int k, bits, sign, isconst, size, align;
  Type *elem; int64_t len; int hassent; int64_t sent;
  Container *ct;
  Vec params; Type *ret; int varargs; /* fn types */
  char *name;
  void *tinfo; /* cached @typeInfo CVal* */
};
/* comptime values */
enum { CV_NONE, CV_INT, CV_BOOL, CV_TYPE, CV_FN, CV_ENUMLIT, CV_NULL, CV_UNDEF, CV_ERR,
       CV_VOID, CV_STR, CV_AGG, CV_PTR, CV_SLICE, CV_FLOAT };
typedef struct Decl Decl;
/* comptime value.
   CV_AGG:   struct/tuple/array/union value; el[0..n) element cells (union: i = field index, el[0] payload)
   CV_PTR:   pointer into comptime memory: base cell, idx (-1 = the cell itself, else element index of an
             array/string cell); base == NULL && s: address of a runtime global symbol s (+ i bytes)
   CV_SLICE: base cell (array AGG or STR), idx = start, slen = len
   CV_STR:   string literal bytes s[0..slen) (t: the type it has been coerced to, or NULL) */
typedef __int128 i128;
typedef struct CVal { int k; i128 i; f128 f; Type *t; Decl *fn; char *s; int slen;
  struct CVal **el; int n; struct CVal *base; int64_t idx;
  int big; i128 ih; /* comptime_int beyond i128: value = ih * 2^128 + (u128)i (only when big) */ } CVal;

enum { D_UNRES, D_FN, D_CONST, D_VAR, D_FIELDLESS };
struct Decl {
  char *name; Node *node; Container *ct; int state; int kind;
  CVal cv; Type *t; char *sym; int emitted;
  Vec insts; /* FnInst* for generic fns */ int has_init;
};
typedef struct FnInst {
  Decl *d; Node *node; char *sym; Scope *scope; /* comptime bindings */
  Type *ty; Vec cargs; /* CVal* */ int queued, done, is_method_self;
  Vec ptypes; Type *ret;
  struct FnInst *from; Node *from_node;
} FnInst;

/* scopes */
enum { S_CVAL, S_LOCAL };
typedef struct Sym { char *name; int k; CVal cv; Type *t; char *addr; int mut; } Sym;
struct Scope { Scope *up; Container *ct; Vec syms; };

/* type API */
extern Type *t_void, *t_bool, *t_noret, *t_cint, *t_type, *t_null, *t_undef, *t_enumlit,
  *t_u8, *t_u16, *t_u32, *t_u64, *t_i32, *t_i64, *t_usize, *t_isize, *t_errset, *t_anytype, *t_u1,
  *t_cfloat, *t_f16, *t_f32, *t_f64, *t_f80, *t_f128;
Type *float_type(int bits);
#define is_float(t) ((t)->k == TY_FLOAT || (t)->k == TY_CFLOAT)
CVal cv_float(f128 f, Type *t); f128 fround(f128 f, Type *t);
i128 f_to_bits(f128 f, int bits); f128 bits_to_f(i128 v, int bits);
Type *int_type(int bits, int sign);
int bits_of(Type *t);
int is_tuple_type(Type *t);
char *cv_cstr(CVal *v, int *lenp);
int is_anon(Type *t);
Type *bt_type_pub(const char *path);
CVal cv_null_pub(void);
Type *ptr_to(Type *t, int isconst);
Type *bitptr_to(Type *t, int isconst, int hbytes, int bitoff);
Type *mptr_to(Type *t, int isconst, int hassent, int64_t sent);
Type *slice_of(Type *t, int isconst);
Type *slice_of_s(Type *t, int isconst, int hs, int64_t sent);
Type *array_of(Type *t, int64_t n, int hassent, int64_t sent);
Type *opt_of(Type *t);
Type *erru_of(Type *t);
Type *fn_type(Vec *params, Type *ret, int varargs);
int is_int(Type *t); int is_scalar(Type *t); int is_aggr(Type *t);
int opt_is_ptr(Type *t);
int tsize(Type *t); int talign(Type *t);
void layout(Container *c);
char *tname(Type *t);
int same_type(Type *a, Type *b);
Field *find_field(Container *c, const char *name);

/* sema */
Scope *new_scope(Scope *up, Container *ct);
void bind_cval(Scope *s, char *name, CVal v);
Sym *lookup_local(Scope *s, const char *name);
Container *container_from(Node *n, Scope *s, char *name);
Decl *find_decl(Container *c, const char *name);
Decl *lookup_decl_scope(Scope *s, const char *name);
void resolve_decl(Decl *d);
int ceval(Node *n, Scope *s, CVal *out);        /* fold if cheaply comptime-known (no side effects) */
int ceval_force(Node *n, Scope *s, CVal *out);  /* full comptime evaluation (comptime context) */
int ceval_rt(Node *n, Scope *s, Type *rt, CVal *out); /* forced, with result type */
int ct_try_assign(Node *n, Scope *s);
Type *mk_anon_struct_cv(Vec *names, Vec *types, int tuple, CVal **cts);
int ct_try_store(Node *dst, Node *n, Scope *s); /* builtin store (memset/memcpy) into a comptime var */           /* assignment to a comptime var from runtime code */
const char *ct_fail_loc(void);
i128 cv_pack(CVal *v); int cv_binop(const char *op, CVal a, CVal b, CVal *out); int cv_match(CVal *v, CVal *item);
int ceval_ex(Node *n, Scope *s, Type *rt, CVal *out); /* pure fold with result type */
Type *eval_type(Node *n, Scope *s);
CVal ccoerce(CVal v, Type *t);
CVal cv_int(i128 i, Type *t); CVal cv_bool(int b); CVal cv_ty(Type *t); CVal cv_void(void);
CVal cv_str(const char *s, int len);
CVal *box(CVal v); CVal cv_copy(CVal v);
Type *cv_typeof(CVal *v);
int cv_is_mem(CVal *v);
int cv_len(CVal *v, int64_t *len);
CVal cv_elem(CVal *v, int64_t i);
CVal *deref_cell(CVal *p);
int cval_eq(CVal *a, CVal *b);
int type_is_ctonly(Type *t);
int fn_takes_ctonly(Decl *fd);
int ceval_ret(Node *n, Scope *s, Type *rt, Type *fnrt, CVal *out, int *returned);
int fn_takes_ctonly(Decl *fd);
int fn_returns_ctonly(Decl *d);
Type *mk_anon_struct(Vec *names, Vec *types, int tuple);
Type *vec_of(Type *t, int64_t n);
#define is_vec(t) ((t)->k == TY_ARRAY && (t)->isconst == 2)
int is_packed(Type *t);
extern const char *std_file, *std_builtin_file, *builtin_file; extern int using_real_std;
Container *import_file(const char *path);
extern const char *root_dir;
extern Vec errnames;
int err_id(const char *name);
FnInst *fn_instance(Decl *d, Vec *cargs);
Type *call_type_fn(Decl *d, Vec *argnodes, Scope *s);
void bind_placeholder(Scope *s, char *name, Type *t);
char *mangle(const char *s);
Field *field_at(Type *t, int i); int field_index(Type *t, const char *name);
int fn_is_generic(Node *f);
extern Type *(*typeof_hook)(Node *n, Scope *s);

void types_init(void);
int lookup(Scope *s, const char *name, Sym **sy, Decl **dl);
int ceval_member(CVal base, const char *name, CVal *out);
int enum_val(Type *et, const char *name, int64_t *out);
int erru_off(Type *t);
int union_tag_off(Type *t);
i128 wrap_int(i128 v, Type *t);
Container *do_import(Node *n, const char *name);
Type *prim_type(const char *s);
Container *this_container(Scope *s);
extern const char *lib_dir;
/* gen */
void gen_fn(FnInst *fi);
void gen_global(Decl *d);
void queue_fn(FnInst *fi);
void gen_all(void);
void out(const char *f, ...);
extern FILE *outf;
CVal *cell_parent(CVal *c, int *fi);
