#include "zb.h"
#include <signal.h>
#include <execinfo.h>
#include <unistd.h>
const char *lib_dir;
void add_module(const char *name, const char *path);
void gen_init_buffers(void); void gen_main_wrapper(FnInst *mi, int glue); void gen_finish(void);
static void on_segv(int sig) {
  void *bt[64]; int n = backtrace(bt, 64);
  fprintf(stderr, "zb: internal error (signal %d)\n", sig); backtrace_symbols_fd(bt, n, 2); _exit(3);
}
static void on_alarm(int sig) { (void)sig; extern const char *ct_cur_loc(void); extern Node *gen_cur_pub(void); Node *g = gen_cur_pub();
  fprintf(stderr, "zb: alarm: ct at %s, gen at %s:%d\n", ct_cur_loc(), g && g->tok ? g->tok->file : "?", g && g->tok ? g->tok->line : 0);
  void *bt[64]; int n = backtrace(bt, 64); backtrace_symbols_fd(bt, n, 2); _exit(4); }
#ifdef ZB_GC
#include <gc.h>
#endif
int main(int argc, char **argv) {
#ifdef ZB_GC
  GC_INIT();
#endif
  if (getenv("ZB_ALARM")) { signal(SIGALRM, on_alarm); alarm(atoi(getenv("ZB_ALARM"))); }
  signal(SIGSEGV, on_segv); signal(SIGABRT, on_segv);
  if (argc < 2) { fprintf(stderr, "usage: zb file.zig [-o out.ssa] [--std-dir <zig>/lib/std]\n"); return 2; }
  const char *in = NULL, *o = NULL, *stddir = getenv("ZB_STD_DIR");
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-o") && i + 1 < argc) o = argv[++i];
    else if (!strcmp(argv[i], "--std-dir") && i + 1 < argc) stddir = argv[++i];
    else if (!strncmp(argv[i], "--std-dir=", 10)) stddir = argv[i] + 10;
    else if (!strncmp(argv[i], "-M", 2) && strchr(argv[i], '=')) { char *e = strchr(argv[i], '='); add_module(xstrndup(argv[i] + 2, e - argv[i] - 2), e + 1); }
    else if (!strcmp(argv[i], "--dep") && i + 1 < argc) i++;
    else if (!in) in = argv[i];
    else die("unexpected argument %s", argv[i]);
  }
  if (!in) die("no input file");
  lib_dir = getenv("ZB_LIB");
  if (!lib_dir) { char *self = realpath(argv[0], NULL); if (!self) self = realpath("/proc/self/exe", NULL); char *sl = strrchr(self, '/'); *sl = 0; lib_dir = fmt("%s/lib", self); }
  if (stddir && *stddir) {
    char *rd = realpath(stddir, NULL); if (!rd) die("--std-dir: cannot open %s", stddir);
    std_file = fmt("%s/std.zig", rd); std_builtin_file = fmt("%s/builtin.zig", rd); if (access(std_builtin_file, R_OK)) std_builtin_file = fmt("%s/lang.zig", rd); /* 0.17: std.builtin -> std.lang */
    builtin_file = fmt(strstr(std_builtin_file, "/lang.zig") ? "%s/builtin_std17.zig" : "%s/builtin_std.zig", lib_dir); using_real_std = 1;
  }
  if (!std_file) { std_file = fmt("%s/std.zig", lib_dir); std_builtin_file = fmt("%s/std/builtin.zig", lib_dir); builtin_file = fmt("%s/builtin.zig", lib_dir); }
  if (getenv("ZB_PARSE_ONLY")) { parse_file(in); return 0; }
  { extern FILE *asm_out; if (o) { asm_out = fopen(fmt("%s.asm.s", o), "w"); if (!asm_out) die("cannot write %s.asm.s", o); } }
  outf = o ? fopen(o, "w") : stdout; if (!outf) die("cannot write %s", o);
  types_init(); gen_init_buffers();
  root_dir = realpath(in, NULL); if (!root_dir) die("cannot open %s", in);
  Container *root = import_file(root_dir);
  Decl *md = find_decl(root, "main");
  for (int i = 0; i < root->decls.n; i++) {
    Decl *d = root->decls.a[i];
    if (d->node->k == N_FN && (d->node->flags & F_EXPORT)) { resolve_decl(d); Vec c = {0}; for (int j = 0; j < d->node->list.n; j++) vpush(&c, NULL); fn_instance(d, &c); }
  }
  FnInst *mi = NULL;
  int start_glue = 0;
  if (md && using_real_std && md->node->k == N_FN && md->node->list.n > 0) {
    Container *sc = import_file(fmt("%s/zb_start.zig", lib_dir)); Decl *zd = find_decl(sc, "zbMain");
    if (!zd) die("zb_start.zig: no zbMain"); resolve_decl(zd); Vec c = {0}; for (int j = 0; j < zd->node->list.n; j++) vpush(&c, NULL); mi = fn_instance(zd, &c); start_glue = 1;
  } else if (md) { resolve_decl(md); Vec c = {0}; mi = fn_instance(md, &c); }
  gen_all();
  if (mi) gen_main_wrapper(mi, start_glue);
  gen_finish();
  if (o) { extern FILE *asm_out; fclose(outf); fclose(asm_out); }
  return 0;
}
