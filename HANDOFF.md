# zb handoff (target: Zig 0.17.0 only)

## What it is
`zb` (C, ~src/*.c) compiles Zig 0.17.0 → QBE IL → x86_64 asm; link with `<out>.asm.s` (inline-asm stubs) and
`tools/zbrt.c`. Input assumed valid. Repo: GitHub `0x6432/zb` (branch `main`); backups are numbered `backup-NN`
lines in `MILESTONES` (the milestone-tag workflow creates the tags).

## Status
- Zig 0.17.0 bootstrap fixed point: zb-built `zig17_2` and gcc-built `zig17_3` self-compile byte-identically (`-j1`).
- Full core language incl. 0.17 changes (std.lang, SoA @typeInfo, @backingInt/@fromBackingInt/@divCeil, logical
  @bitCast, pub-only @hasDecl, comptime-length slice deref), @export/@extern, @cVa*, precise error sets
  (named, `||`, inferred via lazy fn analysis), f80/f128, general inline asm.
- Tests: `./run_tests.sh` → 37/37 (tests/, tests/std/, tests/std17/ against `zig-0.17.0/lib/std`).

## Setup (sandbox resets /tmp and packages; /data may be rolled back — resync from GitHub if git log looks old)
```
sudo dnf install -y -q gdb gc-devel
cd /data/zb && ln -sfn /data/zig17-src zig-0.17.0 && make GC=1 -s && ./run_tests.sh
```
- Zig 0.17 source: /data/zig17-src (`config.zig` = tools/config17.zig; no aro module). QBE: zb/qbe-1.2.
- Resync: `git clone https://github.com/0x6432/zb /tmp/zbgh` (works without auth) and copy files over.
- Push: write `{owner,repo,branch,message,files:[{path,content}]}` JSON (≤~400KB) and call GitHub MCP
  `push_files` with `arguments_file_path`; deletions need `delete_file`.

## Scripts
- `tools/run.sh f.zig --std-dir /data/zb/zig-0.17.0/lib/std` — compile + run one file.
- `tools/build17.sh` — zb → /data/zig17_2 (~10 min; `ZB_DBG=1` for line info).
- `tools/boot17.sh` — compiler_rt17.c, zig17_2 self → stage.sh → zig17_3 → self → cmp.
- `tools/stage.sh IN.c OUT` — split (csplit.py) + cc + link Zig C output.
- Reference outputs from real 0.17: `cd /data/zig17-src && /data/zig17_3 build-exe -ofmt=c -lc -OReleaseSmall
  -femit-bin=/tmp/x.c -target x86_64-linux --zig-lib-dir lib f.zig && cc -w -I lib -o /tmp/x /tmp/x.c -lm`.
- CI: `ci/bootstrap.sh` stages zb / zig2 / stages / compare / stage3 (workflow `.github/workflows/bootstrap.yml`).

## Debug aids
`ZB_TRAPLOC=1`, `ZB_CT_TRACE=1`, `ZB_BT=1`, `ZB_DBG=1`, `ZB_TRACE_FN=1`; gdb on zb for crashes.

## Code map
- lex.c/parse.c (top-level `comptime {}` kept as N_COMPTIME decls), sema.c (types, layout, error-set types,
  fn_instance), ct.c (comptime interpreter, builtins, @typeInfo), gen.c (QBE codegen, coerce, inline asm,
  exports, eset_resolve), main.c (driver; `zig17` flag set when std has lang.zig).
- Error sets: TY_ERRSET with ct->fields = names (anyerror = t_errset, ct NULL); TY_ERRU set in t->ret
  (erru_of2). Inferred sets collect entries in coerce/gen_try and resolve by generating the fn re-entrantly.

## Open items
- Error-set name order differs from Zig (Zig uses global string intern order).
- No runtime safety checks (ReleaseFast-like).
- CI stage3 (`zig build` with the bootstrapped compiler) was only verified on 0.16.
