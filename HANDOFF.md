# zb — handoff notes (for the next agent)

## Goal
User (Teyesh) wants a **simple bootstrap compiler written in C** that compiles **Zig 0.16** source to **QBE IL**
(then `qbe` → asm → `cc`). x86_64 Linux only, assume valid input code, core language only.
Milestones done: M1 (core codegen), M2 (comptime interpreter + `--std-dir <zig>/lib/std` so `@import("std")`
uses the real Zig std), M3 (enough of std to run real programs incl. std.debug.print, std.Io.Threaded file IO).
**Current task (M4): user asked "can it compile the Zig compiler?"** — answer so far: *not yet*, iterating on
compile errors while compiling the real Zig 0.16 compiler source. Report honest status to the user when done/blocked.

## Layout
- `src/*.c, src/zb.h` — lexer, parser, sema (`sema.c`: decls/imports/modules/layout), `ct.c` (comptime interpreter,
  CVal), `gen.c` (QBE codegen, typeof dry runs, inline expansion, peer types).
- `tests/` + `./run_tests.sh` → must stay **28 passed** (expected files end with `exit=0` line).
- Build: `rm -f zb && make`. Debug build: `cc -O0 -g -rdynamic -w -o zbg src/*.c -lm` (+ `addr2line -e zbg` on frames).
- Needs (not in zip, re-download if missing): `qbe-1.2/` (build with make) and `zig-0.16.0/lib` (Zig std) inside /data/zb;
  Zig compiler source at `/data/zig-src` (https://ziglang.org/download/0.16.0/zig-0.16.0.tar.xz) plus
  `/data/zig-src/config.zig` = the build_options module: copy the `build_options` Zig text that `bootstrap.c` writes
  (have_llvm=false, dev=.core, etc.) into that file.

## Helper scripts (copies are in tools/zc.sh and tools/run.sh)
/tmp/zc.sh:
```sh
#!/bin/sh
cd /data/zb && rm -f zb && make 2>&1 | grep -iE '\berror\b'
cd /data/zig-src && ZB_FLOAT_HACK=1 timeout 300 /data/zb/zb src/main.zig -o /tmp/zig2.ssa --std-dir lib/std \
  -Mbuild_options=config.zig -Maro=lib/compiler/aro/aro.zig 2>&1 | head -${1:-8} | cut -c1-300
```
/tmp/t/run.sh (`./run.sh file.zig --std-dir /data/zb/zig-0.16.0/lib/std`):
```sh
#!/bin/sh
f=$1; shift
/data/zb/zb "$f" -o /tmp/t/out.ssa "$@" && /data/zb/qbe-1.2/qbe -o /tmp/t/out.s /tmp/t/out.ssa && cc -o /tmp/t/out /tmp/t/out.s -lm && /tmp/t/out
```
Workflow: run zc.sh → read error (it prints an instantiation chain) → write a tiny repro in /tmp/t → fix → run tests → commit.

## Debug env vars
`ZB_TRAPLOC`, `ZB_CT_TRACE=1`, `ZB_BT=1`, `ZB_INST_STAT=1` (decls with ≥64 instances), `ZB_NOINLINE=1`, `ZB_INLDBG=1`,
`ZB_DBG=1`, `ZB_FLOAT_HACK=1` (TEMPORARY/WRONG: maps f16/f80/f128 to s/d QBE classes just to explore later errors).
No gdb in sandbox. Don't `pkill -f` patterns that match your own shell.

## Recent fixes (this session, latest first; see git log for detail)
- Optional Boehm GC (make GC=1); comptime self params; type-constructor builtins force comptime; &comptime-tuple -> array;
  comptime-known for-range lengths; quoted @"null" idents; 128-bit int<->float; runtime `**`; tuple .len.
- Branch results under partial tuple hints (`const a, const b: T = switch ...`) are peer-resolved (ex_partial()).
- Runtime tuple `.len`; `@unionInit` with computed names; runtime `**` for tuples/arrays.
- 128-bit int <-> float via libgcc (__floattidf, __fixdfti, ...).
- Comptime slice `.len`/`.ptr` assignment; `&.{}` (ptr to tuple) -> slice/many-ptr; `.*` of `++` result.
- ZON `@import("x.zon")` with result types; `.{}` -> slice at comptime.
- inline else over bool/small ints, inline prong ranges; lenient runtime fallback for failing `comptime` calls.
- Peer types for for/while loop expressions; quoted `@"_"` enum fields; @typeInfo of generic fns.
- Wide (u128-window) packed fields; wide comptime_int (>i128, `big`/`ih` in CVal; ev_bin_wide).
- Bit-pointers to packed fields; explicit field align(N); comptime fields in anon structs (Field.is_ct/defcv).
- @memset/@memcpy into comptime vars (ct_try_store); lenient `try` on non-error values; runtime tuple `++`.

## CURRENT ERROR (next thing to fix)
```
zb: src/codegen/aarch64/Assemble.zig:163: cannot coerce anon2909 to anon2915
```
Cause: inline param types like `form: union(enum) {...}` get a new container type each time the param type is evaluated
(container_from memo keyed by Scope pointer). Repro /tmp/t/a17.zig (in tools/repros if copied). An experimental fix
`scope_equiv()` in sema.c (enable with env ZB_CT_MEMO=1) fixes the repro but over-merges elsewhere
(-> "cannot coerce SortOrder to SortOrder" in multi_array_list.zig:605). Needs a precise key: only the comptime
values the container body actually references (or memo per FnInst/fn-type evaluation).
Also noticed: `d + switch(...)` with u8 + u16 peer computes in u8 (a17 prints 46, should be 302).

Build: `make GC=1` (Boehm GC, needs gc-devel) — without GC the full compile OOMs at 4 GB; with GC peak ~2.8 GB.
Setup: Zig source at /data/zig-src (+ config.zig build_options), lib copy at zb/zig-0.16.0/lib, qbe at zb/qbe-1.2.
Tests: ./run_tests.sh must stay "passed 28, failed 0".

## Known big remaining items
1. Runtime f16/f80/f128 (only f32/f64 real today). Plan: f16 via f32 conversions; f80/f128 as 16-byte memory values
   with soft-float helpers (port compiler_rt add/sub/mul/div/cmp/extend/trunc/int-conv, in C runtime or Zig).
2. Inferred error sets not tracked; destructuring loses comptime tuple fields (comptime_int handled leniently).
3. Inline asm: only `syscall` supported; `cpuid`/`xgetbv` compile as traps → needs a linked helper .s/.c runtime.
4. After it compiles: actually build & run the produced zig2 binary (runtime correctness, perf), compiler_rt.

## Backups
Zip (excluding big deps): `cd /data && zip -qr zb_backup.zip zb -x 'zb/zig-0.16.0/*' 'zb/qbe-1.2/*' 'zb/zig.tar.xz' 'zb/build/*' 'zb/zb' 'zb/zbg'`
User wants periodic backups + git commits.

## Status update (M4, latest)
- zb compiles the whole Zig 0.16 compiler -> QBE -> working `zig2` binary (`tools/build2.sh`, needs `make GC=1`, links `tools/zbrt.c`).
- **zb-built zig2 works end to end for hello world**: `zig2 build-exe -ofmt=c -lc ... h2.zig` -> C -> cc -> runs correctly.
- Current blocker: `zig2 build-obj ... -Mroot=lib/compiler_rt.zig` (bootstrap step). Last trap was in big.int setFloat (wide @clz bug), now fixed in zb but zig2 is **not yet rebuilt/retested** with that fix.
- Next: rebuild zig2 (`ZB_DBG=1 ZB_TRAPLOC=1 tools/build2.sh`), rerun compiler_rt (`tools/rz2.sh build-obj -ofmt=c -OReleaseSmall --name compiler_rt -femit-bin=/tmp/zt/compiler_rt.c -target x86_64-linux --zig-lib-dir lib -Mroot=lib/compiler_rt.zig`), then zig2.c self-build.
- Debug aids: `ZB_DBG=1` emits line info (gdb shows Zig file:line); `tools/rz2.sh` runs zig2 under gdb with backtrace at traps. Needs `sudo dnf install gdb gc-devel` after sandbox reset. Helper scripts live in tools/ (copy to /tmp).
- f16/f80/f128 at runtime: kept in f32/f64 registers, real memory format via zbrt shims (approximate precision).
- Fixes this round: &agg.field comptime pointers keep parent; @ptrCast slice->?slice len; ?T==T compares; saturating ops; nested packed struct bit size; switch |*x| captures alias operand; wide @clz/@ctz/@popCount.

## BOOTSTRAP COMPLETE (fixed point)
Chain: zb (C) compiles Zig 0.16 compiler -> QBE -> `zig2` (tools/build2.sh).
- `zig2 build-obj ... -Mroot=lib/compiler_rt.zig` -> compiler_rt.c (OK)
- `tools/self.sh`: zig2 compiles src/main.zig to C (`/data/zig2_self.c`, 218MB, ~2 min). EXIT 0.
- gcc OOMs (4GB) on one 218MB TU -> `tools/csplit.py` splits it into header + 10 TUs; `tools/stage.sh IN.c OUTBIN` compiles+links (~3 min).
- zig3 = stage.sh(zig2_self.c); zig3 compiles itself -> zig3_self.c; zig4 = stage.sh(zig3_self.c); zig4 -> zig4_self.c.
- **zig3_self.c == zig4_self.c byte-for-byte.** zig2_self.c differs from them only in 12 f128 constant lines
  (zb keeps f128 at f64 precision at runtime) plus resulting InternPool numbering.
Remaining polish: real f128/f80 runtime precision in zb (so zig2 output matches directly); a17 u8+u16 peer bug;
inline asm beyond syscall; assembler "value truncated" warnings.

## Session update (f128, asm, 0.17)
- Done: a17 peer fix; general inline asm (stubs in `<out>.asm.s`, must be linked); f80/f128 full precision (16-byte memory values + zbrt.c shims; link tools/zbrt.c); packed union bit sizes; f80 signbit (wide-int bitcast sign-extend).
- zig2_self.c == zig3_self.c modulo numbering; numbering differences are InternPool thread nondeterminism -> self-compiles now use `-j1`.
- stage3 (`zig4 build -p /data/stage3 -Dno-lib`) works: fmt/ast-check/run hello OK.
- Zig 0.17.0: release notes at /data/zig-0.17.0-release-notes.md, source /data/zig17-src (config.zig = tools/config17.zig, no aro module).
  zb supports std.lang, SoA @typeInfo, @backingInt/@fromBackingInt/@divCeil, builtin_std17.zig. `STD=/data/zig17-src/lib/std ./run_tests.sh` passes.
  Compiling the 0.17 compiler: `cd /data/zig17-src && /data/zb/zb src/main.zig -o /data/zig17_2.ssa --std-dir lib/std -Mbuild_options=config.zig`
  Next failure: lib/std/mem.zig:2327 (byteSwapAligned) "expected comptime type expression".
