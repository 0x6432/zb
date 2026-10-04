# zb: a bootstrap Zig compiler in C → QBE (x86_64 Linux)

`zb` compiles **Zig 0.17.0** source to QBE IL; QBE emits x86_64 assembly and `cc` links it with libc and
`tools/zbrt.c` (small runtime: f80/f128 shims, bit-stream helpers). C99 + GCC/Clang extensions (`__int128`,
`__float128`), optional Boehm GC (`make GC=1`). Input is assumed to be valid Zig (no semantic diagnostics).
Only Zig **0.17.0** is targeted; 0.16 support is no longer maintained or tested.

```
make GC=1                                   # builds ./zb
./zb prog.zig -o prog.ssa --std-dir zig-0.17.0/lib/std
qbe -o prog.s prog.ssa && cc -o prog prog.s prog.ssa.asm.s tools/zbrt.c -lm && ./prog
./run_tests.sh                              # tests/, tests/std/, tests/std17/ (std tests need zig-0.17.0/lib/std)
./parse_check.sh zig-0.17.0                 # parser coverage over the Zig tree
```
`<out>.asm.s` holds inline-asm stubs and must be linked too.

## Status
* **Bootstraps Zig 0.17.0**: zb compiles the 0.17 compiler (`tools/build17.sh` → `zig17_2`); `zig17_2` and a
  gcc-built `zig17_3` produce byte-identical self-compiles (`-j1`; `tools/boot17.sh`). CI: `ci/bootstrap.sh`.
* Full 0.17 core language: comptime interpreter, generics, `@typeInfo` (struct-of-arrays `std.lang.Type`),
  `@backingInt/@fromBackingInt/@divCeil`, 0.17 `@bitCast` (logical bit representation), pub-only `@hasDecl`,
  comptime-length slice deref/coercion, packed structs/unions, vectors, atomics, 128-bit ints, f16/f32/f64/f80/f128,
  general inline asm, `@export/@extern`, C varargs (`@cVaStart/Arg/Copy/End`), precise error set types
  (named, `||`, inferred `!T` sets visible to `@typeInfo`).
* Real unmodified std (`--std-dir`): `lib/builtin_std17.zig` replaces the generated `builtin` module,
  `lib/zb_start.zig` is the entry glue. Without `--std-dir` the small shim in `lib/std.zig` is used.
* Not implemented (not needed on x86_64 Linux): GPU/wasm builtins, async `@Frame`. Runtime safety checks are off
  (ReleaseFast-like semantics).

Debug aids: `ZB_TRAPLOC=1` (trap source locations), `ZB_CT_TRACE=1`, `ZB_BT=1`, `ZB_DBG=1` (QBE line info).
See `HANDOFF.md` for working notes and `PLAN.md` for the design.

## `zig` driver (driver/zig.zig)
A small `zig`-compatible front end written in Zig and compiled by zb: `./driver/build.sh` → `bin/zig`.
Uses `zig-0.17.0/lib` next to the repo (override: `ZB_ZIG_LIB`), cache `~/.cache/zb-zig` (`ZIG_GLOBAL_CACHE_DIR`).
* `zig build-exe|build-obj|build-lib file.zig [-femit-bin=..] [--name ..] [-dynamic] [-lc] [x.c] [-lfoo]` — zb → QBE → cc/ld/ar.
* `zig run file.zig [-- args]`, `zig version`, `zig env`.
* `zig build|fetch|init` — compile `lib/compiler/Maker.zig` with zb and exec it (implements the `--listen=-`
  compiler-server subset the build system uses). **Not working yet**: Maker pulls in std.crypto (TLS for
  fetching), whose comptime constants need >128-bit comptime integers, which zb does not support yet.
