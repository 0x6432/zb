# Handoff notes (resume here)

## State
- M1–M3 done. 20 core tests + 7 real-std tests pass (`./run_tests.sh`; std tests need `zig-0.16.0/lib`).
- Setup after a fresh checkout: download qbe-1.2 (build with make) into `qbe-1.2/` and extract
  `zig-x86_64-linux-0.16.0/lib` into `zig-0.16.0/lib`.
- Real std: `lib/builtin_std.zig` stands in for the generated `builtin` module (link_libc = true);
  `lib/zb_start.zig` is the entry glue for `main(init: std.process.Init)`.

## Debug aids
- `ZB_TRAPLOC=1` (runtime trap locations), `ZB_CT_TRACE=1`, `ZB_BT=1` (+ `cc -O0 -g -rdynamic -o zbg src/*.c -lm`, addr2line), `ZB_DBG=1`.

## Ideas for next steps
1. More real-std coverage (std.json, std.Io.Reader line reading, std.process.Child, std.Thread).
2. Runtime safety checks (integer overflow, bounds, `.?` on null) to match Debug-mode Zig panics.
3. Runtime f128/f80 via libgcc soft-float (`__addtf3` etc.), 128-bit int <-> float.
4. Compile the Zig compiler sources (`src/`) – the long-term bootstrap target.
