# Next steps (target: Zig 0.17.0 only)
1. Keep `./run_tests.sh` green on `zig-0.17.0/lib/std`; add 0.17 tests to `tests/std17/` (expected output from a real 0.17 compiler, e.g. `/data/zig17_3`).
2. Re-run `tools/build17.sh` + `tools/boot17.sh` after compiler changes; the zig17_2 vs zig17_3 self output must stay byte-identical.
3. Optional: runtime safety checks (overflow, bounds, `.?`) for Debug-mode parity; error-set name ordering like Zig's intern order.
