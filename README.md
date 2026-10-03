# zb: a bootstrap Zig compiler in C → QBE (x86_64)

`zb` compiles the **core Zig language** (as of Zig 0.16.0) to QBE IL. QBE turns that into x86_64 assembly, and `cc` links it against libc.
It's about 5k lines of C (GCC/Clang: uses `__int128`/`__float128`), no other dependencies. See `PLAN.md` for the design and the milestone roadmap.

```
make                      # builds ./zb (needs only a C compiler)
./zb prog.zig -o prog.ssa
qbe -o prog.s prog.ssa && cc -o prog prog.s -lm && ./prog
./zb prog.zig --std-dir zig-0.16.0/lib/std -o prog.ssa   # use the real Zig std
./run_tests.sh            # end-to-end tests in tests/ (+ tests/std/ when zig-0.16.0/ is present)
./parse_check.sh zig-0.16.0   # parser coverage on the real Zig tree (990/990 files)
```

## What works (milestone 1)
* Lexer and parser: the full Zig 0.16 grammar. Every `.zig` file in `lib/std` and `src/` of
  zig-0.16.0 parses, including labeled switch, destructuring, tuples, multiline strings, and asm syntax.
* Types: `u1..u64`/`i1..i64`, `usize`, `c_int`…, `bool`, `void`, `noreturn`, pointers `*T`, `[*]T`,
  `[*:0]T`, slices `[]T`/`[:0]T`, arrays `[N]T`/`[_]T`, structs (incl. file-as-struct with
  top-level fields, tuples), enums (explicit tag types/values), `union(enum)`/`union(E)`/bare unions,
  optionals `?T` (null-pointer optimized), error unions `E!T` / inferred `!T`, error sets incl. `||`,
  function pointers.
* Control flow: `if`/`while`/`for` as expressions with captures `|x|`, `|*x|`, `|x, i|`,
  multi-object `for`, ranges `0..n`, `while (…) : (…)`, `else` branches, labeled blocks and loops,
  `break :l v`, `continue`, labeled `switch` with `continue :sw v`, switch ranges/multi-items/union
  payload captures, `defer`, `errdefer |e|`, `try`, `catch |e|`, `orelse`, `.?`, `unreachable`.
* Comptime: constant folding, type expressions, `comptime` params and `anytype` (monomorphized and
  memoized), type-returning functions (`fn List(comptime T: type) type`), `@This()`, comptime
  `if`/`switch` pruning (`builtin.os.tag == .linux`), `@import` of files/`std`/`builtin`/`root`.
* Builtins: `@as @intCast @truncate @bitCast @ptrCast @alignCast @constCast @intFromPtr @ptrFromInt
  @intFromBool @intFromEnum @enumFromInt @intFromError @errorFromInt @sizeOf @alignOf @bitSizeOf
  @offsetOf @FieldType @TypeOf @typeName @tagName @errorName @memcpy @memset @min @max @abs
  @divTrunc @divFloor @divExact @mod @rem @shlExact @shrExact @clz @ctz @popCount @panic @trap
  @embedFile @field @hasDecl @hasField @unionInit @compileError`, plus no-op hints.
* `extern fn`/`export fn`/`extern var`, C varargs; `pub fn main()` returning `void`, `u8`, `!void`
  or `!u8`. An error returned from main prints `error: Name` and exits with 1.

## Milestones 2–3 (current)
* **Comptime interpreter**: arbitrary function calls at comptime, comptime vars/loops,
  `inline for/while`, `@typeInfo`, `@Int/@Struct/@Enum/@Union/@Pointer/@Tuple`, comptime format strings,
  memoized generic instances.
* **Real Zig std**: `--std-dir zig-0.16.0/lib/std` compiles against the unmodified Zig 0.16 std.
  Tested so far: `std.debug.print` with all common format specs, `std.fmt` (bufPrint/allocPrint/parseInt/parseFloat),
  `std.mem` (split/tokenize/trim/sort/eql/indexOf), `ArrayList`, `AutoHashMap(Unmanaged)`, `StringHashMap`,
  `FixedBufferAllocator`, `DebugAllocator`, `page_allocator`, `std.math`, and `pub fn main(init: std.process.Init)`
  with `std.Io.Threaded` (stdout writer, file create/read/write/delete, args, environ). See `tests/std/`.
  Without `--std-dir`, the small shim in `lib/std.zig` is used.
* **Floats**: `f16/f32/f64` at runtime (QBE `s`/`d`), `comptime_float` as IEEE binary128 (exact like Zig),
  `f80/f128` at comptime only. Conversions, `@sqrt/@sin/.../@floor/@round/@mulAdd`, `@bitCast` to/from ints,
  Zig-style shortest round-trip printing.
* **128-bit integers** at runtime, packed structs (bit fields), vectors (scalarized), atomics, `@call`,
  `@fieldParentPtr`, inline asm `syscall` (other asm compiles to a trap with a warning).
* Debug aids: `ZB_TRAPLOC=1` makes every trap (`unreachable`, failed safety check) print its source location;
  `ZB_CT_TRACE=1` traces comptime failures; `ZB_BT=1` prints a backtrace on compiler errors.

## Not yet
* Runtime `f80`/`f128`, 128-bit int ↔ float conversions, general inline asm, threads beyond what `std.Io.Threaded`
  needs for single-threaded use, runtime safety checks (overflow/bounds are unchecked).
* Scope: core language only. No build runner, build.zig, package manager, or test runner.
