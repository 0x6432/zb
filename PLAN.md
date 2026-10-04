# zb — a bootstrap Zig compiler in C, targeting QBE (x86_64 only)

**Target language/std: Zig 0.17.0 only** (0.16 support dropped; achieved: 0.17 bootstrap fixed point).

## 0. Reality check / end goal
The real goal of a Zig bootstrap compiler is to compile the Zig compiler itself
(`src/main.zig` + `lib/std`). That code uses heavy comptime (generics, `@typeInfo`,
`inline for`, comptime format strings, `@Type`), so the compiler needs a comptime
interpreter, not only a code generator. We get there in milestones; every milestone is
a working compiler that is tested end-to-end (zig -> QBE IL -> qbe -> as/cc -> run).
Assumptions (as allowed): input is valid Zig (no diagnostics beyond "die"), target is
x86_64 SysV only, no safety checks (overflow/bounds/unreachable are UB / `hlt`).

## Scope
Core language only: no build runner, no build.zig / std.Build, no package manager,
no `zig test` runner, no cImport. The driver is `zb file.zig > out.ssa`.

## 1. Architecture (single pass per function, lazy whole-program)
```
 .zig --lex--> tokens --parse--> AST (per file = struct container)
   --lazy decl resolution + comptime eval (types, consts, generics)
   --typed codegen (sema fused into codegen)--> QBE IL text --qbe--> asm --cc--> exe
```
* src/zb.h     shared types (Vec, Tok, Node, Type, Container, Decl, CVal, Val)
* src/lex.c    full Zig token set: ints (0x/0o/0b/_), chars, strings + escapes, `\\` multiline,
               `@builtin`, `@"ident"`, all operators (`+%=`, `<<|`, `.*`, `.?`, `...`)
* src/parse.c  recursive descent following the official Zig PEG grammar
               (types are expressions; CurlySuffix init lists; statement-vs-expression bodies)
* src/sema.c   type interning, layouts, containers, lazy decl resolution, comptime evaluator
* src/gen.c    typed codegen to QBE: expressions, control flow, defers, calls, data
* src/main.c   driver: entry file, `main` wrapper, function worklist, output

## 2. Data model
* Type kinds: void, bool, noreturn, iN/uN (1..64), comptime_int, `*T`, `[*]T`, `[]T`, `[N]T`,
  struct, enum, union / union(enum), `?T`, `E!T`, error set (global anyerror, u16), `type`, fn.
* QBE classes: ints<=32/bool/enum/error -> `w`; i64/u64/pointers -> `l`;
  everything else is an *aggregate* living in memory and handled by address.
* Layouts: natural C-like alignment. Slice = {ptr,len}. `?*T` = nullable ptr;
  other `?T` = {T, u8 has}. `E!T` = {u16 err, T}. union(enum) = {payload, tag}.
* Internal calling convention: scalars by value, aggregates by pointer, aggregate
  return via hidden sret pointer. `extern`/`export` fns use the C ABI (scalars + varargs).
* Values in codegen: `Val{type, operand, is_lvalue, comptime_value?}`; comptime-known
  values stay symbolic until coerced to a runtime type (comptime_int, enum literals, null...).

## 3. Semantics plan
* Lazy, order-independent decls: a file is a struct; `@import("x.zig")` loads another file.
  Decls are resolved on first use (fn -> queued for codegen, const -> comptime value
  or static data, var -> global).
* Comptime evaluator (M1): integer/bool arithmetic, type expressions, `T == U`,
  comptime `if`/`switch` pruning, `@sizeOf`, `@TypeOf` (via a dry-run codegen),
  `@This`, `@hasDecl`, `@hasField`.
* Generics: `comptime` params are monomorphized and memoized per argument tuple;
  `fn Foo(comptime T: type) type { ...; return struct {...}; }` evaluated at comptime.
* Result-location typing: `expect` type is threaded down so `.{}`, `.tag`, `null`,
  integer literals and `undefined` get their types.
* Control flow: if/while/for/switch as expressions with captures (`|x|`, `|*x|`, `|x, i|`),
  labeled blocks/loops with `break :l v`, `defer`/`errdefer` (run on every exit edge),
  `try`, `catch |e|`, `orelse`, `.?`, `unreachable`.
* Coercions: comptime_int->int, int widening, T->?T, null->?T, T->E!T, error->E!T,
  `*[N]T`->`[]T`/`[*]T`, mut->const ptr, enum literal->enum, anon struct -> struct/array/union.

## 4. Milestones
* **M1 (this drop)**: everything in §2-§3 above + builtins (@as @intCast @truncate
  @bitCast @ptrCast @alignCast @constCast @intFromPtr @ptrFromInt @intFromBool
  @intFromEnum @enumFromInt @sizeOf @alignOf @TypeOf @tagName @errorName @memcpy
  @memset @min @max @divTrunc @divFloor @mod @rem @panic @embedFile @field @This
  @import @intFromError @trap), extern C functions, a tiny `lib/std.zig` shim, test suite.
* **M2**: real comptime interpreter (call arbitrary fns at comptime, comptime vars,
  `inline for/while`, `anytype`, tuples, `@typeInfo`, comptime strings/`++`/`**`),
  so `std.fmt`/`std.debug.print` work.
* **M3**: packed structs/bitfields, u128/i128 (pairs of `l`), floats (QBE `s`/`d`),
  `@addWithOverflow` & friends, `@clz/@ctz/@popCount`, vectors scalarized, threadlocal.
* **M4**: the core-language features needed by `lib/std` (inline asm for syscalls, `@cmpxchg`/atomics,
  `@fieldParentPtr`, `@call`, `@Type`), still core language only, with no build system.

## 5. Testing
`tests/*.zig` each print/exit with a known code; `make test` compiles each with zb,
runs qbe + cc, executes, compares against `tests/*.expected`.
