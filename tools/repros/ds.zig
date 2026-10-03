const std = @import("std");
const E = enum { exact, inexact };
fn g(comptime F: type, x: u32) struct { F, E } {
    const n: struct { a: F } = .{ .a = @floatFromInt(x) };
    return .{ n.a, .inexact };
}
pub fn main() void {
    var x: u32 = 5; _ = &x;
    const r = g(f64, x);
    const f, const e = g(f64, x);
    std.debug.print("{d} {t} {d} {t}\n", .{ r[0], r[1], f, e });
}
