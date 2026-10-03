const std = @import("std");
fn f(a: u16, b: u16) u16 { return @max(a, b); }
fn g(a: u16, b: u16, s: bool) struct { bool, u16 } { return .{ s, @max(a, b) }; }
pub fn main() void {
    var a: u16 = 4; var b: u16 = 3; var s = false; _ = &a; _ = &b; _ = &s;
    const r = g(a, b, s);
    std.debug.print("{d} {d} {d} {d}\n", .{ f(a, b), @max(a, b), @min(a, b), r[1] });
}
