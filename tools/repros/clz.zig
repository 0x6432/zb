const std = @import("std");
pub fn main() void {
    var a: u113 = 1; var b: u128 = 1 << 70; var c: u113 = 1 << 100; var d: u65 = 3;
    _ = &a; _ = &b; _ = &c; _ = &d;
    std.debug.print("{d} {d} {d} {d} {d} {d}\n", .{ @clz(a), @clz(b), @clz(c), @clz(d), std.math.log2(a), @ctz(c) });
}
