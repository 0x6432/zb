const std = @import("std");
pub fn main() void {
    var a: f80 = -1.5; _ = &a;
    var z: f80 = -0.0; _ = &z;
    var q: f128 = -2.5; _ = &q;
    std.debug.print("{x} {x} {x} {} {}\n", .{ a, z, q, std.math.signbit(a), a < 0 });
}
