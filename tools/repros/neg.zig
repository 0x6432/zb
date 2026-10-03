const std = @import("std");
pub fn main() void {
    var a: f128 = -2.5e-62; var b: f64 = -1.0; var c: u128 = 0xbf2859c4ec64ddaeb000000000000000; _ = &a; _ = &b; _ = &c;
    const rs = ~@as(u128, 0) >> 1;
    const inf: u128 = @bitCast(std.math.inf(f128));
    std.debug.print("{} {} {x} {x} {}\n", .{ std.math.isFinite(a), std.math.isFinite(b), c & rs, inf, (c & rs) < inf });
}
