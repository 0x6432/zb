const std = @import("std");
const R = packed struct { mantissa: u112, exponent: u15, sign: u1 };
pub fn main() void {
    var m: u112 = 0x8000000000000000000000000000; var e: u15 = 0x403f; _ = &m; _ = &e;
    const r = R{ .mantissa = m, .exponent = e, .sign = 0 };
    const u: u128 = @bitCast(r);
    const f: f128 = @bitCast(r);
    std.debug.print("{x} {x} {d}\n", .{ u, r.exponent, @as(f64, @floatCast(f)) });
    const Repr = std.math.FloatRepr(f128);
    const n: Repr.Normalized = .{ .fraction = 0, .exponent = 64 };
    std.debug.print("{d}\n", .{@as(f64, @floatCast(n.reconstruct(.positive)))});
}
