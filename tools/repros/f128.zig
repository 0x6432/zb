const std = @import("std");
pub fn main() void {
    var a: f128 = 1.5; var h: f16 = 0.333; var e: f80 = 2.25;
    _ = &a; _ = &h; _ = &e;
    const b: u128 = @bitCast(a);
    const hb: u16 = @bitCast(h);
    const x = std.math.frexp(a);
    std.debug.print("{x} {x} {d} {d} {d}\n", .{ b, hb, @as(f64, @floatCast(a * 3)), @as(f64, @floatCast(e + 1)), x.exponent });
    var fl: f128 = @floatFromInt(@as(i64, 1000)); _ = &fl;
    std.debug.print("{d} {d}\n", .{ @as(i64, @intFromFloat(fl / 8)), @as(f32, h) });
}
