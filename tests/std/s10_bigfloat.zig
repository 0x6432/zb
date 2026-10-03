const std = @import("std");
pub fn main() void {
    var a: f128 = 1.0; var b: f128 = 3.0;
    _ = .{ &a, &b };
    const c = a / b;
    const bits: u128 = @bitCast(c);
    std.debug.print("{x}\n", .{bits});
    var x: f80 = 2.0; _ = &x;
    const r = @sqrt(x);
    const rb: u80 = @bitCast(r);
    std.debug.print("{x} {d:.6} {}\n", .{ rb, @as(f64, @floatCast(r)), c < a });
    const i: u64 = @intFromFloat(c * 3e18);
    std.debug.print("{} {d}\n", .{ i, @as(f64, @floatCast(-@floor(c * 10.0))) });
    var w: i128 = -170141183460469231731687303715884105727; _ = &w;
    const wf: f128 = @floatFromInt(w);
    const back: i128 = @intFromFloat(wf / 2.0);
    std.debug.print("{}\n", .{back});
    var t: f128 = 0.1; _ = &t;
    std.debug.print("{d} {e} {d}\n", .{ t * 3.0, t / 7.0, @as(f80, 2.5) * @as(f80, @floatCast(t)) });
    std.debug.print("{} {}\n", .{ @mod(@as(f128, -7.5), t * 20.0), @rem(@as(f128, -7.5), t * 20.0) });
}


