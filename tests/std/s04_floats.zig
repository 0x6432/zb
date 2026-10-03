const std = @import("std");
pub fn main() !void {
    std.debug.print("{d} {e} {d}\n", .{ 1.5, 2.0e10, 1.0 / 3.0 });
    var x: f64 = 2.0;
    _ = &x;
    std.debug.print("{d} {d} {d}\n", .{ std.math.sqrt(x), std.math.pow(f64, x, 10), std.math.pi });
    std.debug.print("{d:.2} {d} {d}\n", .{ std.math.sin(x), std.math.floor(x * 1.7), std.math.inf(f64) });
    const v = try std.fmt.parseFloat(f64, "3.14159");
    std.debug.print("{d} {}\n", .{ v, std.math.isNan(v) });
    const f: f32 = 1.0 / 3.0;
    std.debug.print("{d} {d}\n", .{ f, @as(f64, f) });
    std.debug.print("{d} {d}\n", .{ std.math.exp(x), std.math.log(f64, 10, 1000) });
}
