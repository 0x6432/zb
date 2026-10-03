const std = @import("std");
fn toF(v: f64) f128 { return @floatCast(v); }
fn render(bits: u16, v: f64) void {
    const f128_val = toF(v);
    if (std.math.isFinite(f128_val)) {
        switch (bits) {
            64 => std.debug.print("fin {x}\n", .{@as(f64, @floatCast(f128_val))}),
            128 => std.debug.print("fin128 {x}\n", .{f128_val}),
            else => unreachable,
        }
    } else {
        const operation = if (std.math.isNan(f128_val)) "nan" else if (std.math.isSignalNan(f128_val)) "nans" else if (std.math.isInf(f128_val)) "inf" else unreachable;
        std.debug.print("{s}\n", .{operation});
    }
}
pub fn main() void {
    render(64, 1.5); render(128, 0.785); render(64, std.math.inf(f64)); render(64, std.math.nan(f64));
}
