const std = @import("std");

const Vec2 = struct {
    x: f64,
    y: f64,
    fn len(self: Vec2) f64 {
        return @sqrt(self.x * self.x + self.y * self.y);
    }
    fn scale(self: Vec2, k: f64) Vec2 {
        return .{ .x = self.x * k, .y = self.y * k };
    }
};

fn mean(xs: []const f32) f32 {
    var s: f32 = 0;
    for (xs) |x| s += x;
    return s / @as(f32, @floatFromInt(xs.len));
}

const third = 1.0 / 3.0; // comptime_float
const table = blk: {
    var t: [5]f64 = undefined;
    for (&t, 0..) |*e, i| e.* = @as(f64, @floatFromInt(i)) * 0.5;
    break :blk t;
};

pub fn main() void {
    const v = Vec2{ .x = 3, .y = 4 };
    std.debug.print("len={d} scaled={any}\n", .{ v.len(), v.scale(0.5) });
    std.debug.print("mean={d}\n", .{mean(&[_]f32{ 1.5, 2.5, 3.25 })});
    var a: f64 = 10;
    a /= 4;
    a -= 0.25;
    a *= -2;
    std.debug.print("a={d} neg={d} abs={d}\n", .{ a, -a, @abs(a) });
    const i: i32 = @intFromFloat(a);
    const u: u8 = @intFromFloat(@floor(7.9));
    std.debug.print("i={d} u={d} back={d}\n", .{ i, u, @as(f64, @floatFromInt(i)) / 8 });
    std.debug.print("cmp {} {} {} {}\n", .{ a < 0, a == -4.5, a >= -4.5, @max(a, 1.0) == 1.0 });
    std.debug.print("third={d} f32={d} table={any}\n", .{ @as(f64, third), @as(f32, third), table });
    std.debug.print("sci={e} prec={d:.3} width=[{d:>8}]\n", .{ 1234.5, 3.14159, 2.5 });
    const bits: u64 = @bitCast(@as(f64, -2.0));
    const fb: f32 = @bitCast(@as(u32, 0x40490fdb));
    std.debug.print("bits={x} fb={d}\n", .{ bits, fb });
    std.debug.print("floor={d} ceil={d} round={d} trunc={d}\n", .{ @floor(-1.5), @ceil(-1.5), @round(2.5), @trunc(-2.7) });
    var z: f64 = 0;
    _ = &z;
    std.debug.print("inf={d} ninf={d} nan={}\n", .{ 1 / z, -1 / z, (z / z) != (z / z) });
    const wide: f64 = @as(f32, 0.1);
    const narrow: f32 = @floatCast(@as(f64, 1.0e10));
    std.debug.print("wide={d} narrow={d} rem={d}\n", .{ wide, narrow, @rem(7.5, 2.0) });
}
