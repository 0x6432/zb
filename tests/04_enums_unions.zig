const std = @import("std");
const w = std.io;
const Color = enum(u8) {
    red = 1,
    green,
    blue = 10,
    pub fn isWarm(self: Color) bool {
        return self == .red;
    }
};
const Shape = union(enum) {
    circle: u32,
    rect: struct { w: u32, h: u32 },
    none,
    fn area(s: Shape) u32 {
        return switch (s) {
            .circle => |r| 3 * r * r,
            .rect => |rc| rc.w * rc.h,
            .none => 0,
        };
    }
};
fn classify(n: i32) []const u8 {
    return switch (n) {
        0 => "zero",
        1...9 => "small",
        10, 20, 30 => "round",
        else => "big",
    };
}
pub fn main() void {
    const c: Color = .green;
    w.writeInt(1, @intFromEnum(c));
    w.writeAll(1, " ");
    w.writeAll(1, @tagName(c));
    w.writeAll(1, " ");
    w.writeInt(1, @intFromBool(Color.red.isWarm()));
    w.writeAll(1, "\n");
    const shapes = [_]Shape{ .{ .circle = 2 }, .{ .rect = .{ .w = 3, .h = 4 } }, .none };
    for (shapes) |s| {
        w.writeInt(1, s.area());
        w.writeAll(1, " ");
        w.writeAll(1, @tagName(s));
        w.writeAll(1, "\n");
    }
    for ([_]i32{ 0, 5, 20, 99 }) |n| {
        w.writeAll(1, classify(n));
        w.writeAll(1, "\n");
    }
    const e: Color = @enumFromInt(10);
    w.writeAll(1, @tagName(e));
    w.writeAll(1, "\n");
}
