const std = @import("std");
const F = packed struct(u32) {
    a: bool = false, u: u13 = 0,
    un: packed union { mask: u1, g: bool } = .{ .mask = 0 },
    x: u1 = 0,
    un2: packed union { mask: u1, m: bool } = .{ .mask = 0 },
    rest: u13 = 0, w: bool = false, r: bool = false,
};
pub fn main() void {
    const f: F = .{ .a = true, .w = true, .r = true };
    var g = f; g.un.g = true; _ = &g;
    std.debug.print("{x} {x} {}\n", .{ @as(u32, @bitCast(f)), @as(u32, @bitCast(g)), @bitSizeOf(@TypeOf(f.un)) });
}
