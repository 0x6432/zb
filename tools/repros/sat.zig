const std = @import("std");
fn t(comptime T: type, x: T, y: T) void {
    var a = x; var b = y; _ = &a; _ = &b;
    std.debug.print("{d} {d} {d} {d}\n", .{ a +| b, a -| b, a *| b, a <<| 3 });
}
pub fn main() void {
    t(u8, 200, 100); t(u8, 5, 8); t(i8, -100, 100); t(i8, 100, -100); t(u32, 4000000000, 400000000);
    t(u64, 1 << 63, 1 << 63); t(u64, 3, 5); t(i64, std.math.minInt(i64), 1); t(i64, std.math.maxInt(i64), -1); t(u48, 1 << 47, 3); t(i16, -300, 200);
    var bs: u32 = 5; _ = &bs; bs -|= @intCast(@as(usize, 8)); std.debug.print("{d}\n", .{bs});
}
