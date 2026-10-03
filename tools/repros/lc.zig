const std = @import("std");
pub fn main() void {
    var x: usize = 64; var y: u8 = 3; var z: i8 = -3; _ = &x; _ = &y; _ = &z;
    std.debug.print("{d} {} {} {} {} {} {}\n", .{ std.math.lossyCast(i12, x), x <= -2048, -1 < y, y < 300, 300 > y, z > -200, z == 1000 });
}
