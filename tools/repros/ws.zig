const std = @import("std");
pub fn main() void {
    var m: u113 = (@as(u113, 1) << 112) | (@as(u113, 1) << 111);
    var e: i32 = 0; _ = &m; _ = &e;
    const a = m >> @intCast(112 - e);
    var s: u7 = 112; _ = &s;
    const b = m >> s;
    var w: u128 = 1 << 127; _ = &w;
    std.debug.print("{x} {x} {x} {x}\n", .{ a, b, w >> s, m << 10 >> s });
}
