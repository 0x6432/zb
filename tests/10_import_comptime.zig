const std = @import("std");
const builtin = @import("builtin");
const util = @import("util/geom.zig");
const w = std.io;
const N = 4 * 4;
const Kind = if (builtin.os.tag == .linux) u32 else u64;
fn pow(comptime base: u64, exp: u64) u64 {
    var r: u64 = 1;
    for (0..exp) |_| r *= base;
    return r;
}
pub fn main() u8 {
    var grid: [N]u8 = undefined;
    for (&grid, 0..) |*g, i| g.* = @intCast(i);
    w.writeInt(1, grid[N - 1]);
    w.writeAll(1, " ");
    w.writeInt(1, @sizeOf(Kind));
    w.writeAll(1, "\n");
    w.writeInt(1, util.Point.origin().dist2(.{ .x = 3, .y = 4 }));
    w.writeAll(1, "\n");
    w.writeInt(1, @intCast(pow(3, 4)));
    w.writeAll(1, "\n");
    switch (builtin.cpu.arch) {
        .x86_64 => w.writeAll(1, "x86_64\n"),
        else => @compileError("unsupported"),
    }
    return 3;
}
