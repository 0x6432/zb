const std = @import("std");
const Idx = enum(u32) { _ };
fn f(insts: []const Idx, items_len: usize, map_start: u32) usize {
    const start, const end = std.mem.minMax(u32, @ptrCast(insts));
    std.debug.print("start {d} end {d}\n", .{ start, end });
    const old_start = if (items_len == 0) start else map_start;
    var better_capacity = items_len;
    var better_start = old_start;
    while (true) {
        const extra_capacity = better_capacity / 2 + 16;
        better_capacity += extra_capacity;
        better_start -|= @intCast(extra_capacity / 2);
        std.debug.print("cap {d} bs {d}\n", .{ better_capacity, better_start });
        if (better_start <= start and end < better_capacity + better_start) break;
    }
    return better_capacity;
}
pub fn main() void {
    var a = [_]Idx{ @enumFromInt(10), @enumFromInt(5), @enumFromInt(20) };
    _ = &a;
    std.debug.print("{d}\n", .{f(&a, 0, 0)});
}
