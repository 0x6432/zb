const std = @import("std");
pub fn main() void {
    const gpa = std.heap.c_allocator;
    var l: std.ArrayList(u32) = .empty;
    var i: u32 = 0;
    while (i < 100000) : (i += 1) l.append(gpa, i) catch unreachable;
    var s: u64 = 0;
    for (l.items) |x| s += x;
    std.debug.print("{d} {d}\n", .{ l.items.len, s });
    var m: std.ArrayList(?u32) = .empty;
    i = 0;
    while (i < 1000) : (i += 1) m.append(gpa, i) catch unreachable;
    std.debug.print("{d}\n", .{m.items.len});
}
