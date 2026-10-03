const std = @import("std");
const w = std.io;
const Node = struct {
    val: i32,
    next: ?*Node = null,
};
fn find(xs: []const i32, needle: i32) ?usize {
    for (xs, 0..) |x, i| if (x == needle) return i;
    return null;
}
pub fn main() void {
    var n3 = Node{ .val = 3 };
    var n2 = Node{ .val = 2, .next = &n3 };
    var n1 = Node{ .val = 1, .next = &n2 };
    var it: ?*Node = &n1;
    var total: i32 = 0;
    while (it) |n| : (it = n.next) total += n.val;
    w.writeInt(1, total);
    w.writeAll(1, "\n");
    const xs = [_]i32{ 4, 8, 15, 16, 23, 42 };
    w.writeInt(1, @intCast(find(&xs, 23) orelse 100));
    w.writeAll(1, " ");
    w.writeInt(1, @intCast(find(&xs, 7) orelse 100));
    w.writeAll(1, "\n");
    var maybe: ?u32 = null;
    if (maybe == null) w.writeAll(1, "null\n");
    maybe = 5;
    if (maybe) |m| {
        w.writeInt(1, m);
        w.writeAll(1, "\n");
    }
    w.writeInt(1, maybe.?);
    w.writeAll(1, "\n");
    if (std.mem.indexOfScalar(u8, "hello", 'l')) |i| {
        w.writeInt(1, @intCast(i));
        w.writeAll(1, "\n");
    }
}
