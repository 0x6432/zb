const std = @import("std");
pub fn main() !void {
    var buf: [4096]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buf);
    const gpa = fba.allocator();
    var list: std.ArrayList(u32) = .empty;
    defer list.deinit(gpa);
    for (0..10) |i| try list.append(gpa, @intCast((i * 7) % 10));
    std.mem.sort(u32, list.items, {}, std.sort.asc(u32));
    std.debug.print("{any}\n", .{list.items});
    var map: std.AutoHashMapUnmanaged(u32, []const u8) = .empty;
    try map.put(gpa, 1, "one");
    try map.put(gpa, 2, "two");
    std.debug.print("{s} {?s} {d}\n", .{ map.get(1).?, map.get(3), map.count() });
    const s = try std.fmt.allocPrint(gpa, "{d}+{d}={d}", .{ 2, 3, 5 });
    std.debug.print("{s}\n", .{s});
}
