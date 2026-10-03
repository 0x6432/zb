const std = @import("std");
pub fn main() !void {
    var buf: [4096]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&buf);
    const gpa = fba.allocator();
    var map: std.AutoHashMapUnmanaged(u32, u32) = .empty;
    try map.put(gpa, 1, 10);
    var it = map.iterator();
    while (it.next()) |e| std.debug.print("k={d} v={d}\n", .{ e.key_ptr.*, e.value_ptr.* });
    std.debug.print("cap={d} contains={}\n", .{ map.capacity(), map.contains(1) });
    const H = std.hash_map.AutoContext(u32);
    const c: H = .{};
    std.debug.print("h={x} {x}\n", .{ c.hash(1), c.hash(1) });
    const gr = try map.getOrPut(gpa, 1);
    std.debug.print("found={} cnt={d}\n", .{ gr.found_existing, map.count() });
}
