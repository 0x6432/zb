const std = @import("std");
const Point = struct { x: i32, y: i32 };
const Color = enum { red, green, blue };
pub fn main() !void {
    var buf: [256]u8 = undefined;
    const s = try std.fmt.bufPrint(&buf, "{d:>5}|{x:0>4}|{s}|{c}", .{ 42, 255, "hi", 'z' });
    std.debug.print("{s}\n", .{s});
    var it = std.mem.splitScalar(u8, "a,bb,ccc", ',');
    while (it.next()) |part| std.debug.print("[{s}]", .{part});
    std.debug.print("\n", .{});
    var tk = std.mem.tokenizeAny(u8, "  12 34  56 ", " ");
    var sum: i64 = 0;
    while (tk.next()) |t| sum += try std.fmt.parseInt(i64, t, 10);
    std.debug.print("sum={d}\n", .{sum});
    std.debug.print("eql={} idx={?d}\n", .{ std.mem.eql(u8, "abc", "abc"), std.mem.indexOf(u8, "hello world", "wor") });
    const p = Point{ .x = 3, .y = -4 };
    std.debug.print("{any} {s} {}\n", .{ p, @tagName(Color.green), Color.blue });
    std.debug.print("max={d} min={d}\n", .{ std.math.maxInt(u16), std.mem.min(i32, &[_]i32{ 5, -2, 9 }) });
    var mem: [1024]u8 = undefined;
    var fba = std.heap.FixedBufferAllocator.init(&mem);
    const a = fba.allocator();
    var sm = std.StringHashMapUnmanaged(i32).empty;
    try sm.put(a, "apple", 1);
    try sm.put(a, "pear", 2);
    std.debug.print("pear={?d} kiwi={?d}\n", .{ sm.get("pear"), sm.get("kiwi") });
    const r = std.fmt.parseInt(u8, "300", 10);
    std.debug.print("err={any}\n", .{r});
}
