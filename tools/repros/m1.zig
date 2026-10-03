const std = @import("std");
const Header = extern struct { capacity: u32, len: u32 };
const Entry = extern struct { a: u64, b: u32 };
const Map = struct {
    entries: [*]Entry,
    const empty: Map = .{ .entries = @constCast(&(extern struct {
        header: Header,
        entries: [1]Entry,
    }{ .header = .{ .capacity = 1, .len = 0 }, .entries = .{.{ .a = 0, .b = 0 }} }).entries) };
    const entries_offset = @offsetOf(extern struct { header: Header, entries: [1]Entry }, "entries");
    fn header(m: Map) *Header {
        return @ptrCast(@alignCast(@as([*]u8, @ptrCast(m.entries)) - entries_offset));
    }
};
pub fn main() void {
    var m: Map = Map.empty;
    _ = &m;
    std.debug.print("{d} {d}\n", .{ m.header().capacity, Map.entries_offset });
}
