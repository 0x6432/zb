const std = @import("std");
const Index = enum(u32) { root = 0, _ };
const OptionalIndex = enum(u32) {
    root = 0,
    none = std.math.maxInt(u32),
    _,
    pub fn unwrap(oi: OptionalIndex) ?Index {
        return if (oi == .none) null else @enumFromInt(@intFromEnum(oi));
    }
};
fn load(comptime size: usize, buffer: *[size]Index, items: [size]OptionalIndex) []Index {
    for (buffer, items, 0..) |*node, opt_node, i| {
        node.* = opt_node.unwrap() orelse return buffer[0..i];
    }
    return buffer[0..];
}
const D = struct { a: OptionalIndex, b: OptionalIndex };
const U = union { x: u64, pair: struct { OptionalIndex, OptionalIndex } };
fn p2(buf: *[2]Index, u: U) ?[]const Index { return load(2, buf, u.pair); }
fn params(buf: *[2]Index, d: D) ?[]const Index {
    return load(2, buf, .{ d.a, d.b });
}
pub fn main() void {
    var buf: [2]Index = undefined;
    var d: D = .{ .a = @enumFromInt(5), .b = .none };
    _ = &d;
    const a = params(&buf, d).?;
    std.debug.print("{d} {d}\n", .{ a.len, @intFromEnum(a[0]) });
    d.b = @enumFromInt(7);
    const c = params(&buf, d).?;
    std.debug.print("{d}\n", .{c.len});
    d.a = .none;
    std.debug.print("{d}\n", .{params(&buf, d).?.len});
    var u: U = .{ .pair = .{ @enumFromInt(3), .none } }; _ = &u;
    std.debug.print("u {d}\n", .{p2(&buf, u).?.len});
    u = .{ .pair = .{ @enumFromInt(3), @enumFromInt(4) } };
    std.debug.print("u {d}\n", .{p2(&buf, u).?.len});
}
