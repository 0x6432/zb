const std = @import("std");
const S = union(enum) { float: u32, cf, int: struct { a: bool, mn: u64, mx: u64 }, none };
pub fn main() void {
    var cur: S = .{ .int = .{ .a = true, .mn = 1, .mx = 1 } };
    var want: S = .{ .int = .{ .a = false, .mn = 8, .mx = 8 } };
    _ = &want;
    if (@intFromEnum(want) < @intFromEnum(cur)) {
        cur = want;
    } else if (@intFromEnum(want) == @intFromEnum(cur)) {
        switch (cur) {
            .none, .cf => {},
            .float => |f| { _ = f; },
            .int => |*ci| {
                const wi = want.int;
                if (!wi.a) ci.a = false;
                ci.mn = @max(ci.mn, wi.mn);
                ci.mx = @max(ci.mx, wi.mx);
            },
        }
    }
    std.debug.print("ie {d} {d}\n", .{ @intFromEnum(want), @intFromEnum(cur) });
    std.debug.print("{} {d} {d}\n", .{ cur.int.a, cur.int.mn, cur.int.mx });
}
