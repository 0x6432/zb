const std = @import("std");
const F = enum { a, b, c };
fn cast(comptime R: type, zv: anytype) R {
    const elems = comptime blk: { var t: [zv.len]F = undefined; for (&t, zv) |*e, z| e.* = z; break :blk t; };
    return &elems;
}
pub fn main() void { const x = cast([]const F, .{ .a, .c }); std.debug.print("{any}\n", .{x}); }
