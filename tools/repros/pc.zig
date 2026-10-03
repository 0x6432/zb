const std = @import("std");
fn f(s: []u8) []u32 { return @ptrCast(@alignCast(s)); }
fn g(s: []const u32) []u8 { return @ptrCast(@constCast(s)); }
fn h(p: [*]u8, n: usize) ?[]u32 { return @ptrCast(@alignCast(p[0..n])); }
pub fn main() void {
    var buf: [16]u8 align(4) = undefined;
    var a: [3]u32 = .{ 1, 2, 3 };
    std.debug.print("{d} {d} {d}\n", .{ f(&buf).len, g(&a).len, h(&buf, 8).?.len });
}
