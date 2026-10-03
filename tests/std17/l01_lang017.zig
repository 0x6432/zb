const std = @import("std");
const Foo = struct { bar: i32, const baz = 1; pub var quux = "xxx"; };
const P = packed struct(u8) { a: u4, b: u4 };
const U = union(enum(u8)) { x: u32 = 5, y: void = 9 };
const E = enum(u16) { a = 3, b = 7 };
pub fn main() void {
    std.debug.print("{} {} {}\n", .{ @hasDecl(Foo, "bar"), @hasDecl(Foo, "baz"), @hasDecl(Foo, "quux") });
    const slice: []const u16 = &.{ 1, 2, 3 };
    const array: [3]u16 = slice.*;
    const array_ptr: *const [3]u16 = slice;
    std.debug.print("{any} {}\n", .{ array, array_ptr[2] });
    var p: P = @fromBackingInt(@as(u8, 0x5a)); _ = &p;
    var u: U = .{ .y = {} }; _ = &u;
    var e: E = .b; _ = &e;
    std.debug.print("{x} {} {} {} {}\n", .{ @backingInt(p), p.a, @backingInt(u), @backingInt(e), @as(E, @fromBackingInt(3)) });
    var n: i32 = -7; _ = &n;
    std.debug.print("{} {} {}\n", .{ @divCeil(n, 2), @divCeil(@as(u32, 7), 2), @divCeil(@as(f64, 7.5), 2.0) });
    const arr: [2]u8 = .{ 0x12, 0x34 };
    std.debug.print("{x} {any}\n", .{ @as(u16, @bitCast(arr)), @as([2]u4, @bitCast(@as(u8, 0xab))) });
}
