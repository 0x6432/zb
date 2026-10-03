const std = @import("std");
const print = std.io.print;

const Color = enum { red, green, blue };
const Shape = union(enum) {
    circle: u32,
    rect: struct { w: u16, h: u16 },
    none,
};
const Point = struct { x: i32, y: i32 };
const E = error{ Oops, Bad };

fn mayFail(ok: bool) E!u8 {
    if (ok) return 7;
    return error.Bad;
}

pub fn main() void {
    const x: i32 = -42;
    const y: u8 = 200;
    print("ints: {} {d} {} {x} {X} {b} {o}\n", .{ x, y, 123, 255, 255, 5, 8 });
    print("strings: {s}|{s}|{c}\n", .{ "hello", @as([]const u8, "world"), 'Z' });
    print("bool: {} {}\n", .{ true, false });
    const opt: ?u32 = 5;
    const none: ?u32 = null;
    print("opt: {?} {?} {any}\n", .{ opt, none, opt });
    print("enum: {} {t} {d}\n", .{ Color.green, Color.blue, Color.blue });
    print("struct: {any}\n", .{Point{ .x = 1, .y = -2 }});
    print("tuple: {any}\n", .{.{ 1, true }});
    const s1: Shape = .{ .circle = 9 };
    const s2: Shape = .{ .rect = .{ .w = 3, .h = 4 } };
    print("union: {any} {any}\n", .{ s1, s2 });
    const arr = [_]u8{ 1, 2, 3 };
    print("array: {any} {any}\n", .{ arr, @as([]const u8, &arr) });
    print("err: {!} {!} {}\n", .{ mayFail(true), mayFail(false), error.Oops });
    print("width: [{d:5}] [{d:<5}] [{d:^5}] [{d:0>4}] [{s:>6}] [{d:03}]\n", .{ 42, 42, 42, 7, "ab", 5 });
    print("braces: {{}} {{{d}}}\n", .{1});
    var buf: [32]u8 = undefined;
    const r = std.fmt.bufPrint(&buf, "{s}-{d}", .{ "abc", 99 }) catch unreachable;
    print("bufPrint: {s} len={d}\n", .{ r, r.len });
    print("maxInt: {d} {d} {d}\n", .{ std.math.maxInt(u8), std.math.maxInt(i16), std.math.minInt(i8) });
    var total: u64 = 0;
    for (0..10) |i| total += i * i;
    print("runtime: {d}\n", .{total});
    std.debug.print("to stderr {d}\n", .{1});
}
