const std = @import("std");
fn add(a: i32, b: i32) callconv(.c) i32 { return a + b; }
var counter: u32 = 42;
comptime { @export(&add, .{ .name = "my_add" }); @export(&counter, .{ .name = "my_counter" }); }
extern fn my_add(a: i32, b: i32) i32;
extern var my_counter: u32;
fn sum(n: c_int, ...) callconv(.c) c_long {
    var ap = @cVaStart(); defer @cVaEnd(&ap);
    var ap2 = @cVaCopy(&ap); defer @cVaEnd(&ap2);
    var t: c_long = 0; var i: c_int = 0;
    while (i < n) : (i += 1) t += @cVaArg(&ap, c_long);
    const first = @cVaArg(&ap2, c_long);
    return t * 100 + first;
}
fn fsum(n: c_int, ...) callconv(.c) f64 {
    var ap = @cVaStart(); defer @cVaEnd(&ap);
    var t: f64 = 0; var i: c_int = 0;
    while (i < n) : (i += 1) t += @cVaArg(&ap, f64);
    return t;
}
const E1 = error{ A, B };
fn g(x: u8) !u8 { if (x == 0) return error.Zero; if (x == 1) return E1.A; return x; }
fn h(x: u8) !u8 { const y = try g(x); if (y > 100) return error.Big; return y; }
pub fn main() void {
    var arr = [_]u8{ 1, 2, 3 };
    @prefetch(&arr, .{});
    @prefetch(&arr[1], .{ .rw = .write, .locality = 1, .cache = .data });
    std.debug.print("{} {}\n", .{ my_add(3, 4), my_counter });
    std.debug.print("{} {d}\n", .{ sum(3, @as(c_long, 1), @as(c_long, 2), @as(c_long, 3)), fsum(2, @as(f64, 1.5), @as(f64, 2.25)) });
    const ES = @typeInfo(@typeInfo(@TypeOf(h)).@"fn".return_type.?).error_union.error_set;
    inline for (@typeInfo(ES).error_set.error_names.?) |e| std.debug.print("{s} ", .{e});
    std.debug.print("\n", .{});
    var x: u8 = 0; _ = &x;
    if (h(x)) |_| {} else |err| switch (err) {
        error.Zero => std.debug.print("zero\n", .{}),
        error.A, error.B => std.debug.print("ab\n", .{}),
        error.Big => std.debug.print("big\n", .{}),
    }
}
