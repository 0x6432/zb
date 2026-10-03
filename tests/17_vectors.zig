const std = @import("std");
const print = std.io.print;

const V4 = @Vector(4, i32);

fn dot(a: V4, b: V4) i32 {
    return @reduce(.Add, a * b);
}

pub fn main() void {
    var a: V4 = .{ 1, 2, 3, 4 };
    const b: V4 = @splat(10);
    const c = a + b;
    print("{any}\n", .{c});
    a *= @splat(2);
    print("{d} {d}\n", .{ dot(a, b), @reduce(.Max, a) });
    const arr: [4]i32 = c;
    print("{d} {d}\n", .{ arr[0], arr[3] });
    const m = a > @as(V4, @splat(4));
    print("{any} {}\n", .{ m, @reduce(.Or, m) });
    const sel = @select(i32, m, a, b);
    print("{any}\n", .{sel});
    var w: @Vector(3, i64) = .{ -5, 7, 0 };
    w = -w * w;
    print("{any} {any}\n", .{ w, ~@as(@Vector(2, u8), .{ 1, 2 }) });
    print("{d} {d}\n", .{ c[1], a[2] });
    const sh = @shuffle(i32, a, b, [_]i32{ 0, -1, 3, -2 });
    print("{any}\n", .{sh});
    var u: @Vector(4, u8) = .{ 250, 1, 2, 3 };
    u +%= @splat(10);
    print("{any}\n", .{u});
    a[0] = 99;
    print("{d}\n", .{a[0]});
}
