const std = @import("std");
const print = std.io.print;

fn mulAdd(a: i128, b: i128, c: i128) i128 {
    return a * b + c;
}

pub fn main() void {
    var x: u128 = 1;
    x <<= 100;
    x += 12345;
    print("{d}\n", .{x});
    var y: i128 = -5;
    _ = &y;
    const z = mulAdd(y, 1_000_000_000_000, 7);
    print("{d} {}\n", .{ z, z < 0 });
    const big: u128 = 0xffff_ffff_ffff_ffff_ffff;
    var q = big;
    _ = &q;
    print("{d} {d}\n", .{ q / 1000, q % 1000 });
    const n: u64 = @truncate(q >> 16);
    print("0x{x} {d}\n", .{ n, @as(i128, @intCast(n)) });
    var w: u100 = 1 << 99;
    w +%= w;
    print("{d} {}\n", .{ w, x > big });
    const ns: i128 = @as(i128, 1700000000) * 1_000_000_000 + 5;
    var v = ns;
    _ = &v;
    const sec: i64 = @intCast(@divTrunc(v, 1_000_000_000));
    print("{d} {d}\n", .{ sec, ~@as(i128, @intCast(sec)) });
}
