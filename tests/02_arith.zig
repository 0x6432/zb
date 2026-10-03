const std = @import("std");
const out = std.io;
fn fib(n: u32) u64 {
    if (n < 2) return n;
    return fib(n - 1) + fib(n - 2);
}
fn gcd(a: u64, b: u64) u64 {
    var x = a;
    var y = b;
    while (y != 0) {
        const t = y;
        y = x % y;
        x = t;
    }
    return x;
}
pub fn main() void {
    out.writeInt(1, @intCast(fib(20)));
    out.writeAll(1, "\n");
    out.writeInt(1, @intCast(gcd(1071, 462)));
    out.writeAll(1, "\n");
    var a: u8 = 250;
    a +%= 10;
    out.writeInt(1, a);
    out.writeAll(1, "\n");
    const b: i32 = -7;
    out.writeInt(1, @divFloor(b, 2));
    out.writeAll(1, " ");
    out.writeInt(1, @mod(b, 3));
    out.writeAll(1, " ");
    out.writeInt(1, @divTrunc(b, 2));
    out.writeAll(1, "\n");
    var sh: u32 = 1;
    sh <<= 31;
    out.writeInt(1, sh >> 30);
    out.writeAll(1, "\n");
    const x: u16 = 0xFF00;
    const y: u8 = @truncate(x >> 4);
    out.writeInt(1, y);
    out.writeAll(1, "\n");
    out.writeInt(1, @max(3, @min(10, 7)));
    out.writeAll(1, "\n");
    var sum: i64 = 0;
    for (0..10) |i| sum += @intCast(i * i);
    out.writeInt(1, sum);
    out.writeAll(1, "\n");
}
