const std = @import("std");
const out = std.io;

fn fib(n: u64) u64 {
    if (n < 2) return n;
    return fib(n - 1) + fib(n - 2);
}
fn squares(comptime n: usize) [n]u32 {
    var a: [n]u32 = undefined;
    for (&a, 0..) |*x, i| x.* = @intCast(i * i);
    return a;
}
const table = squares(8);
const fib20 = comptime fib(20);

const Point = struct {
    x: i32,
    y: i32 = 7,
    fn sum(self: Point) i32 {
        return self.x + self.y;
    }
};
const origin: Point = .{ .x = 3 };

fn Pair(comptime A: type, comptime B: type) type {
    return struct {
        a: A,
        b: B,
        const Self = @This();
        fn swap(self: Self) Pair(B, A) {
            return .{ .a = self.b, .b = self.a };
        }
    };
}

fn countVowels(comptime s: []const u8) usize {
    var n: usize = 0;
    for (s) |c| switch (c) {
        'a', 'e', 'i', 'o', 'u' => n += 1,
        else => {},
    };
    return n;
}
fn concatAll(comptime parts: []const []const u8) []const u8 {
    comptime var r: []const u8 = "";
    inline for (parts) |p| r = r ++ p;
    return r;
}
const greeting = concatAll(&.{ "hel", "lo", " ", "world" });

const Color = enum { red, green, blue };
fn colorName(comptime c: Color) []const u8 {
    return switch (c) {
        .red => "R",
        .green => "G",
        .blue => "B",
    };
}
var counter: u32 = blk: {
    var x: u32 = 0;
    var i: u32 = 0;
    while (i < 10) : (i += 1) x += i;
    break :blk x;
};
const words = [_][]const u8{ "alpha", "beta", "gamma" };
const total_len = blk: {
    var n: usize = 0;
    for (words) |w| n += w.len;
    break :blk n;
};

pub fn main() void {
    out.writeInt(1, @intCast(fib20));
    out.writeAll(1, "\n");
    for (table) |v| {
        out.writeInt(1, v);
        out.writeAll(1, " ");
    }
    out.writeAll(1, "\n");
    out.writeInt(1, origin.sum());
    out.writeAll(1, "\n");
    const P = Pair(u8, i64);
    const p: P = .{ .a = 5, .b = -9 };
    const q = p.swap();
    out.writeInt(1, q.a);
    out.writeAll(1, " ");
    out.writeInt(1, q.b);
    out.writeAll(1, "\n");
    out.writeInt(1, @intFromBool(Pair(u8, i64) == P));
    out.writeAll(1, "\n");
    out.writeInt(1, comptime countVowels("comptime evaluation"));
    out.writeAll(1, "\n");
    out.writeAll(1, greeting);
    out.writeAll(1, "\n");
    out.writeAll(1, colorName(.green));
    out.writeAll(1, "\n");
    counter += 1;
    out.writeInt(1, counter);
    out.writeAll(1, "\n");
    out.writeInt(1, total_len);
    out.writeAll(1, "\n");
    comptime var k = 1;
    inline while (k < 100) : (k *= 3) {
        out.writeInt(1, k);
        out.writeAll(1, ",");
    }
    out.writeAll(1, "\n");
    const arr = comptime blk: {
        var a = [_]u8{ 5, 3, 9, 1, 7 };
        // bubble sort at comptime
        var i: usize = 0;
        while (i < a.len) : (i += 1) {
            var j: usize = 0;
            while (j + 1 < a.len - i) : (j += 1) {
                if (a[j] > a[j + 1]) {
                    const t = a[j];
                    a[j] = a[j + 1];
                    a[j + 1] = t;
                }
            }
        }
        break :blk a;
    };
    for (arr) |v| out.writeInt(1, v);
    out.writeAll(1, "\n");
}
