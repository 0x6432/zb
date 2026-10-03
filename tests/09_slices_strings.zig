const std = @import("std");
const w = std.io;
const greeting = "hello world";
var counter: u32 = 10;
const table = [_]u16{ 1, 1, 2, 3, 5, 8 };
fn reverse(s: []u8) void {
    var i: usize = 0;
    var j = s.len - 1;
    while (i < j) : ({
        i += 1;
        j -= 1;
    }) {
        const t = s[i];
        s[i] = s[j];
        s[j] = t;
    }
}
fn apply(f: *const fn (u32) u32, x: u32) u32 {
    return f(x);
}
fn sq(x: u32) u32 {
    return x * x;
}
pub fn main() void {
    var buf: [11]u8 = undefined;
    @memcpy(&buf, greeting);
    reverse(&buf);
    w.writeAll(1, &buf);
    w.writeAll(1, "\n");
    w.writeAll(1, greeting[6..]);
    w.writeAll(1, " ");
    w.writeInt(1, greeting.len);
    w.writeAll(1, "\n");
    counter += 5;
    w.writeInt(1, counter);
    w.writeAll(1, " ");
    var s: u32 = 0;
    for (table) |t| s += t;
    w.writeInt(1, s);
    w.writeAll(1, "\n");
    w.writeInt(1, apply(&sq, 9));
    w.writeAll(1, "\n");
    const words = [_][]const u8{ "alpha", "beta", "gamma" };
    for (words, 0..) |word, i| {
        w.writeInt(1, @intCast(i));
        w.writeAll(1, "=");
        w.writeAll(1, word);
        w.writeAll(1, " ");
    }
    w.writeAll(1, "\n");
    if (std.mem.eql(u8, words[1], "beta")) w.writeAll(1, "eql\n");
    var arr = [_]i32{ 5, 6, 7 };
    for (&arr) |*x| x.* *= 10;
    w.writeInt(1, arr[0] + arr[1] + arr[2]);
    w.writeAll(1, "\n");
    var z: [4]u8 = undefined;
    @memset(&z, 'z');
    w.writeAll(1, z[0..2]);
    w.writeAll(1, "\n");
    const multi =
        \\line one
        \\line two
    ;
    w.writeAll(1, multi);
    w.writeAll(1, "\n");
    const a, const b = .{ @as(u32, 1), @as(u32, 2) };
    w.writeInt(1, a + b);
    w.writeAll(1, "\n");
}
