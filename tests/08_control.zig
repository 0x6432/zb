const std = @import("std");
const w = std.io;
fn order() void {
    defer w.writeAll(1, "3 ");
    {
        defer w.writeAll(1, "1 ");
    }
    defer w.writeAll(1, "2 ");
}
const Op = enum { inc, dbl, stop };
fn run(prog: []const Op) u32 {
    var acc: u32 = 1;
    var pc: usize = 0;
    sw: switch (prog[pc]) {
        .inc => {
            acc += 1;
            pc += 1;
            continue :sw prog[pc];
        },
        .dbl => {
            acc *= 2;
            pc += 1;
            continue :sw prog[pc];
        },
        .stop => {},
    }
    return acc;
}
pub fn main() void {
    order();
    w.writeAll(1, "\n");
    var found: ?usize = null;
    outer: for (0..5) |i| {
        for (0..5) |j| {
            if (i * j == 6) {
                found = i * 10 + j;
                break :outer;
            }
        }
    }
    w.writeInt(1, @intCast(found.?));
    w.writeAll(1, "\n");
    const v = blk: {
        var k: u32 = 0;
        while (true) : (k += 1) {
            if (k * k > 50) break :blk k;
        }
    };
    w.writeInt(1, v);
    w.writeAll(1, "\n");
    var odd: u32 = 0;
    var i: u32 = 0;
    while (i < 10) : (i += 1) {
        if (i % 2 == 0) continue;
        odd += i;
    }
    w.writeInt(1, odd);
    w.writeAll(1, "\n");
    w.writeInt(1, run(&.{ .inc, .dbl, .dbl, .inc, .stop }));
    w.writeAll(1, "\n");
    const r = for ([_]u8{ 1, 3, 5 }) |x| {
        if (x % 2 == 0) break x;
    } else 255;
    w.writeInt(1, r);
    w.writeAll(1, "\n");
}
