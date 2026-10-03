const std = @import("std");
const print = std.io.print;

const Node = struct {
    val: u32,
    link: Link = .{},
};
const Link = struct { next: ?*Link = null };

fn parse(s: []const u8) !u32 {
    if (s.len == 0) return error.Empty;
    return @intCast(s.len);
}

pub fn main() void {
    var x: u8 = 250;
    const r = @addWithOverflow(x, 10);
    print("{d} {d}\n", .{ r[0], r[1] });
    const m = @mulWithOverflow(@as(i32, 1 << 20), 4096);
    print("{d} {d}\n", .{ m[0], m[1] });
    const sb, const ob = @subWithOverflow(x, 251);
    print("{d} {d}\n", .{ sb, ob });
    const sh = @shlWithOverflow(x, 1);
    print("{d} {d}\n", .{ sh[0], sh[1] });
    x = 0x12;
    var w: u32 = 0x11223344;
    print("0x{x} {d} {d} {d}\n", .{ @byteSwap(w), @clz(w), @ctz(w), @popCount(w) });
    w = @bitReverse(w);
    print("0x{x}\n", .{w});
    var n: Node = .{ .val = 7 };
    const lp = &n.link;
    const np: *Node = @fieldParentPtr("link", lp);
    print("{d}\n", .{np.val});
    var buf = [_]u8{ 1, 2, 3, 4, 5, 6 };
    @memmove(buf[1..5], buf[0..4]);
    print("{any}\n", .{buf});
    var cnt: u32 = 5;
    _ = @atomicRmw(u32, &cnt, .Add, 3, .seq_cst);
    @atomicStore(u32, &cnt, @atomicLoad(u32, &cnt, .acquire) * 2, .release);
    print("{d}\n", .{cnt});
    const arr: *[3]u8 = buf[2..5];
    print("{d} {d}\n", .{ arr.len, arr[0] });
    var i: usize = 0;
    var sum: usize = 0;
    while (i < 10) : (i += 1) {
        if (i % 2 == 0) continue;
        sum += i;
    }
    print("{d}\n", .{sum});
    if (parse("")) |v| {
        print("ok {d}\n", .{v});
    } else |_| {
        print("failed\n", .{});
    }
    if (parse("abc")) |v| print("ok {d}\n", .{v}) else |e| print("{s}\n", .{@errorName(e)});
    const t = .{ @as(u8, 1), true, "hi" };
    print("{d} {} {s}\n", .{ t[0], t[1], t[2] });
    const cond = buf[0] == 1;
    const pv = if (cond) @as(u8, 200) else @as(u16, 1000);
    print("{d} {s}\n", .{ pv, @typeName(@TypeOf(pv)) });
    const mx = @max(x, 3, @as(u8, 100));
    print("{d} {d}\n", .{ mx, @min(w, 5) });
}
