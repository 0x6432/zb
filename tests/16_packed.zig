const std = @import("std");
const print = std.io.print;

const Flags = packed struct(u8) {
    a: bool = false,
    b: bool = true,
    mode: u3 = 5,
    rest: u3 = 0,
};

const Hdr = packed struct {
    kind: u4,
    len: u12,
    tag: u16,
};

const Color = enum(u2) { red, green, blue };
const Outer = packed struct(u16) {
    lo: Flags,
    c: Color,
    n: i6,
};

fn setMode(f: *Flags, m: u3) void {
    f.mode = m;
}

pub fn main() void {
    var f: Flags = .{};
    print("{} {} {d} {d}\n", .{ f.a, f.b, f.mode, @as(u8, @bitCast(f)) });
    f.a = true;
    setMode(&f, 2);
    f.rest +%= 7;
    print("{} {d} {d} 0x{x}\n", .{ f.a, f.mode, f.rest, @as(u8, @bitCast(f)) });
    var h: Hdr = .{ .kind = 3, .len = 1000, .tag = 0xbeef };
    h.len += 24;
    const raw: u32 = @bitCast(h);
    print("0x{x} {d} {d}\n", .{ raw, @sizeOf(Hdr), @bitSizeOf(Hdr) });
    const h2: Hdr = @bitCast(@as(u32, 0x12345671));
    print("{d} {d} 0x{x}\n", .{ h2.kind, h2.len, h2.tag });
    const g: Flags = @bitCast(@as(u8, 0xff));
    print("{any}\n", .{g});
    print("{}\n", .{f == f});
    var o: Outer = .{ .lo = .{}, .c = .blue, .n = -3 };
    o.lo.mode = 1;
    o.n -= 10;
    print("{d} {s} {d} 0x{x}\n", .{ o.lo.mode, @tagName(o.c), o.n, @as(u16, @bitCast(o)) });
    o.c = .green;
    const inner = o.lo;
    print("{} {d} {s}\n", .{ inner.b, inner.mode, @tagName(o.c) });
}
