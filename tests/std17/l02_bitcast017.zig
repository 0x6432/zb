const std = @import("std");
const P = packed struct(u6) { a: u2, b: u4 };
const E = enum(u3) { a, b, c, d, e };
pub fn main() void {
    var x: u15 = 0x5abc; _ = &x;
    const a: [3]u5 = @bitCast(x);
    var b: [2]u24 = .{ 0x123456, 0xabcdef }; _ = &b;
    const c: u48 = @bitCast(b);
    var d: [4]bool = .{ true, false, true, true }; _ = &d;
    const di: u4 = @bitCast(d);
    var v: @Vector(3, u5) = .{ 1, 2, 3 }; _ = &v;
    const vi: u15 = @bitCast(v);
    var pp: [2]P = .{ .{ .a = 1, .b = 9 }, .{ .a = 3, .b = 2 } }; _ = &pp;
    const pi: u12 = @bitCast(pp);
    var ee: [2]E = .{ .c, .e }; _ = &ee;
    const ei: u6 = @bitCast(ee);
    var aa: [2][2]u3 = .{ .{ 1, 2 }, .{ 3, 4 } }; _ = &aa;
    const ai: u12 = @bitCast(aa);
    const back: [2]u24 = @bitCast(c);
    const f: [2]u16 = @bitCast(@as(f32, 1.5));
    std.debug.print("{any} {x} {b} {x} {x} {x} {x} {any} {any}\n", .{ a, c, di, vi, pi, ei, ai, back, f });
    const ca: [3]u5 = comptime @bitCast(@as(u15, 0x5abc));
    const cc: u48 = comptime @bitCast([2]u24{ 0x123456, 0xabcdef });
    const cd: u4 = comptime @bitCast([4]bool{ true, false, true, true });
    std.debug.print("{any} {x} {b}\n", .{ ca, cc, cd });
}
