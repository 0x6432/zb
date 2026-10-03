const std = @import("std");
const C = enum { a, b, ld };
fn bits(c: C, k: u8) ?u16 { if (k == 0) return null; return switch (c) { .a => 16, .b => 32, .ld => 80 }; }
fn al(c: C) ?u16 { _ = c; return 16; }
fn bytes(c: C, k: u8) ?u16 {
    return switch (c) {
        .a, .b => @divExact(bits(c, k) orelse return null, 8),
        .ld => switch (bits(c, k) orelse return null) {
            64 => 8,
            80 => @intCast(std.mem.alignForward(usize, 10, al(c).?)),
            128 => 16,
            else => unreachable,
        },
    };
}
pub fn main() void {
    var k: u8 = 1; _ = &k;
    std.debug.print("{?} {?} {?} {?}\n", .{ bytes(.a, k), bytes(.b, k), bytes(.ld, k), bytes(.ld, 0) });
}
