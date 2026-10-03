const std = @import("std");
const Spec = union(enum) { imm: struct { bits: u16 }, reg,
    fn Storage(comptime spec: Spec) type { return switch (spec) { .imm => |i| @Int(.unsigned, i.bits), .reg => u8 }; }
    fn parse(comptime spec: Spec, tok: []const u8) ?Storage(spec) { return @intCast(tok.len); } };
fn mk(comptime T: type, x: anytype, y: anytype) T { _ = y; return x; }
pub fn main() void {
    var t: []const u8 = "abc"; _ = &t;
    const v = mk(Spec, Spec{ .imm = .{ .bits = 12 } }, .{}).parse(t);
    std.debug.print("{?} {s}\n", .{ v, @typeName(@TypeOf(v)) });
}
