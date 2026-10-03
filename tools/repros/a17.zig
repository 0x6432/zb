const std = @import("std");
const I = struct {
    pub fn add(d: u8, form: union(enum) { imm: u8, reg: u16 }) u32 { return d + switch (form) { .imm => |x| x, .reg => |r| r }; }
};
pub fn main() void {
    const encode = @field(I, "add");
    var args: std.meta.ArgsTuple(@TypeOf(encode)) = undefined;
    args[0] = 1; args[1] = .{ .imm = 4 };
    std.debug.print("{}\n", .{@call(.auto, encode, args)});
    std.debug.print("{}\n", .{I.add(2, .{ .reg = 300 })});
}
