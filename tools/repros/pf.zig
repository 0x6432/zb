const std = @import("std");
const Flags = packed struct(u5) { ptr_cast: bool = false, align_cast: bool = false, addrspace_cast: bool = false, const_cast: bool = false, volatile_cast: bool = false };
const Tag = enum { ptr_cast, align_cast, addrspace_cast, const_cast, volatile_cast, other };
fn run(tags: []const Tag) u5 {
    var flags: Flags = .{};
    for (tags) |t| {
        switch (t) {
            else => break,
            inline .ptr_cast, .align_cast, .addrspace_cast, .const_cast, .volatile_cast => |tag| {
                if (@field(flags, @tagName(tag))) return 31;
                @field(flags, @tagName(tag)) = true;
            },
        }
    }
    return @bitCast(flags);
}
pub fn main() void {
    std.debug.print("{d} {d}\n", .{ run(&.{ .ptr_cast, .align_cast }), run(&.{.const_cast}) });
}
