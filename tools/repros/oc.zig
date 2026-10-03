const std = @import("std");
const S = struct { tag: u8, param_count: ?u8 };
pub fn main() void {
    var a: S = .{ .tag = 1, .param_count = 1 };
    var b: ?S = .{ .tag = 1, .param_count = 2 };
    _ = &a; _ = &b;
    std.debug.print("{} {} {} {}\n", .{ a.param_count != 1, a.param_count == 1, b.?.param_count != 1, b.?.param_count != null });
    const info = b orelse return;
    std.debug.print("{}\n", .{info.param_count != 2});
}
