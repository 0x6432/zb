const std = @import("std");
inline fn f(refs: anytype) [refs.len]u32 { var r: [refs.len]u32 = undefined; inline for (&r, 0..) |*x, i| x.* = refs[i] * 2; return r; }
pub fn main() void { var a: u32 = 3; _ = &a; std.debug.print("{any}\n", .{f(.{ a, a + 1 })}); }
