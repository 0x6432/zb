const std = @import("std");
fn f(comptime n: usize, i: u32) bool {
    if (i >= n) return true;
    switch (i) { inline 0...n - 1 => |k| return k == 1, else => unreachable }
}
pub fn main() void { std.debug.print("{} {} {}\n", .{ f(0, 5), f(3, 1), f(3, 2) }); }
