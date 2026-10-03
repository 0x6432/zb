const std = @import("std");
pub fn main() void {
    _ = std.c.printf("hello, %s %d\n", "world", @as(c_int, 42));
}
