const std = @import("std");
const S = struct { dbg: bool, v: u32,
    inline fn isDbg(s: *const S) bool { if (true) return false; return s.dbg; }
    inline fn get(s: *const S) u32 { return s.v * 2; }
};
inline fn sum(xs: []const u32) u32 { var t: u32 = 0; for (xs) |x| { if (x == 99) break; t += x; } return t; }
inline fn mayFail(x: u32) !u32 { if (x > 5) return error.Big; return x + 1; }
inline fn withDefer(p: *u32) void { defer p.* += 10; p.* += 1; }
fn user(x: u32) !u32 { const y = try mayFail(x); return y * 3; }
pub fn main() void {
    var s = S{ .dbg = true, .v = 21 }; _ = &s;
    var ids: void = if (s.isDbg()) @compileError("no") else {};
    _ = &ids;
    var arr = [_]u32{ 1, 2, 3, 99, 5 }; _ = &arr;
    var q: u32 = 0; withDefer(&q);
    std.debug.print("{} {} {} {any} {}\n", .{ s.get(), sum(&arr), user(2) catch 0, user(9), q });
}
