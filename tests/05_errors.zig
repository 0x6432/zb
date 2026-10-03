const std = @import("std");
const w = std.io;
const ParseError = error{ Empty, BadDigit };
fn parse(s: []const u8) ParseError!u32 {
    if (s.len == 0) return error.Empty;
    var v: u32 = 0;
    for (s) |ch| {
        if (ch < '0' or ch > '9') return error.BadDigit;
        v = v * 10 + (ch - '0');
    }
    return v;
}
fn twice(s: []const u8) !u32 {
    const v = try parse(s);
    return v * 2;
}
var log_count: u32 = 0;
fn withDefers(fail: bool) !u32 {
    defer log_count += 1;
    errdefer |e| {
        w.writeAll(1, "errdefer ");
        w.writeAll(1, @errorName(e));
        w.writeAll(1, "\n");
    }
    if (fail) return error.Boom;
    return 7;
}
pub fn main() !void {
    w.writeInt(1, try twice("21"));
    w.writeAll(1, "\n");
    const r = twice("2x1") catch |e| blk: {
        w.writeAll(1, @errorName(e));
        w.writeAll(1, "\n");
        break :blk 0;
    };
    w.writeInt(1, r);
    w.writeAll(1, "\n");
    w.writeInt(1, parse("") catch 99);
    w.writeAll(1, "\n");
    if (parse("123")) |v| {
        w.writeInt(1, v);
        w.writeAll(1, "\n");
    } else |_| {}
    _ = withDefers(true) catch 0;
    _ = try withDefers(false);
    w.writeInt(1, log_count);
    w.writeAll(1, "\n");
    _ = try parse("oops");
}
