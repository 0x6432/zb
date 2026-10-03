const std = @import("std");
const FileErr = error{ NotFound, Denied };
const NetErr = error{ Timeout, Denied };
const All = FileErr || NetErr;
fn open(x: u8) FileErr!u8 { return if (x == 0) error.NotFound else if (x == 1) error.Denied else x; }
fn conn(x: u8) NetErr!void { if (x == 0) return error.Timeout; }
fn both(x: u8) All!u8 { try conn(x); return open(x); }
fn rec(n: u8) !u8 { if (n == 0) return error.Bottom; return rec(n - 1); }
fn gen(comptime T: type, x: T) !T { if (x == 0) return error.GenZero; return x; }
fn names(comptime E: type) void { inline for (@typeInfo(E).error_set.error_names.?) |n| std.debug.print("{s} ", .{n}); std.debug.print("\n", .{}); }
pub fn main() void {
    names(FileErr); std.debug.print("{}\n", .{@typeInfo(All).error_set.error_names.?.len}); names(@typeInfo(@typeInfo(@TypeOf(rec)).@"fn".return_type.?).error_union.error_set);
    names(@typeInfo(@TypeOf(gen(u8, 3))).error_union.error_set);
    std.debug.print("{} {} {}\n", .{ FileErr == error{ Denied, NotFound }, @typeInfo(anyerror).error_set.error_names == null, @TypeOf(open) == fn (u8) FileErr!u8 });
    var x: u8 = 1; _ = &x;
    const r = both(x) catch |e| switch (e) {
        error.NotFound => @as(u8, 10), error.Denied => 11, error.Timeout => 12,
    };
    const ee: anyerror = FileErr.Denied;
    const fe: FileErr = @errorCast(ee);
    std.debug.print("{} {s} {} {}\n", .{ r, @errorName(fe), fe == error.Denied, @TypeOf(fe) == FileErr });
    std.debug.print("{any} {any}\n", .{ rec(2), gen(u8, 0) });
}
