const std = @import("std");
pub fn main(init: std.process.Init) !void {
    const io = init.io;
    var buf: [256]u8 = undefined;
    var fw = std.Io.File.stdout().writer(io, &buf);
    const out = &fw.interface;
    try out.print("hello {s} {d}\n", .{ "stdout", 42 });
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    try out.print("argc={d}\n", .{args.len});
    try out.flush();
}
