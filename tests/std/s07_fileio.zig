const std = @import("std");
const Io = std.Io;
pub fn main(init: std.process.Init) !void {
    const io = init.io;
    const gpa = init.gpa;
    var buf: [1024]u8 = undefined;
    var fw = Io.File.stdout().writer(io, &buf);
    const out = &fw.interface;
    const cwd = Io.Dir.cwd();
    try cwd.writeFile(io, .{ .sub_path = "/tmp/zb_test.txt", .data = "line one\nline two\nline three\n" });
    const data = try cwd.readFileAlloc(io, "/tmp/zb_test.txt", gpa, .limited(1 << 20));
    defer gpa.free(data);
    var it = std.mem.splitScalar(u8, std.mem.trimEnd(u8, data, "\n"), '\n');
    var n: usize = 0;
    while (it.next()) |line| : (n += 1) try out.print("{d}: {s}\n", .{ n, line });
    var list: std.ArrayList(u64) = .empty;
    defer list.deinit(gpa);
    var i: u64 = 0;
    while (i < 20) : (i += 1) try list.append(gpa, i * i % 17);
    std.mem.sort(u64, list.items, {}, std.sort.desc(u64));
    try out.print("{any}\n", .{list.items});
    if (init.environ_map.get("PATH")) |h| try out.print("path set: {}\n", .{h.len > 0});
    try cwd.deleteFile(io, "/tmp/zb_test.txt");
    try out.flush();
}
