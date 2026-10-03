const std = @import("std");
const Mem = struct { info: u32, b: i32 };
const Inst = struct { tag: u8, data: union { x: struct { fixes: u8 = 0, payload: u32 }, y: u64 } };
const CG = struct {
    extra: std.ArrayList(u32) = .empty,
    fn addExtra(self: *CG, extra: anytype) error{OutOfMemory}!u32 {
        const fields = std.meta.fields(@TypeOf(extra));
        const r: u32 = @intCast(self.extra.items.len);
        inline for (fields) |field| try self.extra.append(std.heap.page_allocator, switch (field.type) {
            u32 => @field(extra, field.name),
            i32 => @bitCast(@field(extra, field.name)),
            else => @compileError("bad"),
        });
        return r;
    }
    fn addInst(self: *CG, i: Inst) !void { _ = self; std.debug.print("{} {}\n", .{ i.tag, i.data.x.payload }); }
};
fn enc(a: u32) Mem { return .{ .info = a, .b = -1 }; }
pub fn main() !void {
    var cg: CG = .{};
    var k: u8 = 1; _ = &k;
    switch (k) {
        1 => try cg.addInst(.{ .tag = 5, .data = .{ .x = .{ .payload = try cg.addExtra(enc(7)) } } }),
        else => {},
    }
    try cg.addInst(.{ .tag = 6, .data = .{ .x = .{ .payload = try cg.addExtra(enc(8)) } } });
    std.debug.print("{any}\n", .{cg.extra.items});
}
