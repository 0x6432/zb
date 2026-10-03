const std = @import("std");
const S = struct { size: ?u8 = null, b: u8 = 3 };
fn dv(comptime T: type, comptime name: []const u8) ?@FieldType(T, name) {
    inline for (@typeInfo(T).@"struct".fields) |f| if (comptime std.mem.eql(u8, f.name, name)) return f.defaultValue();
    return null;
}
pub fn main() void {
    const a = comptime dv(S, "size") orelse @compileError("missing");
    const b = comptime (dv(S, "b") orelse unreachable);
    std.debug.print("{?} {}\n", .{ a, b });
}
