const std = @import("std");
const print = std.io.print;

const Config = struct {
    name: []const u8 = "default",
    level: u8 = 3,
    verbose: bool = false,
    pub const version = 2;
    pub fn describe() void {}
};

fn fieldNames(comptime T: type) []const []const u8 {
    const fields = @typeInfo(T).@"struct".fields;
    var names: [fields.len][]const u8 = undefined;
    for (fields, 0..) |f, i| names[i] = f.name;
    const final = names;
    return &final;
}

fn MakeStruct(comptime names: []const []const u8, comptime T: type) type {
    var types: [names.len]type = undefined;
    for (&types) |*t| t.* = T;
    return @Struct(.auto, null, names, &types, &@splat(.{}));
}

fn EnumFrom(comptime names: []const []const u8) type {
    var vals: [names.len]u8 = undefined;
    for (&vals, 0..) |*v, i| v.* = @intCast(i * 10);
    return @Enum(u8, .exhaustive, names, &vals);
}

fn defaultsOf(comptime T: type) T {
    var r: T = undefined;
    inline for (@typeInfo(T).@"struct".fields) |f| {
        @field(r, f.name) = f.defaultValue().?;
    }
    return r;
}

fn countDecls(comptime T: type) usize {
    return @typeInfo(T).@"struct".decls.len;
}

pub fn main() void {
    const names = comptime fieldNames(Config);
    inline for (names) |n| print("{s} ", .{n});
    print("\n", .{});
    print("{} {} {}\n", .{ @hasDecl(Config, "version"), @hasDecl(Config, "nope"), @hasField(Config, "level") });
    print("decls={d} fields={d}\n", .{ comptime countDecls(Config), @typeInfo(Config).@"struct".fields.len });
    const V = MakeStruct(&.{ "x", "y", "z" }, i32);
    const v: V = .{ .x = 1, .y = 2, .z = 3 };
    print("{any} size={d}\n", .{ v, @sizeOf(V) });
    const E = EnumFrom(&.{ "low", "mid", "high" });
    print("{d} {s}\n", .{ @intFromEnum(E.high), @tagName(@as(E, @enumFromInt(10))) });
    const d = comptime defaultsOf(Config);
    print("{s} {d} {}\n", .{ d.name, d.level, d.verbose });
    const T = @Tuple(&.{ u8, bool });
    const t: T = .{ 9, true };
    print("{any} {d}\n", .{ t, @typeInfo(T).@"struct".fields.len });
    const I = @Int(.unsigned, 12);
    print("{d} {d}\n", .{ @bitSizeOf(I), std.math.maxInt(I) });
    const P = @Pointer(.slice, .{ .@"const" = true }, u8, null);
    const p: P = "abc";
    print("{s} {}\n", .{ p, P == []const u8 });
    print("{s} {s}\n", .{ @typeName(u32), @typeName(?bool) });
    const info = @typeInfo([4:0]u16).array;
    print("{d} {} {?}\n", .{ info.len, info.child == u16, info.sentinel() });
    var cfg: Config = .{};
    inline for (@typeInfo(Config).@"struct".fields) |f| {
        if (f.type == u8) @field(cfg, f.name) += 10;
    }
    print("{d}\n", .{cfg.level});
    print("{d} {d}\n", .{ @offsetOf(Config, "level"), @alignOf(Config) });
}
