const std = @import("std");
const print = std.io.print;

const Op = enum { add, sub, mul, neg };
const Value = union(enum) {
    int: i64,
    boolean: bool,
    text: []const u8,
    nothing,
};

fn arity(comptime op: Op) usize {
    return switch (op) {
        .neg => 1,
        else => 2,
    };
}
fn apply(op: Op, a: i64, b: i64) i64 {
    return switch (op) {
        inline else => |o| blk: {
            const n = comptime arity(o);
            break :blk if (n == 1) -a else switch (o) {
                .add => a + b,
                .sub => a - b,
                .mul => a * b,
                else => unreachable,
            };
        },
    };
}
fn describe(v: Value) void {
    switch (v) {
        inline .int, .boolean => |x, tag| print("{s}={any} ", .{ @tagName(tag), x }),
        .text => |t| print("text={s} ", .{t}),
        .nothing => print("nothing ", .{}),
    }
}
fn typeName(comptime T: type) []const u8 {
    return switch (T) {
        u8 => "byte",
        i32, i64 => "signed",
        bool => "bool",
        else => "other",
    };
}
fn fieldSum(v: anytype) i64 {
    var total: i64 = 0;
    inline for (@typeInfo(@TypeOf(v)).@"struct".fields) |f| {
        total += @field(v, f.name);
    }
    return total;
}
fn collatz(start: u32) u32 {
    var steps: u32 = 0;
    sw: switch (start) {
        1 => {},
        else => |n| {
            steps += 1;
            if (n % 2 == 0) continue :sw n / 2;
            continue :sw 3 * n + 1;
        },
    }
    return steps;
}
const Kind = enum(u8) { a = 1, b = 2, _ };

pub fn main() void {
    inline for (.{ Op.add, Op.sub, Op.mul, Op.neg }) |op| {
        print("{s}:{d} ", .{ @tagName(op), apply(op, 7, 3) });
    }
    print("\n", .{});
    var ops = [_]Op{ .mul, .neg };
    for (ops[0..]) |o| print("{d} ", .{apply(o, 5, 6)});
    print("\n", .{});
    describe(.{ .int = 42 });
    describe(.{ .boolean = true });
    describe(.{ .text = "hi" });
    describe(.nothing);
    print("\n", .{});
    print("{s} {s} {s} {s}\n", .{ typeName(u8), typeName(i64), typeName(bool), typeName(u16) });
    print("{d}\n", .{fieldSum(.{ .a = @as(i64, 1), .b = @as(i64, 20), .c = @as(i64, 300) })});
    print("{d}\n", .{collatz(27)});
    const k: Kind = @enumFromInt(7);
    const r = switch (k) {
        .a => "a",
        .b => "b",
        _ => "other",
    };
    print("{s} {d}\n", .{ r, @intFromEnum(k) });
    ops[0] = .add;
    print("{any}\n", .{ops});
}
