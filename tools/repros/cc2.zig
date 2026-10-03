const std = @import("std");
const Alignment = @import("std").mem.Alignment;
const PackedCallingConvention = packed struct(u18) {
    tag: std.builtin.CallingConvention.Tag,
    /// May be ignored depending on `tag`.
    incoming_stack_alignment: Alignment2,
    /// Interpretation depends on `tag`.
    extra: u4,

    fn pack(cc: std.builtin.CallingConvention) PackedCallingConvention {
        return switch (cc) {
            inline else => |pl, tag| switch (@TypeOf(pl)) {
                void => .{
                    .tag = tag,
                    .incoming_stack_alignment = .none, // unused
                    .extra = 0, // unused
                },
                std.builtin.CallingConvention.CommonOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = 0, // unused
                },
                std.builtin.CallingConvention.X86RegparmOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = pl.register_params,
                },
                std.builtin.CallingConvention.ArcInterruptOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = @intFromEnum(pl.type),
                },
                std.builtin.CallingConvention.ArmInterruptOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = @intFromEnum(pl.type),
                },
                std.builtin.CallingConvention.MicroblazeInterruptOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = @intFromEnum(pl.type),
                },
                std.builtin.CallingConvention.MipsInterruptOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = @intFromEnum(pl.mode),
                },
                std.builtin.CallingConvention.RiscvInterruptOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = @intFromEnum(pl.mode),
                },
                std.builtin.CallingConvention.ShInterruptOptions => .{
                    .tag = tag,
                    .incoming_stack_alignment = .fromByteUnits(pl.incoming_stack_alignment orelse 0),
                    .extra = @intFromEnum(pl.save),
                },
                else => comptime unreachable,
            },
        };
    }

    fn unpack(cc: PackedCallingConvention) std.builtin.CallingConvention {
        return switch (cc.tag) {
            inline else => |tag| @unionInit(
                std.builtin.CallingConvention,
                @tagName(tag),
                switch (@FieldType(std.builtin.CallingConvention, @tagName(tag))) {
                    void => {},
                    std.builtin.CallingConvention.CommonOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                    },
                    std.builtin.CallingConvention.X86RegparmOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                        .register_params = @intCast(cc.extra),
                    },
                    std.builtin.CallingConvention.ArcInterruptOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                        .type = @enumFromInt(cc.extra),
                    },
                    std.builtin.CallingConvention.ArmInterruptOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                        .type = @enumFromInt(cc.extra),
                    },
                    std.builtin.CallingConvention.MicroblazeInterruptOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                        .type = @enumFromInt(cc.extra),
                    },
                    std.builtin.CallingConvention.MipsInterruptOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                        .mode = @enumFromInt(cc.extra),
                    },
                    std.builtin.CallingConvention.RiscvInterruptOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                        .mode = @enumFromInt(cc.extra),
                    },
                    std.builtin.CallingConvention.ShInterruptOptions => .{
                        .incoming_stack_alignment = cc.incoming_stack_alignment.toByteUnits(),
                        .save = @enumFromInt(cc.extra),
                    },
                    else => comptime unreachable,
                },
            ),
        };
    }
};


const Alignment2 = enum(u6) { none = std.math.maxInt(u6), _,
  pub fn fromByteUnits(n: u64) Alignment2 { if (n == 0) return .none; return @enumFromInt(@ctz(n)); }
  pub fn toByteUnits(a: Alignment2) ?u64 { return if (a == .none) null else @as(u64, 1) << @intFromEnum(a); } };
const Flags = packed struct(u32) {
    cc: PackedCallingConvention,
    is_var_args: bool,
    has_comptime_bits: bool,
    has_noalias_bits: bool,
    is_noinline: bool,
    _: u10 = 0,
};
const TF = struct { params_len: u32, return_type: u32, flags: Flags };
fn store(cc: std.builtin.CallingConvention, ex: []u32) void {
    const tf: TF = .{ .params_len = 1, .return_type = 2, .flags = .{ .cc = .pack(cc), .is_var_args = false, .has_comptime_bits = true, .has_noalias_bits = false, .is_noinline = false } };
    inline for (@typeInfo(TF).@"struct".fields, 0..) |f, i| {
        ex[i] = switch (f.type) { u32 => @field(tf, f.name), Flags => @bitCast(@field(tf, f.name)), else => unreachable };
    }
}
fn load(ex: []const u32) TF {
    var r: TF = undefined;
    inline for (@typeInfo(TF).@"struct".fields, 0..) |f, i| {
        @field(r, f.name) = switch (f.type) { u32 => ex[i], Flags => @bitCast(ex[i]), else => unreachable };
    }
    return r;
}
pub fn main() void {
    dbg();
    var ex: [3]u32 = undefined;
    var cc: std.builtin.CallingConvention = .auto;
    _ = &cc;
    store(cc, &ex);
    std.debug.print("{x}\n", .{ex[2]});
    const r = load(&ex);
    std.debug.print("{t} {}\n", .{ r.flags.cc.unpack(), r.flags.has_comptime_bits });
}
pub fn dbg() void {
    std.debug.print("{d} {d} {d} {d} {d}\n", .{ @bitOffsetOf(Flags, "is_var_args"), @bitOffsetOf(PackedCallingConvention, "incoming_stack_alignment"), @bitOffsetOf(PackedCallingConvention, "extra"), @bitSizeOf(PackedCallingConvention), @bitSizeOf(std.builtin.CallingConvention.Tag) });
}
