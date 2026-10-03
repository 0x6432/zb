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
pub fn main() void {
    var cc: std.builtin.CallingConvention = .auto;
    _ = &cc;
    const p = PackedCallingConvention.pack(cc);
    std.debug.print("{t} {d}\n", .{ p.tag, @intFromEnum(p.tag) });
    const u = p.unpack();
    std.debug.print("{t}\n", .{u});
    var c2: std.builtin.CallingConvention = .{ .x86_64_sysv = .{} };
    _ = &c2;
    std.debug.print("{t} {t}\n", .{ PackedCallingConvention.pack(c2).unpack(), PackedCallingConvention.pack(c2).tag });
}
