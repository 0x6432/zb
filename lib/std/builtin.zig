//! Shim of std.builtin for zb (used when --std-dir is not given).
//! `Type` is a verbatim copy of Zig 0.16's std.builtin.Type.
pub const Signedness = enum(u1) { signed, unsigned };
pub const AddressSpace = enum(u5) { generic, gs, fs, ss };
pub const CallingConvention = union(enum(u8)) { auto, async, naked, inline_, c, x86_64_sysv: CommonOptions, pub const CommonOptions = struct { incoming_stack_alignment: ?u64 = null }; };
pub const OptimizeMode = enum { Debug, ReleaseSafe, ReleaseFast, ReleaseSmall };
pub const Endian = enum { big, little };
pub const StackTrace = struct { index: usize, instruction_addresses: []usize };
pub const CallModifier = enum { auto, never_tail, never_inline, no_suspend, always_tail, always_inline, compile_time };
pub const AtomicOrder = enum { unordered, monotonic, acquire, release, acq_rel, seq_cst };
pub const AtomicRmwOp = enum { Xchg, Add, Sub, And, Nand, Or, Xor, Max, Min };
pub const ReduceOp = enum { And, Or, Xor, Min, Max, Add, Mul };
pub const SourceLocation = struct { module: [:0]const u8, file: [:0]const u8, fn_name: [:0]const u8, line: u32, column: u32 };
pub const BranchHint = enum(u3) { none, likely, unlikely, cold, unpredictable };
pub const Type = union(enum) {
    type,
    void,
    bool,
    noreturn,
    int: Int,
    float: Float,
    pointer: Pointer,
    array: Array,
    @"struct": Struct,
    comptime_float,
    comptime_int,
    undefined,
    null,
    optional: Optional,
    error_union: ErrorUnion,
    error_set: ErrorSet,
    @"enum": Enum,
    @"union": Union,
    @"fn": Fn,
    @"opaque": Opaque,
    frame: Frame,
    @"anyframe": AnyFrame,
    vector: Vector,
    enum_literal,

    pub const Int = struct {
        signedness: Signedness,
        bits: u16,
    };

    pub const Float = struct {
        bits: u16,
    };

    pub const Pointer = struct {
        size: Size,
        is_const: bool,
        is_volatile: bool,
        alignment: ?usize,
        address_space: AddressSpace,
        child: type,
        is_allowzero: bool,

        sentinel_ptr: ?*const anyopaque,

        pub inline fn sentinel(comptime ptr: Pointer) ?ptr.child {
            const sp: *const ptr.child = @ptrCast(@alignCast(ptr.sentinel_ptr orelse return null));
            return sp.*;
        }

        pub const Size = enum(u2) {
            one,
            many,
            slice,
            c,
        };

        pub const Attributes = struct {
            @"const": bool = false,
            @"volatile": bool = false,
            @"allowzero": bool = false,
            @"addrspace": ?AddressSpace = null,
            @"align": ?usize = null,
        };
    };

    pub const Array = struct {
        len: comptime_int,
        child: type,

        sentinel_ptr: ?*const anyopaque,

        pub inline fn sentinel(comptime arr: Array) ?arr.child {
            const sp: *const arr.child = @ptrCast(@alignCast(arr.sentinel_ptr orelse return null));
            return sp.*;
        }
    };

    pub const ContainerLayout = enum(u2) {
        auto,
        @"extern",
        @"packed",
    };

    pub const StructField = struct {
        name: [:0]const u8,
        type: type,
        default_value_ptr: ?*const anyopaque,
        is_comptime: bool,
        alignment: ?usize,

        pub inline fn defaultValue(comptime sf: StructField) ?sf.type {
            const dp: *const sf.type = @ptrCast(@alignCast(sf.default_value_ptr orelse return null));
            return dp.*;
        }

        pub const Attributes = struct {
            @"comptime": bool = false,
            @"align": ?usize = null,
            default_value_ptr: ?*const anyopaque = null,
        };
    };

    pub const Struct = struct {
        layout: ContainerLayout,
        backing_integer: ?type = null,
        fields: []const StructField,
        decls: []const Declaration,
        is_tuple: bool,
    };

    pub const Optional = struct {
        child: type,
    };

    pub const ErrorUnion = struct {
        error_set: type,
        payload: type,
    };

    pub const Error = struct {
        name: [:0]const u8,
    };

    pub const ErrorSet = ?[]const Error;

    pub const EnumField = struct {
        name: [:0]const u8,
        value: comptime_int,
    };

    pub const Enum = struct {
        tag_type: type,
        fields: []const EnumField,
        decls: []const Declaration,
        is_exhaustive: bool,

        pub const Mode = enum { exhaustive, nonexhaustive };
    };

    pub const UnionField = struct {
        name: [:0]const u8,
        type: type,
        alignment: ?usize,

        pub const Attributes = struct {
            @"align": ?usize = null,
        };
    };

    pub const Union = struct {
        layout: ContainerLayout,
        tag_type: ?type,
        fields: []const UnionField,
        decls: []const Declaration,
    };

    pub const Fn = struct {
        calling_convention: CallingConvention,
        is_generic: bool,
        is_var_args: bool,
        return_type: ?type,
        params: []const Param,

        pub const Param = struct {
            is_generic: bool,
            is_noalias: bool,
            type: ?type,

            pub const Attributes = struct {
                @"noalias": bool = false,
            };
        };

        pub const Attributes = struct {
            @"callconv": CallingConvention = .auto,
            varargs: bool = false,
        };
    };

    pub const Opaque = struct {
        decls: []const Declaration,
    };

    pub const Frame = struct {
        function: *const anyopaque,
    };

    pub const AnyFrame = struct {
        child: ?type,
    };

    pub const Vector = struct {
        len: comptime_int,
        child: type,
    };

    pub const Declaration = struct {
        name: [:0]const u8,
    };
};

