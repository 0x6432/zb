//! Minimal std shim for the zb bootstrap compiler (core-language milestone).
pub const builtin = @import("std/builtin.zig");

pub const c = struct {
    pub extern fn printf(fmt: [*:0]const u8, ...) c_int;
    pub extern fn write(fd: c_int, buf: [*]const u8, n: usize) isize;
    pub extern fn exit(code: c_int) noreturn;
    pub extern fn abort() noreturn;
    pub extern fn malloc(n: usize) ?*anyopaque;
    pub extern fn realloc(p: ?*anyopaque, n: usize) ?*anyopaque;
    pub extern fn free(p: ?*anyopaque) void;
    pub extern fn snprintf(buf: [*]u8, n: usize, fmt: [*:0]const u8, ...) c_int;
    pub extern fn strtod(s: [*:0]const u8, end: ?*?[*:0]u8) f64;
};

pub const process = struct {
    pub fn exit(code: u8) noreturn {
        c.exit(code);
    }
};

pub const debug = struct {
    pub fn assert(ok: bool) void {
        if (!ok) unreachable;
    }
    /// Formatted print to stderr (like std.debug.print).
    pub fn print(comptime f: []const u8, args: anytype) void {
        var w: fmt.BufWriter = .{ .fd = 2 };
        fmt.format(&w, f, args);
        w.flush();
    }
    pub fn panic(comptime f: []const u8, args: anytype) noreturn {
        print(f, args);
        c.abort();
    }
};

pub const io = struct {
    /// zb shim extension: formatted print to stdout.
    pub fn print(comptime f: []const u8, args: anytype) void {
        var w: fmt.BufWriter = .{ .fd = 1 };
        fmt.format(&w, f, args);
        w.flush();
    }
    pub fn writeAll(fd: c_int, bytes: []const u8) void {
        _ = c.write(fd, bytes.ptr, bytes.len);
    }
    pub fn writeInt(fd: c_int, v: i64) void {
        var buf: [24]u8 = undefined;
        var i: usize = buf.len;
        var n: u64 = if (v < 0) @intCast(-v) else @intCast(v);
        if (n == 0) {
            i -= 1;
            buf[i] = '0';
        }
        while (n != 0) : (n /= 10) {
            i -= 1;
            buf[i] = @intCast('0' + n % 10);
        }
        if (v < 0) {
            i -= 1;
            buf[i] = '-';
        }
        writeAll(fd, buf[i..]);
    }
};

pub const mem = struct {
    pub fn eql(comptime T: type, a: []const T, b: []const T) bool {
        if (a.len != b.len) return false;
        for (a, b) |x, y| {
            if (x != y) return false;
        }
        return true;
    }
    pub fn indexOfScalar(comptime T: type, haystack: []const T, needle: T) ?usize {
        for (haystack, 0..) |x, i| {
            if (x == needle) return i;
        }
        return null;
    }
    pub fn sliceTo(p: [*:0]const u8) []const u8 {
        var n: usize = 0;
        while (p[n] != 0) n += 1;
        return p[0..n];
    }
};

pub const math = struct {
    pub fn maxInt(comptime T: type) comptime_int {
        const info = @typeInfo(T).int;
        const bits = info.bits;
        if (bits == 0) return 0;
        return (1 << (bits - @intFromBool(info.signedness == .signed))) - 1;
    }
    pub fn minInt(comptime T: type) comptime_int {
        const info = @typeInfo(T).int;
        const bits = info.bits;
        if (info.signedness == .unsigned or bits == 0) return 0;
        return -(1 << (bits - 1));
    }
};

pub const fmt = struct {
    pub const BufWriter = struct {
        fd: c_int,
        buf: [256]u8 = undefined,
        n: usize = 0,
        pub fn writeAll(self: *BufWriter, bytes: []const u8) void {
            if (self.n + bytes.len > self.buf.len) {
                self.flush();
                if (bytes.len > self.buf.len) {
                    _ = c.write(self.fd, bytes.ptr, bytes.len);
                    return;
                }
            }
            @memcpy(self.buf[self.n..][0..bytes.len], bytes);
            self.n += bytes.len;
        }
        pub fn writeByte(self: *BufWriter, b: u8) void {
            if (self.n == self.buf.len) self.flush();
            self.buf[self.n] = b;
            self.n += 1;
        }
        pub fn flush(self: *BufWriter) void {
            if (self.n > 0) _ = c.write(self.fd, &self.buf, self.n);
            self.n = 0;
        }
        pub fn print(self: *BufWriter, comptime f: []const u8, args: anytype) void {
            format(self, f, args);
        }
    };
    pub const MemWriter = struct {
        buf: []u8,
        n: usize = 0,
        pub fn writeAll(self: *MemWriter, bytes: []const u8) void {
            for (bytes) |b| self.writeByte(b);
        }
        pub fn writeByte(self: *MemWriter, b: u8) void {
            if (self.n < self.buf.len) self.buf[self.n] = b;
            self.n += 1;
        }
    };
    pub const BufPrintError = error{NoSpaceLeft};
    pub fn bufPrint(buf: []u8, comptime f: []const u8, args: anytype) BufPrintError![]u8 {
        var w: MemWriter = .{ .buf = buf };
        format(&w, f, args);
        if (w.n > buf.len) return error.NoSpaceLeft;
        return buf[0..w.n];
    }

    const Opts = struct {
        spec: []const u8 = "",
        fill: u8 = ' ',
        alignment: u8 = '>',
        width: usize = 0,
        prec: ?usize = null,
    };
    fn isDigit(ch: u8) bool {
        return ch >= '0' and ch <= '9';
    }
    fn parseOpts(comptime s: []const u8) Opts {
        var o: Opts = .{};
        var i: usize = 0;
        while (i < s.len and s[i] != ':') : (i += 1) {}
        o.spec = s[0..i];
        if (i < s.len) {
            i += 1;
            if (i + 1 < s.len and (s[i + 1] == '<' or s[i + 1] == '^' or s[i + 1] == '>')) {
                o.fill = s[i];
                o.alignment = s[i + 1];
                i += 2;
            } else if (i < s.len and (s[i] == '<' or s[i] == '^' or s[i] == '>')) {
                o.alignment = s[i];
                i += 1;
            } else if (i + 1 < s.len and s[i] == '0' and isDigit(s[i + 1])) {
                o.fill = '0';
                i += 1;
            }
            while (i < s.len and isDigit(s[i])) : (i += 1) o.width = o.width * 10 + (s[i] - '0');
            if (i < s.len and s[i] == '.') {
                i += 1;
                var pr: usize = 0;
                while (i < s.len and isDigit(s[i])) : (i += 1) pr = pr * 10 + (s[i] - '0');
                o.prec = pr;
            }
        }
        return o;
    }
    fn eqlStr(comptime a: []const u8, comptime b: []const u8) bool {
        if (a.len != b.len) return false;
        for (a, b) |x, y| if (x != y) return false;
        return true;
    }

    /// Formats `args` according to the format string `f` (subset of std.fmt).
    pub fn format(w: anytype, comptime f: []const u8, args: anytype) void {
        const fields = @typeInfo(@TypeOf(args)).@"struct".fields;
        comptime var i: usize = 0;
        comptime var arg: usize = 0;
        comptime var lit: usize = 0;
        inline while (i < f.len) {
            const ch = f[i];
            if (ch == '{' and i + 1 < f.len and f[i + 1] == '{') {
                w.writeAll(f[lit .. i + 1]);
                i += 2;
                lit = i;
            } else if (ch == '}' and i + 1 < f.len and f[i + 1] == '}') {
                w.writeAll(f[lit .. i + 1]);
                i += 2;
                lit = i;
            } else if (ch == '{') {
                if (i > lit) w.writeAll(f[lit..i]);
                comptime var j = i + 1;
                inline while (f[j] != '}') j += 1;
                const opts = comptime parseOpts(f[i + 1 .. j]);
                formatAligned(w, opts, @field(args, fields[arg].name));
                arg += 1;
                i = j + 1;
                lit = i;
            } else {
                i += 1;
            }
        }
        if (lit < f.len) w.writeAll(f[lit..]);
    }
    fn formatAligned(w: anytype, comptime o: Opts, value: anytype) void {
        if (o.width == 0) return formatValue(w, o, value);
        var tmp: [256]u8 = undefined;
        var m: MemWriter = .{ .buf = &tmp };
        formatValue(&m, o, value);
        const n = if (m.n > tmp.len) tmp.len else m.n;
        if (n >= o.width) return w.writeAll(tmp[0..n]);
        const pad = o.width - n;
        const left = if (o.alignment == '<') 0 else if (o.alignment == '^') pad / 2 else pad;
        var k: usize = 0;
        while (k < left) : (k += 1) w.writeByte(o.fill);
        w.writeAll(tmp[0..n]);
        k = left;
        while (k < pad) : (k += 1) w.writeByte(o.fill);
    }
    fn stripOpt(comptime o: Opts) Opts {
        var r = o;
        r.spec = if (o.spec.len > 0 and (o.spec[0] == '?' or o.spec[0] == '!')) o.spec[1..] else o.spec;
        return r;
    }
    fn anyOpts(comptime o: Opts) Opts {
        var r = o;
        r.spec = "any";
        return r;
    }
    pub fn formatInt(w: anytype, value: anytype, comptime base: u8, comptime upper: bool) void {
        const V = if (@TypeOf(value) == comptime_int) i64 else @TypeOf(value);
        const x: V = value;
        const info = @typeInfo(V).int;
        const U = if (info.bits > 64) u128 else u64;
        const S = if (info.bits > 64) i128 else i64;
        var u: U = undefined;
        var neg = false;
        if (info.signedness == .signed) {
            const sx: S = x;
            if (sx < 0) {
                neg = true;
                u = @bitCast(0 -% sx);
            } else u = @intCast(sx);
        } else u = x;
        var buf: [136]u8 = undefined;
        var i: usize = buf.len;
        if (u == 0) {
            i -= 1;
            buf[i] = '0';
        }
        while (u != 0) : (u /= base) {
            i -= 1;
            const d: u8 = @intCast(u % base);
            buf[i] = if (d < 10) '0' + d else (if (upper) 'A' else 'a') + d - 10;
        }
        if (neg) {
            i -= 1;
            buf[i] = '-';
        }
        w.writeAll(buf[i..]);
    }
    /// Zig-style float formatting: shortest round-trip digits, decimal or scientific.
    pub fn formatFloat(w: anytype, value: anytype, comptime sci: bool, comptime prec: ?usize) void {
        const T = @TypeOf(value);
        const x: f64 = if (T == comptime_float) value else @floatCast(value);
        const xbits: u64 = @bitCast(x);
        if (x != x) return w.writeAll(if (xbits >> 63 != 0) "-nan" else "nan");
        if (x - x != x - x) return w.writeAll(if (x < 0) "-inf" else "inf");
        var buf: [400]u8 = undefined;
        if (prec) |pp| {
            if (!sci) {
                const n = c.snprintf(&buf, buf.len, "%.*f", @as(c_int, @intCast(pp)), x);
                return w.writeAll(buf[0..@intCast(n)]);
            }
        }
        // find shortest digit string that round-trips
        var n: c_int = 0;
        var p: c_int = 0;
        if (prec) |pp| {
            p = @intCast(pp);
            n = c.snprintf(&buf, buf.len, "%.*e", p, x);
        } else while (p < 17) : (p += 1) {
            n = c.snprintf(&buf, buf.len, "%.*e", p, x);
            buf[@intCast(n)] = 0;
            const back = c.strtod(@ptrCast(&buf), null);
            if (T == f32) {
                const b32: f32 = @floatCast(back);
                if (b32 == value) break;
            } else if (back == x) break;
        }
        const s = buf[0..@intCast(n)];
        var i: usize = 0;
        var neg = false;
        if (s[0] == '-') {
            neg = true;
            i = 1;
        }
        var digits: [40]u8 = undefined;
        var nd: usize = 0;
        while (s[i] != 'e') : (i += 1) {
            if (s[i] != '.') {
                digits[nd] = s[i];
                nd += 1;
            }
        }
        i += 1;
        var eneg = false;
        if (s[i] == '-') eneg = true;
        i += 1;
        var e: i32 = 0;
        while (i < s.len) : (i += 1) e = e * 10 + @as(i32, s[i] - '0');
        if (eneg) e = -e;
        if (prec == null) {
            while (nd > 1 and digits[nd - 1] == '0') nd -= 1;
        }
        if (neg) w.writeByte('-');
        if (sci) {
            w.writeByte(digits[0]);
            if (nd > 1) {
                w.writeByte('.');
                w.writeAll(digits[1..nd]);
            }
            w.writeByte('e');
            return formatInt(w, e, 10, false);
        }
        if (e >= 0) {
            const ip: usize = @intCast(e + 1);
            var k: usize = 0;
            while (k < ip) : (k += 1) w.writeByte(if (k < nd) digits[k] else '0');
            if (nd > ip) {
                w.writeByte('.');
                w.writeAll(digits[ip..nd]);
            }
        } else {
            w.writeAll("0.");
            var k: i32 = -1;
            while (k > e) : (k -= 1) w.writeByte('0');
            w.writeAll(digits[0..nd]);
        }
    }
    fn baseOf(comptime spec: []const u8) u8 {
        if (eqlStr(spec, "x") or eqlStr(spec, "X")) return 16;
        if (eqlStr(spec, "b")) return 2;
        if (eqlStr(spec, "o")) return 8;
        return 10;
    }
    pub fn formatValue(w: anytype, comptime o: Opts, value: anytype) void {
        const T = @TypeOf(value);
        const spec = o.spec;
        if (comptime eqlStr(spec, "c")) return w.writeByte(@intCast(value));
        if (comptime eqlStr(spec, "s")) {
            switch (@typeInfo(T)) {
                .pointer => |p| {
                    if (p.size == .many) return w.writeAll(mem.sliceTo(value));
                    return w.writeAll(value);
                },
                .array => return w.writeAll(&value),
                .optional => {
                    if (value) |v| return formatValue(w, o, v);
                    return w.writeAll("null");
                },
                else => @compileError("invalid format string 's' for type " ++ @typeName(T)),
            }
        }
        if (comptime eqlStr(spec, "t")) {
            switch (@typeInfo(T)) {
                .error_set => return w.writeAll(@errorName(value)),
                else => return w.writeAll(@tagName(value)),
            }
        }
        switch (@typeInfo(T)) {
            .int, .comptime_int => return formatInt(w, value, comptime baseOf(spec), comptime eqlStr(spec, "X")),
            .float, .comptime_float => return formatFloat(w, value, comptime (eqlStr(spec, "e") or eqlStr(spec, "E")), o.prec),
            .bool => return w.writeAll(if (value) "true" else "false"),
            .void => return w.writeAll("void"),
            .null => return w.writeAll("null"),
            .type => return w.writeAll(@typeName(value)),
            .optional => {
                if (value) |v| return formatValue(w, comptime stripOpt(o), v);
                return w.writeAll("null");
            },
            .error_union => {
                if (value) |v| {
                    return formatValue(w, comptime stripOpt(o), v);
                } else |e| {
                    w.writeAll("error.");
                    return w.writeAll(@errorName(e));
                }
            },
            .error_set => {
                w.writeAll("error.");
                return w.writeAll(@errorName(value));
            },
            .@"enum" => {
                if (comptime eqlStr(spec, "d") or eqlStr(spec, "x")) return formatInt(w, @intFromEnum(value), comptime baseOf(spec), false);
                w.writeByte('.');
                return w.writeAll(@tagName(value));
            },
            .enum_literal => {
                w.writeByte('.');
                return w.writeAll(@tagName(value));
            },
            .@"union" => |u| {
                if (u.tag_type) |Tag| {
                    w.writeAll(".{ .");
                    w.writeAll(@tagName(@as(Tag, value)));
                    w.writeAll(" = ");
                    inline for (u.fields) |fld| {
                        if (value == @field(Tag, fld.name)) formatValue(w, comptime anyOpts(o), @field(value, fld.name));
                    }
                    w.writeAll(" }");
                } else w.writeAll(".{ ... }");
            },
            .@"struct" => |st| {
                if (st.fields.len == 0) return w.writeAll(".{}");
                w.writeAll(".{");
                inline for (st.fields, 0..) |fld, i| {
                    w.writeAll(if (i == 0) " " else ", ");
                    if (!st.is_tuple) {
                        w.writeByte('.');
                        w.writeAll(fld.name);
                        w.writeAll(" = ");
                    }
                    formatValue(w, comptime anyOpts(o), @field(value, fld.name));
                }
                w.writeAll(" }");
            },
            .pointer => |p| switch (p.size) {
                .one => switch (@typeInfo(p.child)) {
                    .array => |a| return formatValue(w, o, @as([]const a.child, value)),
                    .@"struct", .@"union", .@"enum" => return formatValue(w, o, value.*),
                    else => {
                        w.writeAll(@typeName(p.child));
                        w.writeByte('@');
                        return formatInt(w, @intFromPtr(value), 16, false);
                    },
                },
                .slice => {
                    w.writeAll("{ ");
                    for (value, 0..) |e, i| {
                        formatValue(w, o, e);
                        if (i != value.len - 1) w.writeAll(", ");
                    }
                    w.writeAll(" }");
                },
                else => {
                    w.writeAll(@typeName(p.child));
                    w.writeByte('@');
                    return formatInt(w, @intFromPtr(value), 16, false);
                },
            },
            .array, .vector => {
                w.writeAll("{ ");
                for (value, 0..) |e, i| {
                    formatValue(w, o, e);
                    if (i != value.len - 1) w.writeAll(", ");
                }
                w.writeAll(" }");
            },
            else => @compileError("cannot format type " ++ @typeName(T)),
        }
    }
};

pub fn ArrayList(comptime T: type) type {
    return struct {
        const Self = @This();
        items: []T = &.{},
        capacity: usize = 0,

        pub fn deinit(self: *Self) void {
            if (self.capacity != 0) c.free(self.items.ptr);
        }
        pub fn append(self: *Self, item: T) !void {
            if (self.items.len == self.capacity) {
                const new_cap = if (self.capacity == 0) 8 else self.capacity * 2;
                const p = c.realloc(if (self.capacity == 0) null else @ptrCast(self.items.ptr), new_cap * @sizeOf(T)) orelse return error.OutOfMemory;
                const tp: [*]T = @ptrCast(@alignCast(p));
                self.items = tp[0..self.items.len];
                self.capacity = new_cap;
            }
            self.items.len += 1;
            self.items[self.items.len - 1] = item;
        }
        pub fn pop(self: *Self) ?T {
            if (self.items.len == 0) return null;
            self.items.len -= 1;
            return self.items[self.items.len];
        }
    };
}
