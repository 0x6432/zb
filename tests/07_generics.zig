const std = @import("std");
const w = std.io;
fn Pair(comptime A: type, comptime B: type) type {
    return struct {
        a: A,
        b: B,
        const Self = @This();
        fn swap(self: Self) Pair(B, A) {
            return .{ .a = self.b, .b = self.a };
        }
    };
}
fn max(comptime T: type, a: T, b: T) T {
    return if (a > b) a else b;
}
fn sumAll(xs: anytype) i64 {
    var s: i64 = 0;
    for (xs) |x| s += x;
    return s;
}
fn Stack(comptime T: type, comptime N: usize) type {
    return struct {
        buf: [N]T = undefined,
        len: usize = 0,
        fn push(self: *@This(), v: T) void {
            self.buf[self.len] = v;
            self.len += 1;
        }
        fn pop(self: *@This()) T {
            self.len -= 1;
            return self.buf[self.len];
        }
    };
}
pub fn main() !void {
    const p = Pair(u8, i32){ .a = 7, .b = -3 };
    const q = p.swap();
    w.writeInt(1, q.a);
    w.writeAll(1, " ");
    w.writeInt(1, q.b);
    w.writeAll(1, "\n");
    w.writeInt(1, max(u16, 300, 200));
    w.writeAll(1, " ");
    w.writeInt(1, max(i8, -5, -9));
    w.writeAll(1, "\n");
    const arr = [_]i64{ 1, 2, 3, 4 };
    w.writeInt(1, sumAll(arr));
    w.writeAll(1, "\n");
    var st = Stack(u32, 4){};
    st.push(10);
    st.push(20);
    w.writeInt(1, st.pop() + st.pop());
    w.writeAll(1, "\n");
    var list = std.ArrayList(u64){};
    defer list.deinit();
    for (0..100) |i| try list.append(i * 3);
    w.writeInt(1, @intCast(list.items.len));
    w.writeAll(1, " ");
    w.writeInt(1, @intCast(list.items[99]));
    w.writeAll(1, " ");
    w.writeInt(1, @intCast(list.pop().?));
    w.writeAll(1, "\n");
    if (Pair(u8, u8) == Pair(u8, u8)) w.writeAll(1, "memoized\n");
}
