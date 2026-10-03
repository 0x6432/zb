const std = @import("std");
const w = std.io;
const Vec2 = struct {
    x: i32,
    y: i32 = 5,
    pub fn add(self: Vec2, o: Vec2) Vec2 {
        return .{ .x = self.x + o.x, .y = self.y + o.y };
    }
    pub fn scale(self: *Vec2, k: i32) void {
        self.x *= k;
        self.y *= k;
    }
    pub fn len2(self: Vec2) i32 {
        return self.x * self.x + self.y * self.y;
    }
};
const Rect = struct { min: Vec2, max: Vec2 };
fn area(r: *const Rect) i32 {
    return (r.max.x - r.min.x) * (r.max.y - r.min.y);
}
pub fn main() void {
    var a = Vec2{ .x = 1, .y = 2 };
    const b: Vec2 = .{ .x = 10 };
    var c = a.add(b);
    c.scale(2);
    w.writeInt(1, c.x);
    w.writeAll(1, " ");
    w.writeInt(1, c.y);
    w.writeAll(1, " ");
    w.writeInt(1, c.len2());
    w.writeAll(1, "\n");
    const r = Rect{ .min = .{ .x = 0, .y = 0 }, .max = .{ .x = 4, .y = 3 } };
    w.writeInt(1, area(&r));
    w.writeAll(1, "\n");
    const p = &a;
    p.x = 100;
    w.writeInt(1, a.x);
    w.writeAll(1, "\n");
    w.writeInt(1, @sizeOf(Rect));
    w.writeAll(1, "\n");
}
