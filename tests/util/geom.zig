pub const Point = struct {
    x: i64,
    y: i64,
    pub fn origin() Point {
        return .{ .x = 0, .y = 0 };
    }
    pub fn dist2(a: Point, b: Point) i64 {
        const dx = b.x - a.x;
        const dy = b.y - a.y;
        return dx * dx + dy * dy;
    }
};
