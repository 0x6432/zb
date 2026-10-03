const std = @import("std");
const big = std.math.big.int;
pub fn main() void {
    var l1: [4]std.math.big.Limb = undefined;
    var l2: [8]std.math.big.Limb = undefined;
    const vals = [_]u128{ 1 << 64, 12345, (1 << 64) + 1, 1 << 100 };
    for (vals) |v| {
        const a = big.Mutable.init(&l1, v).toConst();
        const f, const ex = a.toFloat(f128, .nearest_even);
        var m: big.Mutable = .{ .limbs = &l2, .len = undefined, .positive = undefined };
        const ex2 = m.setFloat(f, .nearest_even);
        std.debug.print("{x} {t} {t} eql={} {d}\n", .{ @as(u128, @bitCast(f)), ex, ex2, m.toConst().eql(a), m.toConst().toInt(u128) catch 0 });
    }
}
