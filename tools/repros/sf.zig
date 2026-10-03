const std = @import("std");
const big = std.math.big.int;
pub fn main() void {
    var limbs: [8]std.math.big.Limb = undefined;
    const vals = [_]f128{ 1.5, 255.0, 3.0e20, 0.75, 123456789.0 };
    for (vals) |v| {
        var vv = v; _ = &vv;
        const Repr = std.math.FloatRepr(f128);
        const repr: Repr = @bitCast(vv);
        std.debug.print("exp {d} mant {x} ", .{ repr.exponent.unbias(), repr.mantissa });
        var m = big.Mutable.init(&limbs, 0);
        const r = m.setFloat(vv, .trunc);
        std.debug.print("{t} {d}\n", .{ r, m.toConst().toInt(i128) catch -1 });
    }
}
