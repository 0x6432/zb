const std = @import("std");
pub fn main() void {
    var vv: f128 = 1.5; _ = &vv;
    const Repr = std.math.FloatRepr(f128);
    const repr: Repr = @bitCast(vv);
    const exponent = repr.exponent.unbias();
    const int_bit: Repr.Mantissa = 1 << (@bitSizeOf(Repr.Mantissa) - 1);
    const mantissa = int_bit | repr.mantissa;
    const sh = @bitSizeOf(Repr.Normalized.Fraction) - exponent;
    std.debug.print("{d} {x} {x} {d} {s}\n", .{ exponent, int_bit, mantissa, sh, @typeName(@TypeOf(mantissa)) });
    std.debug.print("{x} {d}\n", .{ mantissa >> @intCast(sh), std.math.big.int.calcLimbLen(mantissa >> @intCast(sh)) });
}
