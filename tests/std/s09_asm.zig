const std = @import("std");
fn xcr0() u32 {
    return asm volatile (
        \\ xor %%ecx, %%ecx
        \\ xgetbv
        : [_] "={eax}" (-> u32),
        :
        : .{ .edx = true, .ecx = true });
}
fn add(a: u64, b: u64) u64 {
    return asm ("leaq (%[a],%[b]), %[r]" : [r] "=r" (-> u64) : [a] "r" (a), [b] "r" (b));
}
fn swap(a: *u32, b: *u32) void {
    asm volatile ("xchgl %[x], %[y]" : [x] "+r" (a.*), [y] "+r" (b.*));
}
fn rdi(x: u64) u64 {
    return asm ("movq %%rdi, %%rax\n shlq $1, %%rax" : [_] "={rax}" (-> u64) : [_] "{rdi}" (x), [_] "{rsi}" (@as(u64, 7)));
}
pub fn main() void {
    var p: u32 = 1; var q: u32 = 2; swap(&p, &q);
    std.debug.print("{} {} {} {} {}\n", .{ xcr0() & 1, add(40, 2), p, q, rdi(21) });
    std.atomic.spinLoopHint();
}
