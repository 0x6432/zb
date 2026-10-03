//! File-as-struct with top-level fields.
const Counter = @This();
count: u32 = 0,
step: u32,
pub fn init(step: u32) Counter {
    return .{ .step = step };
}
pub fn tick(self: *Counter) void {
    self.count += self.step;
}
