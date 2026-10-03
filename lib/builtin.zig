pub const OsTag = enum { freestanding, linux, macos, windows };
pub const Arch = enum { x86_64, aarch64 };
pub const Mode = enum { Debug, ReleaseSafe, ReleaseFast, ReleaseSmall };
pub const os = struct {
    pub const tag = OsTag.linux;
};
pub const cpu = struct {
    pub const arch = Arch.x86_64;
};
pub const mode = Mode.ReleaseFast;
pub const is_test = false;
pub const link_libc = true;
pub const single_threaded = true;
