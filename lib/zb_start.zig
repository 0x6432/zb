//! Entry glue used with the real Zig std (--std-dir) when `main` takes
//! `std.process.Init` / `std.process.Init.Minimal` (mirrors std/start.zig callMain).
const std = @import("std");
const root = @import("root");

pub fn zbMain(argc: usize, argv: [*][*:0]u8, envp: [*:null]?[*:0]u8) u8 {
    var envc: usize = 0;
    while (envp[envc] != null) envc += 1;
    const env_block: std.process.Environ.Block = .{ .slice = envp[0..envc :null] };
    const args = argv[0..argc];
    const fn_info = @typeInfo(@TypeOf(root.main)).@"fn";
    if (fn_info.params[0].type.? == std.process.Init.Minimal) return wrapMain(root.main(.{
        .args = .{ .vector = args },
        .environ = .{ .block = env_block },
    }));

    const gpa = std.heap.c_allocator;
    var arena_allocator = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena_allocator.deinit();

    var threaded: std.Io.Threaded = .init(gpa, .{
        .argv0 = .init(.{ .vector = args }),
        .environ = .{ .block = env_block },
    });
    defer threaded.deinit();

    var environ_map = std.process.Environ.createMap(.{ .block = env_block }, gpa) catch |err|
        std.process.fatal("failed to parse environment variables: {t}", .{err});
    defer environ_map.deinit();

    const preopens = std.process.Preopens.init(arena_allocator.allocator()) catch |err|
        std.process.fatal("failed to init preopens: {t}", .{err});

    return wrapMain(root.main(.{
        .minimal = .{
            .args = .{ .vector = args },
            .environ = .{ .block = env_block },
        },
        .arena = &arena_allocator,
        .gpa = gpa,
        .io = threaded.io(),
        .environ_map = &environ_map,
        .preopens = preopens,
    }));
}

inline fn wrapMain(result: anytype) u8 {
    const ReturnType = @TypeOf(result);
    switch (ReturnType) {
        void => return 0,
        noreturn => unreachable,
        u8 => return result,
        else => {},
    }
    const unwrapped_result = result catch |err| {
        std.log.err("{t}", .{err});
        return 1;
    };
    return switch (@TypeOf(unwrapped_result)) {
        void => 0,
        u8 => unwrapped_result,
        else => unreachable,
    };
}
