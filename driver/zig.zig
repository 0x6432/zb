//! `zig` drop-in driver for zb (Zig 0.17.0, x86_64-linux). libc only, compiled by zb.
//! Commands: version, env, build-exe, build-obj, build-lib, run, build/fetch/init (via lib/compiler/Maker.zig).
//! Supports the compiler server protocol subset used by the build system (--listen=-).
extern var @"zb.argc": c_int;
extern var @"zb.argv": [*][*:0]u8;
extern fn malloc(n: usize) ?[*]u8;
extern fn realloc(p: ?[*]u8, n: usize) ?[*]u8;
extern fn getenv(name: [*:0]const u8) ?[*:0]u8;
extern fn system(cmd: [*:0]const u8) c_int;
extern fn realpath(p: [*:0]const u8, out: ?[*]u8) ?[*:0]u8;
extern fn access(p: [*:0]const u8, mode: c_int) c_int;
extern fn read(fd: c_int, buf: [*]u8, n: usize) isize;
extern fn write(fd: c_int, buf: [*]const u8, n: usize) isize;
extern fn execv(path: [*:0]const u8, argv: [*]const ?[*:0]const u8) c_int;
extern fn exit(code: c_int) noreturn;
extern fn getpid() c_int;
extern fn getcwd(buf: ?[*]u8, n: usize) ?[*:0]u8;

const Str = []const u8;

fn len0(s: [*:0]const u8) usize { var n: usize = 0; while (s[n] != 0) n += 1; return n; }
fn span(s: [*:0]const u8) Str { return s[0..len0(s)]; }
fn eql(a: Str, b: Str) bool { if (a.len != b.len) return false; for (a, 0..) |c, i| if (c != b[i]) return false; return true; }
fn starts(a: Str, p: Str) bool { return a.len >= p.len and eql(a[0..p.len], p); }
fn ends(a: Str, p: Str) bool { return a.len >= p.len and eql(a[a.len - p.len ..], p); }
fn indexOf(a: Str, c: u8) ?usize { for (a, 0..) |x, i| if (x == c) return i; return null; }
fn lastIndexOf(a: Str, c: u8) ?usize { var i = a.len; while (i > 0) { i -= 1; if (a[i] == c) return i; } return null; }

const Buf = struct {
    p: [*]u8 = undefined, n: usize = 0, cap: usize = 0,
    fn add(b: *Buf, s: Str) void {
        if (b.n + s.len + 1 > b.cap) { b.cap = (b.n + s.len + 1) * 2 + 64; b.p = realloc(if (b.n == 0 and b.cap != 0 and b.n == 0) null else b.p, b.cap).?; }
        for (s, 0..) |c, i| b.p[b.n + i] = c;
        b.n += s.len; b.p[b.n] = 0;
    }
    fn addc(b: *Buf, c: u8) void { const one = [1]u8{c}; b.add(&one); }
    fn q(b: *Buf, s: Str) void { // shell-quoted argument
        b.addc(' '); b.addc('\'');
        for (s) |c| { if (c == '\'') b.add("'\\''") else b.addc(c); }
        b.addc('\'');
    }
    fn str(b: *Buf) [:0]const u8 { if (b.cap == 0) b.add(""); return b.p[0..b.n :0]; }
};
fn cat(parts: []const Str) [:0]const u8 { var b: Buf = .{}; for (parts) |p| b.add(p); return b.str(); }

fn err(msg: Str) void { _ = write(2, msg.ptr, msg.len); }
fn out(msg: Str) void { _ = write(1, msg.ptr, msg.len); }
fn fatal(parts: []const Str) noreturn { err("error: "); for (parts) |p| err(p); err("\n"); exit(1); }
fn exists(p: [:0]const u8) bool { return access(p.ptr, 0) == 0; }
fn sh(cmd: [:0]const u8) bool {
    if (getenv("ZB_VERBOSE") != null) { err(cmd); err("\n"); }
    return system(cmd.ptr) == 0;
}
fn hex(v: u128, n: usize) Str {
    const d = "0123456789abcdef"; const p = malloc(n + 1).?; var x = v; var i = n;
    while (i > 0) { i -= 1; p[i] = d[@as(usize, @intCast(x & 15))]; x >>= 4; }
    return p[0..n];
}
fn dirname(p: Str) Str { return if (lastIndexOf(p, '/')) |i| (if (i == 0) "/" else p[0..i]) else "."; }
fn basename(p: Str) Str { return if (lastIndexOf(p, '/')) |i| p[i + 1 ..] else p; }
fn stem(p: Str) Str { const b = basename(p); return if (lastIndexOf(b, '.')) |i| b[0..i] else b; }
fn abs(p: Str) Str { const z = cat(&.{p}); if (realpath(z.ptr, null)) |r| return span(r); return p; }

var zb_home: Str = "";
var self_exe: Str = "";
var lib_dir: Str = "";
var global_cache: Str = "";

fn initPaths() void {
    self_exe = if (realpath("/proc/self/exe", null)) |r| span(r) else span(@"zb.argv"[0]);
    zb_home = if (getenv("ZB_HOME")) |h| span(h) else dirname(dirname(self_exe));
    lib_dir = if (getenv("ZB_ZIG_LIB")) |l| span(l) else abs(cat(&.{ zb_home, "/zig-0.17.0/lib" }));
    global_cache = if (getenv("ZIG_GLOBAL_CACHE_DIR")) |g| span(g) else if (getenv("HOME")) |h| cat(&.{ span(h), "/.cache/zb-zig" }) else "/tmp/zb-zig-cache";
}

const Kind = enum { exe, obj, lib };
const Opts = struct {
    kind: Kind = .exe,
    root: ?Str = null,
    name: ?Str = null,
    emit: ?Str = null,
    no_emit: bool = false,
    listen: bool = false,
    dynamic: bool = false,
    single_threaded: bool = false,
    libc: bool = false,
    cache_dir: ?Str = null,
    mods: Buf = .{}, // zb -M args
    link: Buf = .{}, // cc link inputs/flags
    cflags: Buf = .{},
    csrc: Buf = .{},
    run_args: Buf = .{},
    hash: u128 = 0x6c62272e07bb014262b821756295c58d,
};
fn mix(o: *Opts, s: Str) void { for (s) |c| { o.hash ^= c; o.hash *%= 0x0000000001000000000000000000013B; } o.hash ^= 0xff; o.hash *%= 0x0000000001000000000000000000013B; }

const takes_value = [_]Str{ "--name", "-target", "-mcpu", "--cache-dir", "--global-cache-dir", "--zig-lib-dir", "--build-root", "--dep", "--libc", "-I", "-L", "-z", "--sysroot", "-rpath", "--version", "--stack", "--entry", "-isystem", "--color", "-T", "--script", "--debug-log", "-O", "--subsystem", "-idirafter", "-iframework", "-F", "--mod", "-x", "--test-filter", "--test-name-prefix", "--test-runner", "-framework", "-weak_framework", "--image-base", "-install_name", "--compress-debug-sections", "-fsoname", "--error-limit", "-mexec-model", "--debug-rt", "--zig-lib", "-ofmt", "-mcmodel" };

fn parse(o: *Opts, args: []const Str) void {
    var i: usize = 0;
    var first_mod = true;
    while (i < args.len) : (i += 1) {
        const a = args[i];
        mix(o, a);
        if (eql(a, "--")) { i += 1; while (i < args.len) : (i += 1) o.run_args.q(args[i]); break; }
        if (eql(a, "-cflags")) { i += 1; while (i < args.len and !eql(args[i], "--")) : (i += 1) o.cflags.q(args[i]); continue; }
        if (starts(a, "-femit-bin=")) { o.emit = a[11..]; continue; }
        if (eql(a, "-fno-emit-bin")) { o.no_emit = true; continue; }
        if (eql(a, "--listen=-")) { o.listen = true; continue; }
        if (eql(a, "-fsingle-threaded")) { o.single_threaded = true; continue; }
        if (eql(a, "-fno-single-threaded")) { o.single_threaded = false; continue; }
        if (eql(a, "-dynamic")) { o.dynamic = true; continue; }
        if (eql(a, "-static")) { o.dynamic = false; continue; }
        if (eql(a, "--name")) { i += 1; o.name = args[i]; mix(o, args[i]); continue; }
        if (eql(a, "--cache-dir")) { i += 1; o.cache_dir = args[i]; continue; }
        if (eql(a, "--zig-lib-dir")) { i += 1; lib_dir = abs(args[i]); continue; }
        if (eql(a, "--global-cache-dir")) { i += 1; global_cache = args[i]; continue; }
        if (starts(a, "-M")) {
            const eq = indexOf(a, '=') orelse { first_mod = false; continue; };
            if (first_mod and o.root == null) { o.root = a[eq + 1 ..]; if (o.name == null and !eql(a[2..eq], "root")) o.name = a[2..eq]; } else o.mods.q(a);
            first_mod = false; continue;
        }
        if (eql(a, "-lc")) { o.libc = true; continue; }
        if (eql(a, "-lm")) continue;
        if (starts(a, "-l") or starts(a, "-L")) { o.link.q(a); if (a.len == 2 and i + 1 < args.len) { i += 1; o.link.q(args[i]); } continue; }
        if (eql(a, "-I") or eql(a, "-isystem")) { o.cflags.q(a); i += 1; o.cflags.q(args[i]); continue; }
        if (starts(a, "-I") or starts(a, "-D")) { o.cflags.q(a); continue; }
        var tv = false; for (takes_value) |t| if (eql(a, t)) { tv = true; }
        if (tv) { i += 1; if (i < args.len) mix(o, args[i]); continue; }
        if (a.len > 0 and a[0] == '-') continue; // other flags: ignored
        if (ends(a, ".zig")) { if (o.root == null) o.root = a else o.mods.q(cat(&.{ "-M", stem(a), "=", a })); continue; }
        if (ends(a, ".c") or ends(a, ".S") or ends(a, ".s")) { o.csrc.q(a); continue; }
        o.link.q(a); // .o .a .so and anything else goes to the linker
    }
}

fn outName(o: *const Opts) Str {
    const n = o.name orelse (if (o.root) |r| stem(r) else "a");
    return switch (o.kind) {
        .exe => n,
        .obj => cat(&.{ n, ".o" }),
        .lib => cat(&.{ "lib", n, if (o.dynamic) ".so" else ".a" }),
    };
}

/// zb -> qbe -> cc. Returns false on failure (diagnostics already on stderr).
fn compile(o: *Opts, dest0: Str) bool {
    const dest = if (dest0.len > 0 and dest0[0] == '/') dest0 else cat(&.{ span(getcwd(null, 0).?), "/", dest0 });
    const tmp = cat(&.{ global_cache, "/tmp/", hex(o.hash, 32), "-", hex(@intCast(getpid()), 8) });
    if (!sh(cat(&.{ "mkdir -p '", tmp, "' '", dirname(dest), "'" }))) return false;
    const ssa = cat(&.{ tmp, "/out.ssa" });
    const qbe = if (getenv("QBE")) |q| span(q) else cat(&.{ zb_home, "/qbe-1.2/qbe" });
    var c: Buf = .{};
    if (o.root) |root| {
        c.q(cat(&.{ zb_home, "/zb" })); c.q(root); c.add(" --std-dir"); c.q(cat(&.{ lib_dir, "/std" }));
        c.add(o.mods.str()); if (!o.single_threaded) c.add(" -fno-single-threaded"); if (!o.libc) c.add(" -fno-libc"); c.add(" -o"); c.q(ssa);
        c.add(" 2>"); c.q(cat(&.{ tmp, "/zb.log" }));
        if (!sh(c.str())) { _ = sh(cat(&.{ "grep -v 'note:' '", tmp, "/zb.log' >&2" })); return false; }
        c = .{}; c.q(qbe); c.add(" -o"); c.q(cat(&.{ tmp, "/out.s" })); c.q(ssa);
        if (!sh(c.str())) return false;
    }
    const pic = if (o.kind == .lib and o.dynamic) " -fPIC" else "";
    var objs: Buf = .{};
    // compile assembly + runtime + C sources to objects
    c = .{}; c.add("cd"); c.q(tmp); c.add(" && cc -c -w -O1"); c.add(pic); c.add(o.cflags.str());
    if (o.root != null) { c.q(cat(&.{ tmp, "/out.s" })); c.q(cat(&.{ ssa, ".asm.s" })); }
    c.q(cat(&.{ zb_home, "/tools/zbrt.c" })); c.add(o.csrc.str()); c.add(" 2>&1 | grep -v 'Warning\\|Assembler messages' >&2; exit 0");
    if (!sh(c.str())) return false;
    if (o.root != null) { objs.q(cat(&.{ tmp, "/out.o" })); objs.q(cat(&.{ tmp, "/out.ssa.asm.o" })); }
    objs.q(cat(&.{ tmp, "/zbrt.o" }));
    { // C objects: basename.o in tmp
        var it: Buf = .{}; it.add("cd"); it.q(tmp); it.add(" && ls *.o >/dev/null"); if (!sh(it.str())) return false; }
    c = .{}; c.add("cd"); c.q(tmp); c.add(" && ");
    switch (o.kind) {
        .exe => { c.add("cc -o"); c.q(dest); c.add(" *.o"); c.add(o.link.str()); c.add(" -lm -lpthread -Wl,-z,stack-size=0x10000000"); },
        .obj => { c.add("ld -r -o"); c.q(dest); c.add(" *.o"); },
        .lib => if (o.dynamic) { c.add("cc -shared -o"); c.q(dest); c.add(" *.o"); c.add(o.link.str()); c.add(" -lm"); } else { c.add("rm -f"); c.q(dest); c.add(" && ar rcs"); c.q(dest); c.add(" *.o"); },
    }
    const ok = sh(c.str());
    if (getenv("ZB_KEEP_TMP") == null) _ = sh(cat(&.{ "rm -rf '", tmp, "'" }));
    return ok;
}

fn le32(b: *[4]u8, v: u32) void { b[0] = @truncate(v); b[1] = @truncate(v >> 8); b[2] = @truncate(v >> 16); b[3] = @truncate(v >> 24); }
fn sendMsg(tag: u32, body: Str) void {
    var h: [8]u8 = undefined; le32(h[0..4], tag); le32(h[4..8], @intCast(body.len));
    _ = write(1, &h, 8); if (body.len > 0) _ = write(1, body.ptr, body.len);
}
fn readAll(buf: [*]u8, n: usize) bool { var got: usize = 0; while (got < n) { const r = read(0, buf + got, n - got); if (r <= 0) return false; got += @intCast(r); } return true; }

fn serve(o: *Opts) noreturn {
    sendMsg(0, "0.17.0"); // zig_version
    while (true) {
        var h: [8]u8 = undefined;
        if (!readAll(&h, 8)) exit(0);
        const tag = @as(u32, h[0]) | @as(u32, h[1]) << 8 | @as(u32, h[2]) << 16 | @as(u32, h[3]) << 24;
        const blen = @as(u32, h[4]) | @as(u32, h[5]) << 8 | @as(u32, h[6]) << 16 | @as(u32, h[7]) << 24;
        if (blen > 0) { const tmp = malloc(blen).?; if (!readAll(tmp, blen)) exit(0); }
        switch (tag) {
            0 => exit(0), // exit
            1 => { // update
                const cache = o.cache_dir orelse cat(&.{ global_cache, "/local" });
                const digest = o.hash;
                const dest = cat(&.{ cache, "/o/", hex(digest, 32), "/", outName(o) });
                if (!o.no_emit and !compile(o, dest)) exit(1);
                var body: [17]u8 = undefined; body[0] = 0; // flags: cache_hit = false
                // hex(digest) prints most-significant nibble first; emit digest bytes in that order
                for (0..16) |k| body[1 + k] = @truncate(digest >> @intCast(8 * (15 - k)));
                sendMsg(2, &body); // emit_digest
            },
            else => {},
        }
    }
}

fn buildCmd(kind: Kind, args: []const Str) noreturn {
    var o: Opts = .{ .kind = kind }; parse(&o, args);
    if (o.listen) serve(&o);
    if (o.no_emit) exit(0);
    const dest = o.emit orelse outName(&o);
    exit(if (compile(&o, dest)) 0 else 1);
}

fn runCmd(args: []const Str) noreturn {
    var o: Opts = .{ .kind = .exe }; parse(&o, args);
    const dest = cat(&.{ global_cache, "/run/", hex(o.hash, 32), "/", outName(&o) });
    if (!compile(&o, dest)) exit(1);
    var c: Buf = .{}; c.add("exec"); c.q(dest); c.add(o.run_args.str());
    const r = system(c.str().ptr);
    exit(if (r == 0) 0 else if ((r & 0x7f) == 0) @intCast((r >> 8) & 0xff) else 1);
}

fn makerCmd(cmd: Str, args: []const Str) noreturn {
    const maker = cat(&.{ global_cache, "/zb/maker" });
    if (!exists(maker) or getenv("ZB_REBUILD_MAKER") != null) {
        err("Compiling maker with zb (first time setup)...\n");
        var o: Opts = .{ .kind = .exe };
        o.root = cat(&.{ lib_dir, "/compiler/Maker.zig" });
        if (!compile(&o, maker)) fatal(&.{"failed to compile lib/compiler/Maker.zig"});
    }
    const argv = @as([*]?[*:0]const u8, @ptrCast(@alignCast(malloc(8 * (args.len + 8)).?)));
    var n: usize = 0;
    argv[n] = maker.ptr; n += 1;
    argv[n] = cat(&.{cmd}).ptr; n += 1;
    argv[n] = cat(&.{ "--zig-lib=", lib_dir }).ptr; n += 1;
    argv[n] = cat(&.{ "--zig=", self_exe }).ptr; n += 1;
    argv[n] = cat(&.{ "--global-cache=", global_cache }).ptr; n += 1;
    argv[n] = cat(&.{ "--seed=0x", hex(@intCast(getpid()), 8) }).ptr; n += 1;
    for (args) |a| { argv[n] = cat(&.{a}).ptr; n += 1; }
    argv[n] = null;
    _ = execv(maker.ptr, argv);
    fatal(&.{ "cannot exec ", maker });
}

const usage =
    \\Usage: zig [command] [options]   (zb driver, Zig 0.17.0, x86_64-linux)
    \\  build-exe / build-obj / build-lib   compile with zb -> QBE -> cc
    \\  run file.zig [-- args]             build and run
    \\  build / fetch / init               Zig build system (lib/compiler/Maker.zig, compiled by zb)
    \\  version / env
    \\
;

pub fn main() u8 {
    initPaths();
    const argc: usize = @intCast(@"zb.argc");
    const args = @as([*]Str, @ptrCast(@alignCast(malloc(16 * (argc + 1)).?)))[0..argc];
    for (0..argc) |i| args[i] = span(@"zb.argv"[i]);
    if (argc < 2) { err(usage); return 1; }
    const cmd = args[1];
    const rest = args[2..];
    if (eql(cmd, "version")) { out("0.17.0\n"); return 0; }
    if (eql(cmd, "env")) {
        out(cat(&.{ "{\n  \"zig_exe\": \"", self_exe, "\",\n  \"lib_dir\": \"", lib_dir, "\",\n  \"std_dir\": \"", lib_dir, "/std\",\n  \"global_cache_dir\": \"", global_cache, "\",\n  \"version\": \"0.17.0\",\n  \"target\": \"x86_64-linux-gnu\"\n}\n" }));
        return 0;
    }
    if (eql(cmd, "build-exe")) buildCmd(.exe, rest);
    if (eql(cmd, "build-obj")) buildCmd(.obj, rest);
    if (eql(cmd, "build-lib")) buildCmd(.lib, rest);
    if (eql(cmd, "run")) runCmd(rest);
    if (eql(cmd, "build") or eql(cmd, "fetch") or eql(cmd, "init")) makerCmd(cmd, rest);
    if (eql(cmd, "help") or eql(cmd, "--help") or eql(cmd, "-h")) { out(usage); return 0; }
    fatal(&.{ "unknown command: ", cmd });
}
