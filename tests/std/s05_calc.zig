const std = @import("std");
const Token = union(enum) { num: f64, op: u8, lparen, rparen };
fn tokenize(gpa: std.mem.Allocator, src: []const u8) !std.ArrayList(Token) {
    var list: std.ArrayList(Token) = .empty;
    var i: usize = 0;
    while (i < src.len) {
        const c = src[i];
        switch (c) {
            ' ' => i += 1,
            '0'...'9', '.' => {
                const start = i;
                while (i < src.len and (std.ascii.isDigit(src[i]) or src[i] == '.')) i += 1;
                try list.append(gpa, .{ .num = try std.fmt.parseFloat(f64, src[start..i]) });
            },
            '(' => { try list.append(gpa, .lparen); i += 1; },
            ')' => { try list.append(gpa, .rparen); i += 1; },
            else => { try list.append(gpa, .{ .op = c }); i += 1; },
        }
    }
    return list;
}
const Parser = struct {
    toks: []const Token,
    pos: usize = 0,
    fn peek(p: *Parser) ?Token { return if (p.pos < p.toks.len) p.toks[p.pos] else null; }
    fn expr(p: *Parser) f64 {
        var v = p.term();
        while (p.peek()) |t| switch (t) {
            .op => |o| if (o == '+' or o == '-') { p.pos += 1; const r = p.term(); v = if (o == '+') v + r else v - r; } else break,
            else => break,
        };
        return v;
    }
    fn term(p: *Parser) f64 {
        var v = p.atom();
        while (p.peek()) |t| switch (t) {
            .op => |o| if (o == '*' or o == '/') { p.pos += 1; const r = p.atom(); v = if (o == '*') v * r else v / r; } else break,
            else => break,
        };
        return v;
    }
    fn atom(p: *Parser) f64 {
        const t = p.peek().?; p.pos += 1;
        return switch (t) {
            .num => |n| n,
            .lparen => blk: { const v = p.expr(); p.pos += 1; break :blk v; },
            .op => |o| if (o == '-') -p.atom() else unreachable,
            .rparen => unreachable,
        };
    }
};
pub fn main() !void {
    var gpa_state: std.heap.DebugAllocator(.{}) = .init;
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();
    const exprs = [_][]const u8{ "1 + 2 * 3", "(1.5 + 2.5) * -4", "10 / 4 - 0.5", "2 * (3 + (4 - 1)) / 3" };
    for (exprs) |e| {
        var toks = try tokenize(gpa, e);
        defer toks.deinit(gpa);
        var p = Parser{ .toks = toks.items };
        std.debug.print("{s} = {d}\n", .{ e, p.expr() });
    }
    var words = std.StringHashMap(usize).init(gpa);
    defer words.deinit();
    var it = std.mem.tokenizeScalar(u8, "the quick brown fox jumps over the lazy dog the end", ' ');
    while (it.next()) |w| {
        const gop = try words.getOrPut(w);
        if (gop.found_existing) gop.value_ptr.* += 1 else gop.value_ptr.* = 1;
    }
    std.debug.print("the={d} fox={d} count={d}\n", .{ words.get("the").?, words.get("fox").?, words.count() });
    const up = try std.ascii.allocUpperString(gpa, "hello");
    defer gpa.free(up);
    std.debug.print("{s} {s}\n", .{ up, std.mem.trim(u8, "  pad  ", " ") });
}
