const std = @import("std");
const w = std.io;
const Counter = @import("util/Counter.zig");

pub const Token = struct {
    tag: Tag,
    start: usize,
    end: usize,
    pub const Tag = enum { identifier, number, plus, minus, star, l_paren, r_paren, eof, invalid };
};

pub const Tokenizer = struct {
    buffer: [:0]const u8,
    index: usize,

    const State = enum { start, identifier, number };

    pub fn init(buffer: [:0]const u8) Tokenizer {
        return .{ .buffer = buffer, .index = 0 };
    }

    pub fn next(self: *Tokenizer) Token {
        var result: Token = .{ .tag = undefined, .start = self.index, .end = undefined };
        state: switch (State.start) {
            .start => switch (self.buffer[self.index]) {
                0 => {
                    result.tag = .eof;
                },
                ' ', '\n', '\t' => {
                    self.index += 1;
                    result.start = self.index;
                    continue :state .start;
                },
                'a'...'z', 'A'...'Z', '_' => {
                    result.tag = .identifier;
                    continue :state .identifier;
                },
                '0'...'9' => {
                    result.tag = .number;
                    continue :state .number;
                },
                '+' => {
                    self.index += 1;
                    result.tag = .plus;
                },
                '-' => {
                    self.index += 1;
                    result.tag = .minus;
                },
                '*' => {
                    self.index += 1;
                    result.tag = .star;
                },
                '(' => {
                    self.index += 1;
                    result.tag = .l_paren;
                },
                ')' => {
                    self.index += 1;
                    result.tag = .r_paren;
                },
                else => {
                    self.index += 1;
                    result.tag = .invalid;
                },
            },
            .identifier => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    'a'...'z', 'A'...'Z', '_', '0'...'9' => continue :state .identifier,
                    else => {},
                }
            },
            .number => {
                self.index += 1;
                switch (self.buffer[self.index]) {
                    '0'...'9' => continue :state .number,
                    else => {},
                }
            },
        }
        result.end = self.index;
        return result;
    }
};

const EvalError = error{UnexpectedToken} || error{DivByZero};

const Parser = struct {
    tokens: []const Token,
    src: []const u8,
    pos: usize = 0,

    fn peek(p: *Parser) Token.Tag {
        return p.tokens[p.pos].tag;
    }
    fn expr(p: *Parser) EvalError!i64 {
        var v = try p.term();
        while (true) {
            switch (p.peek()) {
                .plus => {
                    p.pos += 1;
                    v += try p.term();
                },
                .minus => {
                    p.pos += 1;
                    v -= try p.term();
                },
                else => return v,
            }
        }
    }
    fn term(p: *Parser) EvalError!i64 {
        var v = try p.atom();
        while (p.peek() == .star) {
            p.pos += 1;
            v *= try p.atom();
        }
        return v;
    }
    fn atom(p: *Parser) EvalError!i64 {
        const t = p.tokens[p.pos];
        p.pos += 1;
        switch (t.tag) {
            .number => {
                var n: i64 = 0;
                for (p.src[t.start..t.end]) |c| n = n * 10 + (c - '0');
                return n;
            },
            .l_paren => {
                const v = try p.expr();
                if (p.peek() != .r_paren) return error.UnexpectedToken;
                p.pos += 1;
                return v;
            },
            .minus => return -(try p.atom()),
            else => return error.UnexpectedToken,
        }
    }
};

fn eval(src: [:0]const u8) EvalError!i64 {
    var toks = std.ArrayList(Token){};
    defer toks.deinit();
    var tz = Tokenizer.init(src);
    while (true) {
        const t = tz.next();
        toks.append(t) catch unreachable;
        if (t.tag == .eof) break;
    }
    var p = Parser{ .tokens = toks.items, .src = src };
    return p.expr();
}

pub fn main() !void {
    var tz = Tokenizer.init("foo + 42*(bar_1 - 7) $");
    var c = Counter.init(2);
    while (true) {
        const t = tz.next();
        if (t.tag == .eof) break;
        c.tick();
        w.writeAll(1, @tagName(t.tag));
        w.writeAll(1, ":");
        w.writeAll(1, tz.buffer[t.start..t.end]);
        w.writeAll(1, " ");
    }
    w.writeAll(1, "\n");
    w.writeInt(1, c.count);
    w.writeAll(1, "\n");
    w.writeInt(1, try eval("1 + 2 * (3 + 4) - -5"));
    w.writeAll(1, "\n");
    const bad = eval("(1 + 2");
    if (bad) |_| {} else |e| {
        w.writeAll(1, @errorName(e));
        w.writeAll(1, "\n");
    }
}
