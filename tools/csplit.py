#!/usr/bin/env python3
"""Split a huge Zig C-backend output file into several translation units.
usage: csplit.py in.c outdir nchunks
Every top-level item is classified; types/prototypes go to a shared header (statics made extern),
definitions are distributed over chunk files (statics made global)."""
import sys, re, os
src, outdir, nch = sys.argv[1], sys.argv[2], int(sys.argv[3])
os.makedirs(outdir, exist_ok=True)
data = open(src, encoding='latin-1').read()

def items(s):
    i, n, start, depth = 0, len(s), 0, 0
    while i < n:
        c = s[i]
        if c == '"' or c == "'":
            q = c; i += 1
            while i < n and s[i] != q:
                if s[i] == '\\': i += 1
                i += 1
            i += 1; continue
        if c == '/' and i + 1 < n and s[i+1] == '*':
            j = s.find('*/', i + 2); i = j + 2; continue
        if c == '/' and i + 1 < n and s[i+1] == '/':
            j = s.find('\n', i); i = j; continue
        if c == '#' and depth == 0 and (i == 0 or s[i-1] == '\n'):
            j = s.find('\n', i)
            while s[j-1] == '\\': j = s.find('\n', j + 1)
            yield s[start:j+1]; start = i = j + 1; continue
        if c in '{([': depth += 1
        elif c in '})]':
            depth -= 1
            if depth == 0 and c == '}':
                # function body ends at '}' followed by newline (no ';')
                k = i + 1
                while k < n and s[k] in ' \t': k += 1
                if k < n and s[k] == '\n':
                    seg = s[start:k+1]
                    if not seg.rstrip().endswith('};') and re.search(r'\)\s*(zig_\w+(\([^)]*\))?\s*)*\{', seg) and '=' not in seg.split('{',1)[0]:
                        yield seg; start = i = k + 1; continue
        elif c == ';' and depth == 0:
            k = s.find('\n', i); k = n - 1 if k < 0 else k
            yield s[start:k+1]; start = i = k + 1; continue
        i += 1
    if s[start:].strip(): yield s[start:]

STATIC = re.compile(r'^(\s*(?:zig_\w+\([^()]*\)\s*)*)static\s+')
header, defs, declared, defined = [], [], set(), set()
name_re = re.compile(r'([A-Za-z_]\w*)\s*(\[[^\]]*\]\s*)*$')
def obj_name(decl):
    d = re.sub(r'zig_\w+\([^()]*\)', '', decl).strip()
    m = name_re.search(d)
    return m.group(1) if m else None
for it in items(data):
    st = it.strip()
    if not st: continue
    if st.startswith('#') or st.startswith('typedef') or st.startswith('zig_static_assert') or re.match(r'^(struct|union|enum)\b[^=(]*\{', st) or re.match(r'^(struct|union|enum)\s+\w+\s*;$', st):
        header.append(it); continue
    has_body = st.endswith('}') and not st.endswith('};')
    if has_body:  # function definition
        d = STATIC.sub(r'\1', it, count=1); defs.append(d)
        sig = d.split('{', 1)[0].strip()
        header.append(sig + ';\n'); continue
    if '=' in st.split('(')[0] or (' = ' in st and not re.match(r'^[^=]*\)\s*;$', st)):
        lhs = st.split(' = ', 1)[0]
        nm = obj_name(STATIC.sub('', lhs))
        defs.append(STATIC.sub(r'\1', it, count=1))
        if nm: defined.add(nm); header.append('extern ' + STATIC.sub('', lhs) + ';\n')
        continue
    # declaration without initializer
    body = STATIC.sub('', st)
    if st.endswith(');') and '(' in st and not re.search(r'\(\s*\*', st.split('(')[0] + '('):
        # function prototype (zig_extern ones stay as they are)
        header.append(STATIC.sub(r'\1', it, count=1)); continue
    nm = obj_name(body[:-1])
    if nm: declared.add(nm)
    header.append('extern ' + body + '\n' if not body.startswith('extern') and not body.startswith('zig_extern') else it)
    defs.append(('TENT', nm, body))
# tentative definitions never given an initializer get a zero definition in chunk 0
tent = [b for (k, nm, b) in [d for d in defs if isinstance(d, tuple)] if nm not in defined]
defs = [d for d in defs if not isinstance(d, tuple)]
hdr = ''.join(header)
open(os.path.join(outdir, 'zig2.h'), 'w', encoding='latin-1').write(hdr)
total = sum(len(d) for d in defs); per = total // nch + 1
files, cur, size, idx = [], [], 0, 0
def flush():
    global cur, size, idx
    with open(os.path.join(outdir, f'zig2_{idx}.c'), 'w', encoding='latin-1') as f:
        f.write('#include "zig2.h"\n')
        if idx == 0: f.write(''.join(t + '\n' for t in tent))
        f.write(''.join(cur))
    idx += 1; cur = []; size = 0
for d in defs:
    cur.append(d); size += len(d)
    if size >= per and idx < nch - 1: flush()
flush()
print('header', len(hdr), 'defs', len(defs), 'tentative', len(tent), 'chunks', idx)
