#!/usr/bin/env python3
"""Fail if the import closure of any executable (*Main.agda) contains a `.Properties` module
(or a theory module such as Assembly), so executables never typecheck or compile proofs.
Usage: tests/check_closure.py [-v]"""
import re, sys, os, glob
root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
src = os.path.join(root, 'src')
def path(m): return os.path.join(src, m.replace('.', '/') + '.agda')
imps = {}
def get(m):
    if m not in imps:
        p = path(m)
        if not os.path.exists(p): imps[m] = None
        else:
            t = open(p).read()
            imps[m] = set(re.findall(r'^\s*(?:open\s+)?import\s+([A-Za-z0-9_.]+)', t, re.M))
    return imps[m]
def closure(m):
    seen, st, via = set(), [m], {m: None}
    while st:
        x = st.pop()
        if x in seen: continue
        i = get(x)
        if i is None: continue
        seen.add(x)
        for y in i:
            via.setdefault(y, x); st.append(y)
    return seen, via
bad = 0
for f in sorted(glob.glob(src + '/**/*Main.agda', recursive=True)):
    m = os.path.relpath(f, src)[:-5].replace('/', '.')
    c, via = closure(m)
    lines = sum(1 for x in c for _ in open(path(x)))
    print(f'{m}: {len(c)} modules, {lines} lines')
    for x in sorted(c):
        if re.search(r'\.Properties(\.|$)', x) or x.startswith('Slides.Anim.Assembly'):
            bad += 1; print(f'  ERROR: {x} (imported by {via[x]})')
sys.exit(1 if bad else 0)
