#!/usr/bin/env python3
"""plain.js keeps its key table in the asset (a byte-exact golden); `plainKinds`
(src/Slides/Backend/Plain/Supports.agda) is its checked description.  Extract both tables
(key name -> command) and fail if they differ.  Deterministic, no browser.
usage: tests/check_plain_keys.py"""
import os, re, sys
root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
js = open(os.path.join(root, 'assets/plain.js')).read()
ag = open(os.path.join(root, 'src/Slides/Backend/Plain/Supports.agda')).read()

# plain.js: `if (e.key === 'A' || e.key === 'B') cmd;` in the keydown handler
handler = js[js.index("addEventListener('keydown'"):]
calls = {'next()': 'next', 'prev()': 'prev', 'show(0, false)': 'first', 'show(slides.length - 1, true)': 'last'}
def agda_name(k): return 'space' if k == ' ' else k[0].lower() + k[1:]
table_js = {}
for m in re.finditer(r"if \(((?:e\.key === '[^']*'(?: \|\| )?)+)\) ([^;]+);", handler):
    cmd = calls[m.group(2)]
    for k in re.findall(r"e\.key === '([^']*)'", m.group(1)):
        table_js[agda_name(k)] = cmd

# plainKinds: `on _≟K_ (a ∷ b ∷ []) (nav cmd)`
kinds = ag[ag.index('plainKinds :'):ag.index('plainKeys :')]
table_ag = {}
for m in re.finditer(r"on _≟K_ \(([^)]*)\) \(nav (\w+)\)", kinds):
    for k in re.findall(r"\w+", m.group(1).replace('∷', ' ')):
        table_ag[k] = m.group(2)

ok = table_js == table_ag and len(table_js) > 0
print(('ok   ' if ok else 'FAIL ') + f'plain.js key table matches plainKinds ({len(table_js)} keys)')
if not ok:
    for k in sorted(set(table_js) | set(table_ag)):
        if table_js.get(k) != table_ag.get(k):
            print(f'  {k}: plain.js {table_js.get(k)}, plainKinds {table_ag.get(k)}')
sys.exit(0 if ok else 1)
