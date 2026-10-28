#!/usr/bin/env python3
"""Park and unpark modules (a temporary move out of src/ to cut check time and agent reading).

  tests/park.py park 'why' Mod.A Mod.B ...   git mv src/Mod/A.agda park/Mod/A.agda, record in park/MANIFEST.md
  tests/park.py unpark                       move every parked module back, clear the manifest
  tests/park.py status                       list parked modules; exit 1 if any (the gate in `make test`)

A module can be parked only if no module still in src/ imports it (outside the set being parked),
so a parked module is a leaf: the proof-only `.Properties` modules, examples, and the like.
Parked modules are not checked; unpark before merging to main."""
import os, re, subprocess, sys
root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
src, park, manifest = (os.path.join(root, d) for d in ('src', 'park', 'park/MANIFEST.md'))
HEADER = '# Parked modules\n\nMoved out of `src/` by `tests/park.py`; restore with `make unpark`.\n\n'
def path(base, m): return os.path.join(base, m.replace('.', '/') + '.agda')
def parked():
    if not os.path.exists(manifest): return []
    return [l[2:].split(' | ')[0] for l in open(manifest).read().splitlines() if l.startswith('- ')]
def importers(m):
    out = []
    for d, _, fs in os.walk(src):
        for f in fs:
            if f.endswith('.agda'):
                p = os.path.join(d, f); me = os.path.relpath(p, src)[:-5].replace('/', '.')
                if re.search(r'^\s*(?:open\s+)?import\s+' + re.escape(m) + r'\b', open(p).read(), re.M): out.append(me)
    return out
def git(*a): subprocess.check_call(['git', '-C', root] + list(a))
cmd = sys.argv[1] if len(sys.argv) > 1 else 'status'
if cmd == 'status':
    ps = parked()
    for m in ps: print('parked:', m)
    if ps: print(f'{len(ps)} parked module(s): run `make unpark` before merging to main'); sys.exit(1)
elif cmd == 'park':
    why, mods = sys.argv[2], sys.argv[3:]
    bad = [(m, i) for m in mods for i in importers(m) if i not in mods]
    for m, i in bad: print(f'cannot park {m}: imported by {i}')
    missing = [m for m in mods if not os.path.exists(path(src, m))]
    for m in missing: print(f'no such module {m}')
    if bad or missing: sys.exit(1)
    os.makedirs(park, exist_ok=True)
    if not os.path.exists(manifest): open(manifest, 'w').write(HEADER)
    for m in mods:
        os.makedirs(os.path.dirname(path(park, m)), exist_ok=True)
        git('mv', path(src, m), path(park, m))
        open(manifest, 'a').write(f'- {m} | {why}\n')
elif cmd == 'unpark':
    for m in parked():
        if not os.path.exists(path(park, m)): continue
        os.makedirs(os.path.dirname(path(src, m)), exist_ok=True)
        git('mv', path(park, m), path(src, m))
    if os.path.exists(manifest): os.remove(manifest)
    for d, _, _ in sorted(os.walk(park), reverse=True):
        if not os.listdir(d): os.rmdir(d)
else: sys.exit('usage: park.py park WHY MOD... | unpark | status')
