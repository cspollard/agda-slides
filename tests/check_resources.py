#!/usr/bin/env python3
"""Check that the figure files a deck declares exist next to the rendered deck.

usage: check_resources.py <deck source .agda> <output directory>

Agda checks that a figure used in a deck is declared in its `Resources`; this
checks the other half, that every declared figure is a file on disk.  The
declared figures are the string literals in `figures = ... ∷ []`.
"""
import os, re, sys

source, outdir = sys.argv[1], sys.argv[2]
text = open(source).read()
m = re.search(r'figures\s*=\s*(.*?)(?:;|\n\s*[;}])', text, re.S)
names = re.findall(r'"([^"]+)"', m.group(1)) if m else []
missing = [n for n in names if not os.path.exists(os.path.join(outdir, n))]
for n in names:
    print(("ok   " if n not in missing else "MISSING ") + n)
sys.exit(1 if missing else 0)
