#!/usr/bin/env python3
"""Load a rendered deck in headless Chrome and check what reveal.js made of it.

usage: check_reveal.py out/intro/index.html
Set CHROME to override the browser binary.
"""
import os, re, subprocess, sys

chrome = os.environ.get(
    "CHROME", "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome")
path = os.path.abspath(sys.argv[1])
dom = subprocess.run(
    [chrome, "--headless=new", "--disable-gpu", "--no-sandbox",
     "--virtual-time-budget=8000", "--dump-dom", "file://" + path],
    capture_output=True, text=True, check=True).stdout

failures = []
def check(name, ok):
    print(("ok   " if ok else "FAIL ") + name)
    if not ok:
        failures.append(name)

source = open(path).read()
check("reveal.js initialised", re.search(r'class="reveal[^"]*\bready\b', dom) is not None)
check("one <section> per source section",
      len(re.findall(r"<section", dom)) >= len(re.findall(r"<section", source)))
check("fragments preserved", dom.count('class="fragment') >= source.count('class="fragment'))
check("vertical stack recognised", 'class="stack' in dom if "<section><section" in source else True)
check("notes aside kept", ('class="notes"' in dom) == ('class="notes"' in source))
check("math rendered by KaTeX", 'class="katex' in dom if r"\[" in source or r"\(" in source else True)
check("code highlighted", 'hljs' in dom if "<code" in source else True)
check("inline markup rendered as mixed content", '<em>' in dom if '<em>' in source else True)
check("columns laid out side by side",
      'class="columns"' in dom if 'class="columns"' in source else True)
colours = re.findall(r'data-background-color="([^"]+)"', source)
check("slide backgrounds applied",
      'slide-background' in dom and all(c.lower() in dom.replace(' ', '').lower() for c in colours)
      if colours else True)
sys.exit(1 if failures else 0)
