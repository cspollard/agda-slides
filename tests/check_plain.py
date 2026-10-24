#!/usr/bin/env python3
"""Load a standalone-HTML deck in headless Chrome and check its navigation script ran.

usage: check_plain.py out/plain/index.html
"""
import os, re, subprocess, sys

chrome = os.environ.get(
    "CHROME", "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome")
path = os.path.abspath(sys.argv[1])
dom = subprocess.run(
    [chrome, "--headless=new", "--disable-gpu", "--no-sandbox",
     "--virtual-time-budget=3000", "--dump-dom", "file://" + path],
    capture_output=True, text=True, check=True).stdout
source = open(path).read()

failures = []
def check(name, ok):
    print(("ok   " if ok else "FAIL ") + name)
    if not ok:
        failures.append(name)

check("every slide is a section.slide",
      len(re.findall(r'<section class="slide', dom)) == len(re.findall(r'<section class="slide', source)))
check("navigation script ran: exactly one active slide",
      len(re.findall(r'class="slide[^"]*\bactive\b', dom)) == 1)
check("fragments preserved", dom.count('class="fragment') >= source.count('class="fragment'))
check("no unclosed-element nesting: slides are siblings",
      len(re.findall(r'<section class="slide', dom)) == len(re.findall(r'</section>', dom)))
sys.exit(1 if failures else 0)
