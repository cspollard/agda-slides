// Checks the page evaluator against Agda: for every animation of the `animref` deck and every
// quarter tick of its duration, the drawing commands the page produces from the shipped events
// (`a._show(t)`) must be those Agda computed from the exact semantics (`refs.json`): the same
// tags, and numbers equal to within 1e-3 (the page works in floating point).
//
// usage: node tests/browser/anim-ref.mjs [outdir]   (default: ../../out, deck `animref`)
import { chromium } from 'playwright-core';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const out = path.resolve(process.argv[2] ?? path.join(here, '..', '..', 'out'));
const chrome = process.env.CHROME ?? '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
let failures = 0;
const check = (n, ok, d = '') => { console.log(`${ok ? 'ok  ' : 'FAIL'} ${n}${ok ? '' : `  (${d})`}`); if (!ok) failures++; };

const refs = JSON.parse(fs.readFileSync(path.join(out, 'animref', 'refs.json'), 'utf8'));
const rat = x => (typeof x === 'number' ? x : x[0] / x[1]);
const browser = await chromium.launch({ executablePath: chrome, headless: true });
const page = await browser.newPage();
const errors = [];
page.on('pageerror', e => errors.push(e.message));
await page.goto(pathToFileURL(path.join(out, 'animref', 'index.html')).href);
await page.waitForTimeout(300);

// the numbers of an element, in the order of Agda's reference (`Slides.Examples.AnimRef`)
const NUMS = { rect: ['x', 'y', 'width', 'height'], circle: ['cx', 'cy', 'r'], ellipse: ['cx', 'cy', 'rx', 'ry'],
               line: ['x1', 'y1', 'x2', 'y2'], text: ['x', 'y'] };
for (const [name, frames] of Object.entries(refs)) {
  const got = await page.evaluate(([name, ts]) => {
    const a = document.getElementById(name + '-frames');
    return ts.map(t => {
      a._show(t);
      return [...a.querySelector(':scope > .frame svg').children].slice(1)
        .map(el => [el.localName, ['polyline', 'polygon'].includes(el.localName)
          ? el.getAttribute('points').trim().split(/[ ,]+/).map(Number)
          : Object.fromEntries([...el.attributes].map(a => [a.name, +a.value]))]);
    });
  }, [name, frames.map(f => rat(f.t))]);
  let bad = [], worst = 0;
  frames.forEach((f, i) => {
    const want = f.ds, have = got[i];
    if (want === null) { if (have.length) bad.push(rat(f.t)); return; }
    if (want.length !== have.length) { bad.push(rat(f.t)); return; }
    want.forEach(([tag, ns], j) => {
      if (have[j][0] !== tag) { bad.push(rat(f.t)); return; }
      if (Array.isArray(have[j][1]) && have[j][1].length !== ns.length) { bad.push(rat(f.t)); return; }
      ns.forEach((v, m) => {
        const e = Math.abs(have[j][1][Array.isArray(have[j][1]) ? m : NUMS[tag][m]] - rat(v));
        worst = Math.max(worst, e);
        if (!(e < 1e-3)) bad.push(rat(f.t));
      });
    });
  });
  check(`${name}: ${frames.length} times agree with Agda (worst error ${worst.toExponential(1)})`, bad.length === 0, bad.slice(0, 5).join(', '));
}
check('no page errors', errors.length === 0, errors.join('; '));
await browser.close();
process.exit(failures ? 1 : 0);
