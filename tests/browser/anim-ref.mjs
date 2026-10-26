// Checks the page player against Agda: every frame the player rebuilds from the first
// frame and the edits must be the frame Agda computed (the reference diagrams of the
// `animref` deck, `make animref`).  Frames are compared as serialized SVG, without the
// arrowhead `<defs>` (whose id depends on the diagram's name).
//
// usage: node tests/browser/anim-ref.mjs [outdir]   (default: ../../out, deck `animref`)
import { chromium } from 'playwright-core';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const out = path.resolve(process.argv[2] ?? path.join(here, '..', '..', 'out'));
const chrome = process.env.CHROME ?? '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
let failures = 0;
const check = (n, ok, d = '') => { console.log(`${ok ? 'ok  ' : 'FAIL'} ${n}${ok ? '' : `  (${d})`}`); if (!ok) failures++; };

const browser = await chromium.launch({ executablePath: chrome, headless: true });
const page = await browser.newPage();
const errors = [];
page.on('pageerror', e => errors.push(e.message));
await page.goto(pathToFileURL(path.join(out, 'animref', 'index.html')).href);
await page.waitForTimeout(300);

const result = await page.evaluate(() => {
  const norm = svg => { const c = svg.cloneNode(true); c.querySelectorAll('defs').forEach(d => d.remove()); return c.outerHTML.replace(/url\(#[^)]*-arrow\)/g, "url(#arrow)"); };
  const res = {};
  for (const a of document.querySelectorAll('.animation')) {
    const name = a.id.replace(/-0-frames$/, "");
    const n = JSON.parse(a.dataset.deltas).length + 1;
    const refs = [...document.querySelectorAll(`[id^="ref-${name}-"]`)].filter(e => e.classList.contains('diagram'));
    let bad = [], order = [];
    // forwards, then straight back to the start and to the middle (rebuilding from the first frame)
    for (let k = 0; k < n; k++) order.push(k);
    order.push(0, Math.floor(n / 2), n - 1, 1);
    for (const k of order) {
      a._show(k);
      const got = norm(a.querySelector(':scope > .frame svg'));
      const want = refs[k] && norm(refs[k].querySelector('svg'));
      if (got !== want) bad.push(k);
    }
    res[name] = { frames: n, refs: refs.length, bad };
  }
  return res;
});
for (const [name, r] of Object.entries(result)) {
  check(`${name}: ${r.frames} frames, ${r.refs} references`, r.frames === r.refs, `${r.frames} vs ${r.refs}`);
  check(`${name}: the player agrees with Agda on every frame`, r.bad.length === 0, `differs at ${r.bad.slice(0, 8)}`);
}
check('animations found', Object.keys(result).length === 2);
check('no page errors', errors.length === 0, errors.join('; '));
await browser.close();
console.log(failures === 0 ? 'all anim-ref tests passed' : `${failures} failure(s)`);
process.exit(failures === 0 ? 0 : 1);
