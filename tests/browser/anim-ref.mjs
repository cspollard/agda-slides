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
  const NUMS = { rect: ['x', 'y', 'width', 'height'], circle: ['cx', 'cy', 'r'], line: ['x1', 'y1', 'x2', 'y2'], text: ['x', 'y'] };
  // the page's drawing commands as [tag, numbers] (the first child of the svg is the arrowhead's defs)
  const drawn = svg => [...svg.children].slice(1).map(el => [el.localName, (NUMS[el.localName] || []).map(k => +el.getAttribute(k))]);
  const frac = q => q[0] / q[1];
  // the references computed by Agda from the exact semantics
  const refs = {};
  for (const e of document.querySelectorAll('[data-js]')) {
    const j = e.getAttribute('data-js');
    if (j.startsWith('({"ref"')) { const r = JSON.parse(j.slice(1, -1)); refs[r.ref] = r; }
  }
  const res = {};
  for (const a of document.querySelectorAll('.animation')) {
    const name = a.id.replace(/-0-frames$/, "");
    const param = a.dataset.param !== undefined;
    const n = param ? +a.dataset.n : JSON.parse(a.dataset.deltas).length + 1;
    const diagrams = [...document.querySelectorAll(`[id^="ref-${name}-"]`)].filter(e => e.classList.contains('diagram'));
    let bad = [], order = [], worst = 0, checked = 0, boundaryWorst = 0, nBoundary = 0;
    if (param) {
      const P = JSON.parse(a.dataset.param);
      // piece boundaries of every segment: where Step jumps and easings start and stop
      const bounds = new Set();
      for (const [s, ps] of P.v) { let t = s; bounds.add(t); for (const p of ps) { t += p[0]; bounds.add(t); } }
      const R = refs[name];
      for (let i = 0; R && i < R.taus.length; i++) {
        const tau = frac(R.taus[i]);
        a._show(tau);
        const got = drawn(a.querySelector(':scope > .frame svg')), want = R.frames[i];
        let ok = want !== null && got.length === want.length;
        let err = 0;
        for (let j = 0; ok && j < want.length; j++) {
          ok = got[j][0] === want[j][0] && got[j][1].length === want[j].length - 1;
          for (let m = 0; ok && m < got[j][1].length; m++) err = Math.max(err, Math.abs(got[j][1][m] - frac(want[j][m + 1])));
        }
        const isB = bounds.has(tau);
        if (isB) { nBoundary++; boundaryWorst = Math.max(boundaryWorst, err); }
        worst = Math.max(worst, err); checked++;
        if (!ok || err > (isB ? 1e-9 : 0.01)) bad.push(tau);
      }
      // the whole-step animation also equals the discrete frames Agda computes (as diagrams)
      if (diagrams.length) {
        for (let k = 0; k < n; k++) {
          a._show(k);
          const got = drawn(a.querySelector(':scope > .frame svg')), want = drawn(diagrams[k].querySelector('svg'));
          if (JSON.stringify(got) !== JSON.stringify(want)) bad.push('discrete ' + k);
        }
      }
      res[name] = { frames: n, refs: R ? R.taus.length : 0, bad, param, phases: P.p.length, size: a.dataset.param.length, formulas: JSON.stringify(P.p).length, worst, checked, boundaryWorst, nBoundary, discrete: diagrams.length };
    } else {
      // forwards, then straight back to the start and to the middle (rebuilding from the first frame)
      for (let k = 0; k < n; k++) order.push(k);
      order.push(0, Math.floor(n / 2), n - 1, 1);
      for (const k of order) {
        a._show(k);
        const got = norm(a.querySelector(':scope > .frame svg'));
        const want = diagrams[k] && norm(diagrams[k].querySelector('svg'));
        if (got !== want) bad.push(k);
      }
      res[name] = { frames: n, refs: diagrams.length, bad, param, phases: 0, size: a.dataset.deltas.length };
    }
  }
  return res;
});
for (const [name, r] of Object.entries(result)) {
  if (r.param) {
    check(`${name}: ${r.refs || r.discrete} reference ${r.discrete && !r.refs ? 'frames (every tick of the period, compared exactly)' : 'times'} from Agda (${r.frames} ticks)`, (r.refs > 0 && r.refs >= r.frames) || (r.discrete === r.frames));
    check(`${name}: the simulator agrees with Agda at ${r.checked || r.discrete} ${r.checked ? 'times' : 'ticks'} (worst error ${r.worst.toFixed(5)}; at ${r.nBoundary} piece boundaries ${r.boundaryWorst.toExponential(1)})`, r.bad.length === 0, `differs at ${r.bad.slice(0, 8)}`);
    check(`${name}: shipped as a simulator (${r.phases} phases), ${r.size} characters`, true);
  } else {
    check(`${name}: ${r.frames} frames, ${r.refs} references`, r.frames === r.refs, `${r.frames} vs ${r.refs}`);
    check(`${name}: the player agrees with Agda on every frame`, r.bad.length === 0, `differs at ${r.bad.slice(0, 8)}`);
    check(`${name}: shipped as edits, ${r.size} characters`, true);
  }
  check(`${name}: shipped ${r.param ? 'as formulas' : 'as edits'} as expected`, r.param === (name.startsWith('t') || name.startsWith('d')));
}
// size does not grow with the ticks: the formulas of the 60-tick and the 600-tick slider have the same length
const L60 = result.tlong, L600 = result.tvlong;
check('formulas: 60 and 600 ticks ship the same number of characters', L60 && L600 && L60.formulas === L600.formulas, `${L60 && L60.formulas} vs ${L600 && L600.formulas}`);
check('whole data: the 600-tick slider is at most 3 characters larger than the 60-tick one', L60 && L600 && L600.size - L60.size <= 3, `${L60 && L60.size} vs ${L600 && L600.size}`);
check('the 60-tick slider as formulas is smaller than as edits', L60 && result.elong && L60.size < result.elong.size, `${L60 && L60.size} vs ${result.elong && result.elong.size}`);
check('a discrete reference was compared for the whole-step slider', result.twhole && result.twhole.discrete === 6);
check('animations found', Object.keys(result).length === 12, String(Object.keys(result).length));
check('no page errors', errors.length === 0, errors.join('; '));
await browser.close();
console.log(failures === 0 ? 'all anim-ref tests passed' : `${failures} failure(s)`);
process.exit(failures === 0 ? 0 : 1);
