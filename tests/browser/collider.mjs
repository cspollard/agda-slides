// The collider deck (`make collider-local`, src/Slides/Examples/ColliderSlides.lagda.md): slide
// count and titles, reveal steps per slide, every animation sampled at several times, no errors.
// The sampled frames are checked against numbers computed from the scenes' definitions
// (src/Slides/Examples/Collider.lagda.md, LHC.agda).  Set SHOTS=dir to save a screenshot of every
// slide (after its last step); CHROME overrides the browser.
//
// usage: node tests/browser/collider.mjs [outdir]   (default: ../../out, deck `collider-local`)
import { chromium } from 'playwright-core';
import path from 'node:path';
import fs from 'node:fs';
import { fileURLToPath, pathToFileURL } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const out = path.resolve(process.argv[2] ?? path.join(here, '..', '..', 'out'));
const chrome = process.env.CHROME ?? '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
let failures = 0;
const eq = (name, got, want) => {
  const ok = JSON.stringify(got) === JSON.stringify(want);
  console.log(`${ok ? 'ok  ' : 'FAIL'} ${name}${ok ? '' : `  (got ${JSON.stringify(got)}, want ${JSON.stringify(want)})`}`);
  if (!ok) failures++;
};

const browser = await chromium.launch({ executablePath: chrome, headless: true });
const page = await browser.newPage({ viewport: { width: 1280, height: 720 } });
const errors = [];
page.on('pageerror', e => errors.push(e.message));
page.on('requestfailed', r => errors.push('request failed: ' + r.url()));
page.on('response', r => { if (r.status() >= 400) errors.push(`${r.status()} ${r.url()}`); });
page.on('console', m => { if (m.type() === 'error') errors.push(m.text()); });
await page.goto(pathToFileURL(path.join(out, 'collider-local', 'index.html')).href);
await page.waitForFunction(() => window.Reveal && Reveal.isReady && Reveal.isReady());
await page.waitForTimeout(800);

// ---- slides and steps
const titles = ['how collider physics is', 'scientific impact of curiosity-driven particle physics', 'the Large Hadron Collider',
  'an early spin-off', 'a data firehose', 'the computing grid', 'statistical inference', 'when is a bump a discovery?',
  'an example with socks', 'estimating a parameter: slide the template', 'more data, a tighter likelihood',
  'simulation-based inference', 'one parameter, millions of events', 'built for the LHC, used by everyone',
  'try it yourself', '', 'references'];
const steps = [0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0];
eq('slide count', await page.evaluate(() => Reveal.getTotalSlides()), titles.length);
const got = [];
for (let i = 0; i < titles.length; i++) {
  await page.evaluate(i => Reveal.slide(i), i);
  await page.waitForTimeout(120);
  const info = await page.evaluate(() => {
    const s = Reveal.getCurrentSlide();
    const h = s.querySelector('h1, h2');
    return { title: h ? h.textContent : '', frags: s.querySelectorAll('.fragment').length };
  });
  eq(`slide ${i} title`, info.title, titles[i]);
  eq(`slide ${i} fragments`, info.frags, steps[i]);
  let n = 0;
  for (; n < 10; n++) {
    const before = await page.evaluate(() => Reveal.getCurrentSlide().querySelectorAll('.fragment.visible').length);
    await page.evaluate(() => Reveal.nextFragment());
    await page.waitForTimeout(60);
    if (before === await page.evaluate(() => Reveal.getCurrentSlide().querySelectorAll('.fragment.visible').length)) break;
  }
  got.push(n);
  if (process.env.SHOTS) {
    fs.mkdirSync(process.env.SHOTS, { recursive: true });
    await page.waitForTimeout(1500);
    await page.screenshot({ path: path.join(process.env.SHOTS, `collider-${String(i).padStart(2, '0')}.png`) });
  }
}
eq('steps taken on each slide', got, steps);

// ---- animations, sampled while their slide is not shown (a loop redraws a shown animation)
await page.evaluate(() => Reveal.slide(0));
await page.waitForTimeout(100);
const at = (id, t) => page.evaluate(([id, t]) => {
  const a = document.getElementById(id + '-frames');
  a._show(t);
  const svg = a.querySelector(':scope > .frame svg');
  const count = c => svg.querySelectorAll('.' + c).length;
  const centres = c => [...svg.querySelectorAll('circle.' + c)].map(e => [+e.getAttribute('cx'), +e.getAttribute('cy')]);
  return { box: svg.getAttribute('viewBox'), n: svg.children.length - 1, count, text: [...svg.querySelectorAll('text')].map(e => e.textContent),
           pipe: count('pipe'), bunch: centres('bunch'), burst: count('burst'), spark: count('spark'),
           pt: count('pt'), cur: count('cur'), now: count('now'), tmpl: count('tmpl'), mu: count('mu') };
}, [id, t]);
const dur = id => page.evaluate(id => document.getElementById(id + '-frames').dataset.duration, id);
const near = (a, b) => Math.abs(a - b) <= 2;

for (const id of ['d-lhc', 'd-lhc2']) {
  eq(`${id}: a lap is 64 ticks`, await dur(id), '64');
  eq(`${id}: loops`, await page.evaluate(id => document.getElementById(id + '-frames').hasAttribute('data-loop'), id), true);
  const f0 = await at(id, 0), f16 = await at(id, 16), f20 = await at(id, 20), f32 = await at(id, 32), f63 = await at(id, 63);
  eq(`${id}: frame size`, f0.box, '0 0 1920 920');
  eq(`${id} t=0: one pipe, two bunch cores meeting at the bottom, a burst and eight sparks`, [f0.pipe, f0.bunch.length, f0.burst, f0.spark], [1, 2, 1, 8]);
  eq(`${id} t=0: bunches at the collision point`, f0.bunch.map(c => near(c[0], 960) && near(c[1], 740)), [true, true]);
  eq(`${id} t=16: bunches at the sides, flash over`, [f16.bunch.length, f16.burst, f16.spark], [2, 0, 0]);
  eq(`${id} t=16: bunches at the right and left ends`, [near(f16.bunch[0][0], 1840), near(f16.bunch[1][0], 80), near(f16.bunch[0][1], 400)], [true, true, true]);
  eq(`${id} t=20: no flash`, [f20.burst, f20.spark], [0, 0]);
  eq(`${id} t=32: bunches pass at the top`, f32.bunch.map(c => near(c[0], 960) && near(c[1], 60)), [true, true]);
  eq(`${id} t=63: one tick before the collision`, [f63.pipe, f63.bunch.length, f63.burst], [1, 2, 0]);
  const phase0 = await page.evaluate(id => document.getElementById(id + '-frames').dataset.phase, id);
  await page.evaluate(i => Reveal.slide(i), id === 'd-lhc' ? 1 : 2);
  await page.waitForTimeout(500);
  const phase1 = await page.evaluate(id => document.getElementById(id + '-frames').dataset.phase, id);
  check(`${id}: plays while its slide is shown`, phase1 !== undefined && phase1 !== phase0);
  await page.evaluate(() => Reveal.slide(0));
  await page.waitForTimeout(100);
}
function check(n, ok) { eq(n, ok, true); }

// the scan: the mean runs from 5.00 to 11.00 in 25 quarter-bin steps, one dot more each step
eq('d-scan: 25 ticks', await dur('d-scan'), '25');
for (const [t, mu, dots] of [[0, 'μ = 5.00', 1], [4, 'μ = 6.00', 5], [12.5, 'μ = 8.00', 13], [24.5, 'μ = 11.00', 25]]) {
  const f = await at('d-scan', t);
  eq(`d-scan t=${t}: readout`, f.text.includes(mu), true);
  eq(`d-scan t=${t}: dots on the curve`, f.cur, dots);
  eq(`d-scan t=${t}: 16 data points, one mean line, one marker`, [f.pt, f.mu, f.now], [16, 1, 1]);
}
eq('d-scan: axes names stay', (await at('d-scan', 7)).text.filter(s => ['counts', 'template mean μ', 'observable x (bin)', '-2 ln L(μ)'].includes(s)).length, 4);

// more data: twelve batches of three ticks, the events running total
eq('d-grow: 36 ticks', await dur('d-grow'), '36');
for (const [t, events] of [[0, 20], [2.9, 20], [3, 36], [35, 240]]) {
  const f = await at('d-grow', t);
  eq(`d-grow t=${t}: events`, f.text.includes('events: ' + events), true);
  eq(`d-grow t=${t}: 16 points, 25 curve dots`, [f.pt, f.cur], [16, 25]);
}
{
  // the peak of the template at the true mean grows with the batches (amp = 10 (s + 1) / 3, four pixels a count)
  const peak = t => page.evaluate(t => { const a = document.getElementById('d-grow-frames'); a._show(t);
    return Math.max(...[...a.querySelectorAll('rect.tmpl')].map(e => +e.getAttribute('height'))); }, t);
  const p0 = await peak(0), p35 = await peak(35);
  eq('d-grow: the template peak is 12 high at the first batch and 160 at the last', [p0, p35], [12, 160]);
}

await page.evaluate(() => Reveal.slide(0));
await browser.close();
eq('no console errors or failed loads', errors, []);
if (failures) { console.log(`${failures} failure(s)`); process.exit(1); }
console.log('all collider checks passed');
