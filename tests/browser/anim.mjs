// Drives the `animate` slide of the intro deck (`make example`): the frame shown
// is the number of visible steps, forward and backward.
//
// usage: node tests/browser/anim.mjs [outdir]   (default: ../../out, deck `intro`)
import { chromium } from 'playwright-core';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const out = path.resolve(process.argv[2] ?? path.join(here, '..', '..', 'out'));
const chrome = process.env.CHROME ?? '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
let failures = 0;
const check = (n, ok, d = '') => { console.log(`${ok ? 'ok  ' : 'FAIL'} ${n}${ok ? '' : `  (${d})`}`); if (!ok) failures++; };

const browser = await chromium.launch({ executablePath: chrome, headless: true });
const page = await browser.newPage({ viewport: { width: 1280, height: 720 } });
const errors = [];
page.on('pageerror', e => errors.push(e.message));
page.on('console', m => { if (m.type() === 'error') errors.push(m.text()); });
await page.goto(pathToFileURL(path.join(out, 'intro', 'index.html')).href);
await page.waitForSelector('.reveal.ready');

const slide = await page.evaluate(() => Reveal.getHorizontalSlides().findIndex(s => s.querySelector('.animation')));
check('a slide holds the animation', slide >= 0);
await page.evaluate(i => Reveal.slide(i), slide);
const shown = () => page.evaluate(() => {
  return [Math.round(+document.getElementById('mover-frames').dataset.cur)];
});
const text = () => page.evaluate(() => [...document.querySelectorAll('#mover-frames > .frame text')].map(t => t.textContent));
const same = (n, got, want) => check(n, JSON.stringify(got) === JSON.stringify(want), `got ${JSON.stringify(got)}, want ${JSON.stringify(want)}`);

const waitMs = ms => page.waitForTimeout(ms);
same('duration three ticks', await page.evaluate(() => document.getElementById('mover-frames').dataset.duration), '3');
same('one step', await page.evaluate(() => document.querySelectorAll('#mover-frames .anim-step').length), 1);
same('frame 0 first', await shown(), [0]);
same('caption one', await text(), ['one']);
await page.evaluate(() => Reveal.nextFragment());
await waitMs(150);
check('still near the start shortly after the step', (await shown())[0] <= 1, JSON.stringify(await shown()));
await waitMs(1500);
same('plays to the end', await shown(), [3]);
same('caption three', await text(), ['three']);
await page.evaluate(() => Reveal.prevFragment());
await waitMs(1500);
same('plays back to the start', await shown(), [0]);
await page.evaluate(i => { Reveal.slide(0); Reveal.slide(i); }, slide);
same('frame 0 on re-entering', await shown(), [0]);

// two acts of three and two ticks, resting on 3 and 5
const actsSlide = await page.evaluate(() => Reveal.getHorizontalSlides().findIndex(s => s.querySelector('#acts-frames')));
await page.evaluate(i => Reveal.slide(i), actsSlide);
const actShown = () => page.evaluate(() => [Math.round(+document.getElementById('acts-frames').dataset.cur)]);
same('two steps', await page.evaluate(() => document.querySelectorAll('#acts-frames .anim-step').length), 2);
same('rests recorded', await page.evaluate(() => document.querySelector('#acts-frames').dataset.rests), '[3,5]');
same('acts start on frame 0', await actShown(), [0]);
await page.evaluate(() => Reveal.nextFragment());
await waitMs(600);
same('first act rests at tick 3', await actShown(), [3]);
await page.evaluate(() => Reveal.nextFragment());
await waitMs(600);
same('second act rests at tick 5', await actShown(), [5]);
await page.evaluate(() => Reveal.prevFragment());
await waitMs(600);
same('back to the first act\'s rest', await actShown(), [3]);

// the slider: the box moves right, linearly (a Coupling driver)
const sliderSlide = await page.evaluate(() => Reveal.getHorizontalSlides().findIndex(s => s.querySelector('#slider-frames')));
await page.evaluate(i => Reveal.slide(i), sliderSlide);
// the box's x at each frame, as the player draws it
const xs = await page.evaluate(() => {
  const a = document.getElementById('slider-frames');
  const n = 6, out = [];
  for (let k = 0; k < n; k++) { a._show(k); out.push(+a.querySelector(':scope > .frame rect').getAttribute('x')); }
  return out;
});
same('six slider frames', xs.length, 6);
check('slider moves right monotonically', xs.every((x, i) => i === 0 || x > xs[i - 1]), JSON.stringify(xs));
const gaps = xs.slice(1).map((x, i) => x - xs[i]);
check('linear: equal gaps', gaps.every(g => Math.abs(g - gaps[0]) < 1e-6), JSON.stringify(gaps));
same('no page errors', errors, []);
await browser.close();
process.exit(failures ? 1 : 0);
