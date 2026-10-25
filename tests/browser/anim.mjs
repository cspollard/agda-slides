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
  const fs = [...document.querySelectorAll('#mover-0-frames > .frame')];
  return fs.map((f, i) => f.hidden ? null : i).filter(i => i !== null);
});
const text = () => page.evaluate(() => [...document.querySelectorAll('#mover-0-frames > .frame:not([hidden]) text')].map(t => t.textContent));
const same = (n, got, want) => check(n, JSON.stringify(got) === JSON.stringify(want), `got ${JSON.stringify(got)}, want ${JSON.stringify(want)}`);

const waitMs = ms => page.waitForTimeout(ms);
same('three frames', await page.evaluate(() => document.querySelectorAll('#mover-0-frames > .frame').length), 3);
same('one step', await page.evaluate(() => document.querySelectorAll('#mover-0-frames .anim-step').length), 1);
same('frame 0 first', await shown(), [0]);
same('caption one', await text(), ['one']);
await page.evaluate(() => Reveal.nextFragment());
await waitMs(150);
check('still near the start shortly after the step', (await shown())[0] <= 1, JSON.stringify(await shown()));
await waitMs(1500);
same('plays to the last frame', await shown(), [2]);
same('caption three', await text(), ['three']);
await page.evaluate(() => Reveal.prevFragment());
await waitMs(1500);
same('plays back to frame 0', await shown(), [0]);
await page.evaluate(i => { Reveal.slide(0); Reveal.slide(i); }, slide);
same('frame 0 on re-entering', await shown(), [0]);

// two acts: five frames, resting on 2 and 4
const actsSlide = await page.evaluate(() => Reveal.getHorizontalSlides().findIndex(s => s.querySelector('#acts-0-frames')));
await page.evaluate(i => Reveal.slide(i), actsSlide);
const actShown = () => page.evaluate(() => [...document.querySelectorAll('#acts-0-frames > .frame')].map((f, i) => f.hidden ? null : i).filter(i => i !== null));
same('two steps', await page.evaluate(() => document.querySelectorAll('#acts-0-frames .anim-step').length), 2);
same('rests recorded', await page.evaluate(() => document.querySelector('#acts-0-frames').dataset.rests), '2,4');
same('acts start on frame 0', await actShown(), [0]);
await page.evaluate(() => Reveal.nextFragment());
await waitMs(600);
same('first act rests on frame 2', await actShown(), [2]);
await page.evaluate(() => Reveal.nextFragment());
await waitMs(600);
same('second act rests on frame 4', await actShown(), [4]);
await page.evaluate(() => Reveal.prevFragment());
await waitMs(600);
same('back to the first act\'s rest', await actShown(), [2]);

// the eased slider: six frames, the box moves right, slowly then quickly then slowly
const sliderSlide = await page.evaluate(() => Reveal.getHorizontalSlides().findIndex(s => s.querySelector('#slider-0-frames')));
await page.evaluate(i => Reveal.slide(i), sliderSlide);
const xs = await page.evaluate(() => [...document.querySelectorAll('#slider-0-frames > .frame rect')].map(r => +r.getAttribute('x')));
same('six slider frames', xs.length, 6);
check('slider moves right monotonically', xs.every((x, i) => i === 0 || x > xs[i - 1]), JSON.stringify(xs));
const gaps = xs.slice(1).map((x, i) => x - xs[i]);
check('ease-in-out: slow, fast, slow', gaps[0] < gaps[2] && gaps[4] < gaps[2], JSON.stringify(gaps));
same('no page errors', errors, []);
await browser.close();
process.exit(failures ? 1 : 0);
