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
  const fs = [...document.querySelectorAll('.animation > .frame')];
  return fs.map((f, i) => f.hidden ? null : i).filter(i => i !== null);
});
const text = () => page.evaluate(() => [...document.querySelectorAll('.animation > .frame:not([hidden]) text')].map(t => t.textContent));
const same = (n, got, want) => check(n, JSON.stringify(got) === JSON.stringify(want), `got ${JSON.stringify(got)}, want ${JSON.stringify(want)}`);

same('three frames', await page.evaluate(() => document.querySelectorAll('.animation > .frame').length), 3);
same('two steps', await page.evaluate(() => document.querySelectorAll('.animation .anim-step').length), 2);
same('frame 0 first', await shown(), [0]);
same('caption one', await text(), ['one']);
await page.evaluate(() => Reveal.nextFragment());
same('frame 1 after a step', await shown(), [1]);
same('caption two', await text(), ['two']);
await page.evaluate(() => Reveal.nextFragment());
same('frame 2 after two steps', await shown(), [2]);
await page.evaluate(() => Reveal.prevFragment());
same('frame 1 stepping back', await shown(), [1]);
await page.evaluate(() => Reveal.prevFragment());
same('frame 0 stepping back', await shown(), [0]);
await page.evaluate(i => { Reveal.slide(0); Reveal.slide(i); }, slide);
same('frame 0 on re-entering', await shown(), [0]);
same('no page errors', errors, []);
await browser.close();
process.exit(failures ? 1 : 0);
