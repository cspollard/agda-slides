// Spike: drive tests/spike/anim/index.html (flipbook and CSS tracks, forward and backward).
// usage: node tests/spike/anim.mjs     (needs the browser dependencies of tests/browser)
import { chromium } from '../browser/node_modules/playwright-core/index.mjs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const chrome = process.env.CHROME ?? '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
let failures = 0;
const check = (n, ok, d = '') => { console.log(`${ok ? 'ok  ' : 'FAIL'} ${n}${ok ? '' : `  (${d})`}`); if (!ok) failures++; };

const browser = await chromium.launch({ executablePath: chrome, headless: true });
const page = await browser.newPage({ viewport: { width: 1280, height: 720 } });
const errors = [];
page.on('pageerror', e => errors.push(e.message));
page.on('console', m => { if (m.type() === 'error') errors.push(m.text()); });
await page.goto(pathToFileURL(path.join(here, 'anim', 'index.html')).href);
await page.waitForSelector('.reveal.ready');
const wait = ms => page.waitForTimeout(ms);
const step = id => page.evaluate(i => document.querySelector(`#${i} svg`).getAttribute('data-step'), id);
const shown = id => page.evaluate(i => [...document.querySelectorAll(`#${i} .frame`)]
  .filter(f => getComputedStyle(f).display !== 'none').map(f => f.dataset.f), id);
const tx = sel => page.evaluate(s => { const m = new DOMMatrix(getComputedStyle(document.querySelector(s)).transform); return [m.e, m.f]; }, sel);
const css = (sel, p) => page.evaluate(([s, q]) => getComputedStyle(document.querySelector(s))[q], [sel, p]);

console.log('-- flipbook');
await page.evaluate(() => Reveal.slide(0));
check('starts at step 0', await step('flip') === '0');
check('frame 0 shown', JSON.stringify(await shown('flip')) === '["0"]');
await page.evaluate(() => Reveal.nextFragment());
check('step 1', await step('flip') === '1');
check('frame 1 shown', JSON.stringify(await shown('flip')) === '["1"]');
await page.evaluate(() => Reveal.nextFragment());
check('frame 2 shown (rect and circle)', JSON.stringify(await shown('flip')) === '["2"]');
await page.evaluate(() => Reveal.prevFragment());
check('backward: frame 1 again', JSON.stringify(await shown('flip')) === '["1"]');

console.log('-- tracks');
await page.evaluate(() => Reveal.slide(1, 0, -1));
await wait(200);
check('starts at step 0', await step('tracks') === '0');
check('a at origin', JSON.stringify(await tx('#a')) === '[0,0]');
await page.evaluate(() => Reveal.nextFragment());
await wait(500);
let mid = await tx('#a');
check('linear: halfway through step 1 (x about 50)', mid[0] > 35 && mid[0] < 65 && mid[1] === 0, JSON.stringify(mid));
await wait(800);
check('linear: arrived at x = 100', JSON.stringify(await tx('#a')) === '[100,0]', JSON.stringify(await tx('#a')));
await page.evaluate(() => Reveal.nextFragment());
await wait(500);
mid = await tx('#a');
check('bezier: moving in y mid-transition', mid[1] > 5 && mid[1] < 75, JSON.stringify(mid));
check('step: colour has not jumped yet', (await css('#t', 'fill')) === 'rgb(0, 0, 0)', await css('#t', 'fill'));
check('fade: opacity partway', parseFloat(await css('#b', 'opacity')) > 0.2 && parseFloat(await css('#b', 'opacity')) < 0.8, await css('#b', 'opacity'));
await wait(800);
check('step: colour jumped at the end', (await css('#t', 'fill')) === 'rgb(255, 0, 0)', await css('#t', 'fill'));
check('arrived at (100, 80)', JSON.stringify(await tx('#a')) === '[100,80]', JSON.stringify(await tx('#a')));
await page.evaluate(() => Reveal.prevFragment());
await wait(500);
mid = await tx('#a');
check('backward: transition runs in reverse (y between 0 and 80)', mid[1] > 5 && mid[1] < 75, JSON.stringify(mid));
await wait(800);
check('backward: back at (100, 0)', JSON.stringify(await tx('#a')) === '[100,0]', JSON.stringify(await tx('#a')));
check('no page errors', errors.length === 0, errors.join(' | '));
await browser.close();
console.log(failures ? `${failures} failure(s)` : 'all spike checks passed');
process.exit(failures ? 1 : 0);
