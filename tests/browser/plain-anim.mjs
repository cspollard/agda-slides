// Drives the animations of the standalone HTML backend (`make showcase`):
// steps play on the arrow keys (forward and backward), a loop runs while its
// slide is active and stands still otherwise, and printing shows the last step.
//
// usage: node tests/browser/plain-anim.mjs [outdir]   (default: ../../out, deck `showcase-plain`)
// Set CHROME to override the browser binary.

import { chromium } from 'playwright-core';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const out = path.resolve(process.argv[2] ?? path.join(here, '..', '..', 'out'));
const chrome = process.env.CHROME
  ?? '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'ok  ' : 'FAIL'} ${name}${ok ? '' : `  (${detail})`}`);
  if (!ok) failures++;
}
const eq = (name, got, want) => check(name, JSON.stringify(got) === JSON.stringify(want), `got ${JSON.stringify(got)}, want ${JSON.stringify(want)}`);

const browser = await chromium.launch({ executablePath: chrome, headless: true });
const page = await browser.newPage({ viewport: { width: 1280, height: 720 } });
const errors = [];
page.on('pageerror', e => errors.push(e.message));
const slide = await (async () => {
  await page.goto(pathToFileURL(path.join(out, 'showcase-plain', 'index.html')).href);
  return page.evaluate(() => Array.from(document.querySelectorAll('.slide')).findIndex(s => s.querySelector('.animation')));
})();
check('a slide holds the animations', slide >= 0);
await page.goto(pathToFileURL(path.join(out, 'showcase-plain', 'index.html')).href + '#' + (slide + 1));
await page.reload();  // a hash change alone does not rerun the page script
await page.waitForTimeout(300);

const shown = id => page.evaluate(id => {
  const a = document.getElementById(id);
  const fs = Array.from(a.querySelectorAll(':scope > .frame'));
  return { index: Math.round(+(a.dataset.cur || 0)), phase: +(a.dataset.phase || 0), visible: fs.length, text: fs[0].textContent };
}, id);
const key = async k => { await page.keyboard.press(k); await page.waitForTimeout(500); };

console.log('-- steps');
eq('step 0 shows the first frame', (await shown('steps-frames')).index, 0);
await key('ArrowRight');
eq('step 1 rests at the end of act 1', (await shown('steps-frame'+'s')).index, 2);
await key('ArrowRight');
eq('step 2 rests at the end of act 2', (await shown('steps-frames')).index, 3);
await key('ArrowLeft');
eq('stepping back plays back', (await shown('steps-frames')).index, 2);
eq('one frame at a time', (await shown('steps-frames')).visible, 1);

console.log('-- loop');
const words = new Set();
for (let i = 0; i < 12; i++) { words.add((await page.evaluate(() => document.querySelector('#blink-frames > .frame text').textContent))); await page.waitForTimeout(100); }
eq('the loop shows both of its frames', [...words].sort(), ['tick', 'tock']);

console.log('-- printing');
// the loop's timer must not draw over the printed page: wait several loop ticks after `beforeprint`
await page.evaluate(() => window.dispatchEvent(new Event('beforeprint')));
await page.waitForTimeout(600);
eq('printing shows the last step of the steps', (await shown('steps-frames')).index, 3);
eq('and the first phase of the loop, which stands still', (await shown('blink-frames')).phase, 0);
await page.evaluate(() => window.dispatchEvent(new Event('afterprint')));
eq('afterprint restores the step', (await shown('steps-frames')).index, 2);
await page.waitForTimeout(300);
check('and the loop runs again', (await shown('blink-frames')).phase !== 0);

eq('no page errors', errors, []);
await browser.close();
console.log(failures === 0 ? 'all plain-animation tests passed' : `${failures} failure(s)`);
process.exit(failures === 0 ? 0 : 1);
