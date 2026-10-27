// Label navigation in reveal on the labelled example deck (src/Slides/Examples/Labels.agda).
// Slides, flat from 0: intro, details, unnamed, more (a stack: 3 and 4), end.  `#/id` goes to a
// labelled slide on load and on hashchange; a numeric `#/h` still works; an unknown id stays put.
// usage: node tests/browser/labels.mjs [outdir]   (after `make labels`)
import { chromium } from 'playwright-core';
import path from 'node:path';
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
const url = hash => pathToFileURL(path.join(out, 'labels', 'index.html')).href + hash;
const where = page => page.evaluate(() => { const i = Reveal.getIndices(); return [i.h, i.v]; });
const open = async hash => {
  const page = await browser.newPage({ viewport: { width: 1280, height: 800 } });
  await page.goto(url(hash));
  await page.waitForFunction(() => window.Reveal && Reveal.isReady && Reveal.isReady());
  return page;
};

for (const [id, want] of [['intro', [0, 0]], ['details', [1, 0]], ['more', [3, 0]], ['end', [4, 0]]])
  eq(`load #/${id}`, await where(await open('#/' + id)), want);
eq('load #/2 (unnamed, by number)', await where(await open('#/2')), [2, 0]);

const page = await open('');
eq('start', await where(page), [0, 0]);
for (const [id, want] of [['end', [4, 0]], ['details', [1, 0]], ['more', [3, 0]], ['intro', [0, 0]]]) {
  await page.evaluate(h => { location.hash = h; }, '#/' + id);
  await page.waitForFunction(w => { const i = Reveal.getIndices(); return i.h === w[0] && i.v === w[1]; }, want, { timeout: 3000 }).catch(() => {});
  eq(`hashchange #/${id}`, await where(page), want);
}
await page.evaluate(() => { location.hash = '#/nowhere'; });
await page.waitForTimeout(300);
eq('unknown label stays put', await where(page), [0, 0]);
await browser.close();
if (failures) { console.log(`${failures} failure(s)`); process.exit(1); }
console.log('all label checks passed');
