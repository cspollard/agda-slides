// A deck with a non-default key binding (`make keys`, KeysMain.agda): the binding reaches
// reveal.js as a `keyboard` option for exactly the keys where it differs from reveal's own
// table, and works.  The keys that agree (ArrowRight, ArrowLeft, Space, n) are not emitted.
//
// usage: node tests/browser/keys.mjs [outdir]   (default: ../../out, deck `keys`)
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
await page.goto(pathToFileURL(path.join(out, 'keys', 'index.html')).href);
await page.waitForSelector('.reveal.ready');

const keyboard = await page.evaluate(() => Reveal.getConfig().keyboard);
const want = { 72: false, 74: false, 75: false, 76: false, 38: false, 40: false, 81: 'next' };
check('keyboard option: q is next; h j k l Up Down are off; nothing else',
  JSON.stringify(Object.entries(keyboard).sort()) === JSON.stringify(Object.entries(want).sort()),
  JSON.stringify(keyboard));

const state = () => page.evaluate(() => { const i = Reveal.getIndices(); return [i.h, Reveal.getSlide(i.h).querySelectorAll('.fragment.visible').length]; });
const press = async k => { await page.keyboard.press(k); await page.waitForTimeout(100); };
const same = (n, got, w) => check(n, JSON.stringify(got) === JSON.stringify(w), `got ${JSON.stringify(got)}, want ${JSON.stringify(w)}`);

same('start', await state(), [0, 0]);
await press('q');           same('q is next (a step)', await state(), [0, 1]);
await press('ArrowRight');  same('ArrowRight is next (a slide)', await state(), [1, 0]);
await press('l');           same('l is off', await state(), [1, 0]);
await press('ArrowDown');   same('ArrowDown is off', await state(), [1, 0]);
await press('ArrowLeft');   same('ArrowLeft is prev', await state(), [0, 1]);
await press('j');           same('j is off', await state(), [0, 1]);
await press('h');           same('h is off', await state(), [0, 1]);
await press('n');           same('n (a common key) is next', await state(), [1, 0]);
await press('Home');        same('Home (a common key) is first (the slide is shown full)', await state(), [0, 1]);
await press('Space');       same('Space (a common key) is next', await state(), [1, 0]);

check('no page errors', errors.length === 0, errors.join('; '));
await browser.close();
process.exit(failures ? 1 : 0);
