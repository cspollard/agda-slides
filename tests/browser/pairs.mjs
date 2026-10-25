// Drives the rendered "It Just Takes Two" deck (`make pairs`): structure,
// the SVG diagrams, and every JavaScript animation.
//
// usage: node pairs.mjs [outdir [deck]]   (default: ../../out, deck `pairs`;
// `pairs-local` is the build with a local copy of reveal.js)
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
page.on('console', m => { if (m.type() === 'error') errors.push(m.text()); });
const deck = process.argv[3] ?? 'pairs';
console.log(`deck: ${deck}`);
await page.goto(pathToFileURL(path.join(out, deck, 'index.html')).href);
await page.waitForSelector('.reveal.ready');
const ev = f => page.evaluate(f);
const go = async i => { await page.evaluate(n => Reveal.slide(n), i); };
const wait = ms => page.waitForTimeout(ms);

console.log('-- structure');
eq('eleven slides', await ev(() => Reveal.getHorizontalSlides().length), 11);
eq('first slide is the title', await ev(() => Reveal.getHorizontalSlides()[0].querySelector('h1').textContent), 'It Just Takes Two');
eq('deck script ran (reveal configured)', await ev(() => Reveal.getConfig().center), false);
eq('reveal.js came from the expected place', await ev(() => Array.from(document.scripts).some(s => s.src.includes('reveal.js@6.0.2/')) ? 'cdn' : 'local'), deck === 'pairs' ? 'cdn' : 'local');
eq('pairs.js loaded', await ev(() => typeof PAIRS.title), 'function');
check('stylesheet applied', await ev(() => getComputedStyle(document.querySelector('.card')).borderRadius !== '0px'));
eq('diagram slides', await ev(() =>
  Reveal.getHorizontalSlides().map(s => s.querySelectorAll('.diagram svg').length).join(',')),
  '0,1,0,0,1,1,1,0,1,1,0');
eq('math rendered on slides 2, 5, 7', await ev(() =>
  [1, 4, 6].map(i => Reveal.getHorizontalSlides()[i].querySelectorAll('.katex').length > 0).join(',')), 'true,true,true');

console.log('-- title animation');
await go(0); await wait(600);
eq('canvas drawn in the hero mount', await ev(() => {
  const c = document.querySelector('#hero-title canvas');
  return !!c && c.width > 0 && c.height > 0;
}), true);
check('canvas has painted pixels', await ev(() => {
  const c = document.querySelector('#hero-title canvas');
  const d = c.getContext('2d').getImageData(0, 0, c.width, c.height).data;
  for (let i = 3; i < d.length; i += 4) if (d[i] > 0) return true;
  return false;
}));

console.log('-- pulses along arrows');
await go(1); await wait(500);
check('slide 2: pulses were added', await ev(() => document.querySelectorAll('#d-problem .pulse').length >= 8));
const p0 = await ev(() => document.querySelector('#d-problem .pulse').getAttribute('cx'));
await wait(400);
const p1 = await ev(() => document.querySelector('#d-problem .pulse').getAttribute('cx'));
check('slide 2: pulses move', p0 !== p1, `${p0} = ${p1}`);

console.log('-- live histogram');
await go(2); await wait(1500);
const hist = () => ev(() => {
  const h = r => Array.from(document.querySelectorAll('#bump ' + r)).reduce((a, e) => a + +e.getAttribute('height'), 0);
  return { bkg: h('.hist-bkg'), sig: h('.hist-sig'), cap: document.querySelector('#bump text:not(.dim)').textContent };
});
const h1 = await hist();
check('histogram has background and signal', h1.bkg > 0 && h1.sig > 0, JSON.stringify(h1));
await wait(1500);
const h2 = await hist();
check('histogram keeps filling', +h2.cap.match(/\d+/)[0] > +h1.cap.match(/\d+/)[0], `${h1.cap} -> ${h2.cap}`);
await wait(3500);
eq('histogram stops at 2500 events', (await hist()).cap, 'N = 2500 events');

console.log('-- fragments');
await go(3);
eq('slide 4: one fragment (the callout)', await ev(() => Reveal.getCurrentSlide().querySelectorAll('.fragment').length), 1);

console.log('-- highlighting cycles');
await go(5); await wait(300);
const lit = new Set();
for (let i = 0; i < 12; i++) {
  lit.add(await ev(() => ['st1', 'st2', 'st3'].filter(i => document.getElementById(i).classList.contains('on')).join('+')));
  await wait(450);
}
check('slide 6: each stage lights up in turn', ['st1', 'st2', 'st3'].every(i => lit.has(i)), [...lit].join(' | '));
await go(6);
const chain = new Set();
for (let i = 0; i < 14; i++) {
  chain.add(await ev(() => ['c1', 'c2', 'c3', 'c4'].filter(i => document.getElementById(i).classList.contains('on')).length));
  await wait(450);
}
check('slide 7: the chain builds up', [0, 1, 2, 3].every(n => chain.has(n)), [...chain].join(','));

console.log('-- bars and counters');
await go(8); await wait(2800);
eq('slide 9: bars grown', await ev(() => document.querySelectorAll('#d-results .bar.go').length), 3);
eq('slide 9: counters reach the paper\'s numbers', await ev(() =>
  Array.from(document.querySelectorAll('#d-results .count')).map(e => e.textContent)), ['1.17', '0.35', '0.05']);
await go(9); await wait(2800);
eq('slide 10: counters reach their targets', await ev(() =>
  Array.from(document.querySelectorAll('#d-tiles .count')).map(e => e.textContent)), ['≈100×', '128', '0.004']);

console.log('-- closing slide');
await go(10); await wait(600);
check('slide 11: canvas animation and link', await ev(() =>
  !!document.querySelector('#hero-end canvas') && !!Reveal.getCurrentSlide().querySelector('a[href="https://arxiv.org/abs/2605.07972"]')));

eq('no page errors', errors, []);
await browser.close();
console.log(failures === 0 ? 'all deck tests passed' : `${failures} failure(s)`);
process.exit(failures === 0 ? 0 : 1);
