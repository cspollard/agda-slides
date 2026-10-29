// Drives the rendered "It Just Takes Two" deck (`make pairs`): structure,

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
page.on('requestfailed', r => errors.push('request failed: ' + r.url()));
page.on('response', r => { if (r.status() >= 400) errors.push(`${r.status()} ${r.url()}`); });
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
eq('no JavaScript beyond reveal and the deck script', await ev(() => typeof PAIRS), 'undefined');
check('stylesheet applied', await ev(() => getComputedStyle(document.querySelector('.card')).borderRadius !== '0px'));
eq('diagram slides', await ev(() =>
  Reveal.getHorizontalSlides().map(s => Array.from(s.querySelectorAll('.diagram svg')).filter(v => !v.closest('.frame[hidden]')).length).join(',')),
  '1,1,1,0,1,1,1,0,1,1,1');
eq('math rendered on slides 2, 5, 7', await ev(() =>
  [1, 4, 6].map(i => Reveal.getHorizontalSlides()[i].querySelectorAll('.katex').length > 0).join(',')), 'true,true,true');

console.log('-- point pairs (loops)');
for (const [i, id] of [[0, 'hero-title-frames'], [10, 'hero-end-frames']]) {
  await go(i); await wait(300);
  const seen = new Set();
  for (let k = 0; k < 12; k++) { seen.add(await page.evaluate(id => +(document.getElementById(id).dataset.phase || 0), id)); await wait(150); }
  check(`slide ${i + 1}: the pairs move`, seen.size >= 5, [...seen].join(','));
  const xs = await page.evaluate(id => { const a = document.getElementById(id); const at = t => { a._show(t); return Array.from(a.querySelectorAll(':scope > .frame circle')).map(c => +c.getAttribute('cx')); }; const r = [at(0), at(20), at(63.99)]; a._show(0); return r; }, id);
  check(`slide ${i + 1}: the loop closes (the end runs into the start) and the pairs have moved by tick 20`,
        xs[0].every((x, k) => Math.abs(x - xs[2][k]) < 1) && xs[0].some((x, k) => Math.abs(x - xs[1][k]) > 5), '');
  eq(`slide ${i + 1}: 26 pairs of two dots`, await page.evaluate(id => document.querySelectorAll(`#${id} > .frame circle`).length, id), 52);
}

console.log('-- marching arrows (loops)');
const cur = id => page.evaluate(id => +(document.getElementById(id).dataset.phase || 0), id);
for (const [i, id] of [[1, 'd-problem-frames'], [4, 'd-pipeline-frames']]) {
  await go(i); await wait(300);
  const seen = new Set();
  for (let k = 0; k < 16; k++) { seen.add(Math.floor(await cur(id))); await wait(60); }
  check(`slide ${i + 1}: the loop visits several of its 8 frames`, seen.size >= 4 && [...seen].every(f => f >= 0 && f < 8), [...seen].join(','));
  await go(0); await wait(100);
  const frozen = await cur(id); await wait(400);
  eq(`slide ${i + 1}: it stands still while the slide is not shown`, await cur(id), frozen);
}

// An animation is one drawing the page redraws from its events; a reveal step plays one act.
const shown = id => page.evaluate(id => {
  const f = document.querySelector(`#${id} > .frame`);
  return { text: Array.from(f.querySelectorAll('text')).map(e => e.textContent) };
}, id);
const press = async ms => { await ev(() => Reveal.nextFragment()); await wait(ms); };

console.log('-- steps over a loop');
// stages: 3 reveal steps (rests 2, 3, 4 ticks of one phase) under 8 phases of one tick each; the
// time shown is phase * 4 + (the step time within the phase)
const both = id => page.evaluate(id => { const a = document.getElementById(id); return { phase: Math.floor(+(a.dataset.phase || 0)), cur: +a.dataset.cur, phases: a.dataset.phases, rests: a.dataset.rests }; }, id);
await go(5); await wait(300);
const seenPhase = new Set();
const b0 = await both('d-stages-frames');
eq('slide 6: eight phases, steps rest at 2, 3, 4', [b0.phases, b0.rests], ['8', '[2,3,4]']);
for (let k = 0; k < 14; k++) { seenPhase.add((await both('d-stages-frames')).phase); await wait(60); }
check('slide 6: the loop runs under the steps', seenPhase.size >= 3, [...seenPhase].join(','));
await press(600);
const afterPress = await both('d-stages-frames');
check('slide 6: a step plays the first act (to tick 2)', afterPress.cur > 1.9 && afterPress.cur < 2, JSON.stringify(afterPress));
check('slide 6: and the loop keeps going', afterPress.phase !== (await (async () => { await wait(200); return (await both('d-stages-frames')).phase; })()) );
await go(0); await wait(100);

console.log('-- histogram (an animation)');
// (reveal shows every fragment of a slide reached from a later one)
await go(2); await wait(300);
eq('slide 3: starts empty', (await shown('bump-frames')).text[0], 'N = 0 events');
const heights = r => page.evaluate(r => Array.from(document.querySelectorAll(`#bump-frames > .frame ${r}`)).reduce((a, e) => a + +e.getAttribute('height'), 0), r);
eq('slide 3: no bars yet', await heights('.hist-bkg'), 0);
await press(2500);
eq('slide 3: one step fills it to 2500 events', (await shown('bump-frames')).text[0], 'N = 2500 events');
check('slide 3: background and signal drawn', (await heights('.hist-bkg')) > 0 && (await heights('.hist-sig')) > 0);

console.log('-- fragments');
await go(3);
eq('slide 4: one fragment (the callout)', await ev(() => Reveal.getCurrentSlide().querySelectorAll('.fragment').length), 1);

console.log('-- highlighting (animations)');
const lit = id => page.evaluate(id => document.querySelectorAll(`#${id} > .frame .node.on`).length, id);
await go(5); await wait(300);
const stages = [await lit('d-stages-frames')];
for (let i = 0; i < 3; i++) { await press(400); stages.push(await lit('d-stages-frames')); }
eq('slide 6: each step lights the next stage', stages, [0, 1, 1, 1]);
await go(6); await wait(300);
const chain = [await lit('d-chain-frames')];
for (let i = 0; i < 4; i++) { await press(400); chain.push(await lit('d-chain-frames')); }
eq('slide 7: the chain builds up', chain, [0, 1, 2, 3, 4]);

console.log('-- bars and counters (animations)');
await go(8); await wait(300);
eq('slide 9: starts at zero', (await shown('d-results-frames')).text.slice(1, 4), ['0.00', '0.00', '0.00']);
await press(2500);
eq('slide 9: counters reach the paper\'s numbers', (await shown('d-results-frames')).text.slice(1, 4), ['1.17', '0.35', '0.05']);
eq('slide 9: bars grown', await ev(() => Array.from(document.querySelectorAll('#d-results-frames > .frame :is(rect.b1, rect.b2, rect.b3)')).map(e => +e.getAttribute('height'))), [234, 70, 10]);
await go(9); await wait(300);
await press(2500);
eq('slide 10: counters reach their targets', (await ev(() =>
  Array.from(document.querySelectorAll('#d-tiles-frames > .frame text')).map(e => e.textContent))).filter(t => /^[≈0-9]/.test(t) && !/ /.test(t)), ['≈100×', '3–4×', '128', '0.004']);

console.log('-- closing slide');
await go(10); await wait(300);
check('slide 11: link', await ev(() => !!Reveal.getCurrentSlide().querySelector('a[href="https://arxiv.org/abs/2605.07972"]')));

eq('no page errors or failed loads', errors, []);
await browser.close();
console.log(failures === 0 ? 'all deck tests passed' : `${failures} failure(s)`);
process.exit(failures === 0 ? 0 : 1);
