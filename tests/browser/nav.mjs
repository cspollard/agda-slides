// Pins how a deck is NAVIGATED, end to end, in both browser backends.  This is the
// behaviour that Stage 1 of the legacy plan (plan/Unify.md in ../agda-slides-legacy) ports onto `Nav` commands bound by a backend
// (`Supports`); the port must leave every assertion here unchanged (../agda-slides-legacy/docs/NavInventory.md).
//
// Commands exercised (Nav = next | prev | goto n | first | last, plus fragment steps):
//   reveal : ArrowRight/ArrowDown/Space/PageDown (next), ArrowLeft/ArrowUp/Shift+Space/PageUp
//            (prev), Home (first), End (last), `#/h[/v]` in the URL (goto, on load and by
//            hashchange), `o`/Escape (overview), the Reveal.next()/prev() API;
//   plain  : ArrowRight/ArrowDown/Space/PageDown, ArrowLeft/ArrowUp/PageUp, Home, End,
//            `#n` on load (assets/plain.js has no buttons and no hashchange handler).
// After each command it asserts which slide is shown and how many fragments are visible.
// A deck is also walked end to end and the traces of the two backends are compared.
//
// usage: node tests/browser/nav.mjs [outdir]    (default: ../../out)
// Needs `make REVEAL=... example talk plain showcase` first.  Set CHROME to override the browser.

import { chromium } from 'playwright-core';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const out = path.resolve(process.argv[2] ?? path.join(here, '..', '..', 'out'));
const chrome = process.env.CHROME ?? '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'ok  ' : 'FAIL'} ${name}${ok ? '' : `  (${detail})`}`);
  if (!ok) failures++;
}
const eq = (name, got, want) =>
  check(name, JSON.stringify(got) === JSON.stringify(want), `got ${JSON.stringify(got)}, want ${JSON.stringify(want)}`);

const browser = await chromium.launch({ executablePath: chrome, headless: true });

async function open(dir, ready, hash = '') {
  const page = await browser.newPage({ viewport: { width: 1280, height: 800 } });
  const errors = [];
  page.on('pageerror', e => errors.push(e.message));
  await page.goto(pathToFileURL(path.join(out, dir, 'index.html')).href + hash);
  await page.waitForSelector(ready, { timeout: 10000 });
  return { page, errors };
}

// ---- reveal ---------------------------------------------------------------------------
// state: [flat leaf-slide index, visible fragments on it]; leaf = a slide that is not a stack
const revealState = page => page.evaluate(() => {
  const leaves = Array.from(document.querySelectorAll('.slides section')).filter(s => !s.querySelector(':scope > section'));
  const cur = Reveal.getCurrentSlide();
  return [leaves.indexOf(cur), cur.querySelectorAll('.fragment.visible').length];
});
const revealHV = page => page.evaluate(() => { const i = Reveal.getIndices(); return [i.h, i.v]; });

// the shape of a deck: fragments per leaf slide
const revealShape = page => page.evaluate(() =>
  Array.from(document.querySelectorAll('.slides section')).filter(s => !s.querySelector(':scope > section'))
    .map(s => s.querySelectorAll('.fragment').length));
const plainShape = page => page.evaluate(() =>
  Array.from(document.querySelectorAll('.slide')).map(s => s.querySelectorAll('.fragment').length));
const plainState = page => page.evaluate(() => {
  const ss = Array.from(document.querySelectorAll('.slide'));
  const i = ss.findIndex(s => s.classList.contains('active'));
  return [i, ss[i].querySelectorAll('.fragment.visible').length];
});

// press `key` until the state stops changing (at most `limit` times); the trace of states
async function walk(page, key, state, limit = 400) {
  const trace = [await state(page)];
  for (let n = 0; n < limit; n++) {
    await page.keyboard.press(key);
    const s = await state(page);
    if (JSON.stringify(s) === JSON.stringify(trace[trace.length - 1])) return trace;
    trace.push(s);
  }
  throw new Error('walk did not terminate');
}

// the trace that a deck of this shape must have going forward: each slide enters with no
// fragment shown, then shows them one at a time
const expectedForward = shape => shape.flatMap((n, i) => Array.from({ length: n + 1 }, (_, k) => [i, k]));

console.log('-- reveal.js: showcase');
let revealTrace;
{
  const { page, errors } = await open('showcase', '.reveal.ready');
  const key = k => page.keyboard.press(k);
  const hv = () => revealHV(page);
  const st = () => revealState(page);
  const fragLog = () => page.evaluate(() => window.__navlog.splice(0));
  await page.evaluate(() => {
    window.__navlog = [];
    for (const e of ['slidechanged', 'fragmentshown', 'fragmenthidden'])
      Reveal.on(e, () => window.__navlog.push(e));
  });

  eq('starts on the first slide', await hv(), [0, 0]);
  await key('ArrowLeft'); eq('prev at the first slide: stays', await hv(), [0, 0]);

  // next / prev through the fragments of a `pause` slide (slide 1: one fragment, the chunk after the pause)
  await key('ArrowRight'); eq('ArrowRight: slide 1, nothing shown', await st(), [1, 0]);
  eq('events: slide change', await fragLog(), ['slidechanged']);
  await key('ArrowRight'); eq('ArrowRight: fragment 1', await st(), [1, 1]);
  eq('events: one fragmentshown per step', await fragLog(), ['fragmentshown']);
  await key('ArrowRight'); eq('ArrowRight: next slide', await st(), [2, 0]);
  eq('events: slide change', await fragLog(), ['slidechanged']);
  await key('ArrowLeft');  eq('ArrowLeft: back to slide 1 with every fragment shown', await st(), [1, 1]);
  await key('ArrowLeft');  eq('ArrowLeft: hides the last fragment', await st(), [1, 0]);
  eq('events: slidechanged then fragmenthidden', await fragLog(), ['slidechanged', 'fragmenthidden']);
  await key('ArrowLeft');  eq('ArrowLeft: slide 0', await st(), [0, 0]);

  // the other next/prev keys
  await key('ArrowDown');   eq('ArrowDown on a horizontal slide (no stack): does nothing', await st(), [0, 0]);
  await key('ArrowUp');     eq('ArrowUp on a horizontal slide: does nothing', await st(), [0, 0]);
  await key('Space');       eq('Space: next', await st(), [1, 0]);
  await key('PageDown');    eq('PageDown: next (fragment)', await st(), [1, 1]);
  await key('PageUp');      eq('PageUp: prev (fragment)', await st(), [1, 0]);
  await key('Shift+Space'); eq('Shift+Space: prev', await st(), [0, 0]);

  // the API commands agree with the keys
  await page.evaluate(() => Reveal.next());
  await page.evaluate(() => Reveal.next());
  eq('Reveal.next() steps like ArrowRight', await st(), [1, 1]);
  await page.evaluate(() => Reveal.prev());
  eq('Reveal.prev() steps like ArrowLeft', await st(), [1, 0]);
  await page.evaluate(() => Reveal.nextFragment());
  eq('Reveal.nextFragment()', await st(), [1, 1]);
  await page.evaluate(() => Reveal.prevFragment());
  eq('Reveal.prevFragment()', await st(), [1, 0]);

  // first / last
  await key('End');   eq('End: last slide', await hv(), [13, 0]);
  await key('ArrowRight'); eq('next at the last slide: stays', await hv(), [13, 0]);
  await key('Home');  eq('Home: first slide', await hv(), [0, 0]);
  await key('ArrowRight'); await key('ArrowRight'); await key('ArrowRight');
  await key('Home');  eq('Home from the middle of a slide: first slide, nothing shown', await st(), [0, 0]);

  // goto: the URL hash is `#/h[/v]`, zero-based, handled by reveal on load and on hashchange
  await page.evaluate(() => { location.hash = '#/5'; });
  await page.waitForFunction(() => Reveal.getIndices().h === 5, null, { timeout: 5000 });
  eq('hashchange #/5: slide 5', await hv(), [5, 0]);
  await page.evaluate(() => { location.hash = '#/8/1'; });
  await page.waitForFunction(() => Reveal.getIndices().v === 1, null, { timeout: 5000 });
  eq('hashchange #/8/1: second slide of the stack', await hv(), [8, 1]);
  await page.evaluate(() => { location.hash = '#/1'; });
  await page.waitForFunction(() => Reveal.getIndices().h === 1, null, { timeout: 5000 });
  eq('hashchange #/1 (backwards): the target shows all its fragments', await st(), [1, 1]);

  // a vertical stack (slide 8, two slides)
  await page.evaluate(() => Reveal.slide(8, 0));
  eq('stack: top', await hv(), [8, 0]);
  await key('ArrowDown');  eq('ArrowDown: down the stack', await hv(), [8, 1]);
  await key('ArrowDown');  eq('ArrowDown at the bottom: stays', await hv(), [8, 1]);
  await key('ArrowUp');    eq('ArrowUp: up the stack', await hv(), [8, 0]);
  await key('Space');      eq('Space (next) goes down the stack first', await hv(), [8, 1]);
  await key('Space');      eq('Space past the bottom: next horizontal slide', await hv(), [9, 0]);
  await key('Shift+Space'); eq('Shift+Space (prev) returns to the bottom of the stack', await hv(), [8, 1]);
  await key('ArrowRight'); eq('ArrowRight from inside a stack: next horizontal slide', await hv(), [9, 0]);

  // overview
  await key('o');
  check('o: overview opens', await page.waitForFunction(() => Reveal.isOverview(), null, { timeout: 5000 }).then(() => true, () => false));
  await key('Escape');
  check('Escape: overview closes', await page.waitForFunction(() => !Reveal.isOverview(), null, { timeout: 5000 }).then(() => true, () => false));
  eq('overview round trip keeps the slide', await hv(), [9, 0]);
  await key('o');
  await page.waitForFunction(() => Reveal.isOverview(), null, { timeout: 5000 });
  await key('ArrowRight'); await key('Enter');
  check('overview: arrow then Enter selects the neighbour',
        await page.waitForFunction(() => !Reveal.isOverview() && Reveal.getIndices().h === 10, null, { timeout: 5000 }).then(() => true, () => false));

  // the animation slide: its steps are fragments, stepped by the same keys; the player is
  // synced from the fragment events (assets/animation.js via `animationSync`)
  await page.evaluate(() => Reveal.slide(Reveal.getHorizontalSlides().findIndex(s => s.querySelector('.animation'))));
  const anim = await page.evaluate(() => {
    const a = document.querySelector('section.present .animation');
    return { id: a.id, rests: JSON.parse(a.dataset.rests), steps: a.querySelectorAll('.anim-step').length };
  });
  eq('animation: one fragment per step', anim.steps, anim.rests.length);
  const cur = () => page.evaluate(id => +document.getElementById(id).dataset.cur, anim.id);
  eq('animation: rests on frame 0 on entering', await cur(), 0);
  for (let i = 0; i < anim.steps; i++) await key('ArrowRight');
  check('animation: plays to the last rest after all steps',
        await page.waitForFunction(([id, r]) => Math.round(+document.getElementById(id).dataset.cur) === r, [anim.id, anim.rests.at(-1)], { timeout: 8000 }).then(() => true, () => false),
        `cur=${await cur()}`);
  await key('ArrowLeft');
  check('animation: ArrowLeft plays back to the previous rest',
        await page.waitForFunction(([id, r]) => Math.round(+document.getElementById(id).dataset.cur) === r, [anim.id, anim.rests.at(-2) ?? 0], { timeout: 8000 }).then(() => true, () => false),
        `cur=${await cur()}`);

  // whole-deck walks with Space / Shift+Space
  await page.evaluate(() => Reveal.slide(0, 0, -1));
  const shape = await revealShape(page);
  revealTrace = await walk(page, 'Space', st);
  eq('Space walk visits every slide and fragment once, in order', revealTrace, expectedForward(shape));
  const back = await walk(page, 'Shift+Space', st);
  eq('Shift+Space walk is the forward walk reversed', back, revealTrace.slice().reverse());

  eq('no page errors', errors.length, 0);
  await page.close();
}

// goto on load: `index.html#/h`
{
  const { page, errors } = await open('showcase', '.reveal.ready', '#/6');
  eq('load with #/6: slide 6', await revealHV(page), [6, 0]);
  eq('no page errors', errors.length, 0);
  await page.close();
}

// ---- plain ----------------------------------------------------------------------------
console.log('-- standalone: showcase-plain');
let plainTrace;
{
  const { page, errors } = await open('showcase-plain', '.slide.active');
  const key = k => page.keyboard.press(k);
  const st = () => plainState(page);
  const hash = () => page.evaluate(() => location.hash);
  const bar = () => page.evaluate(() => document.querySelector('.progress').style.width);

  eq('starts on the first slide', await st(), [0, 0]);
  eq('start: hash is #1', await hash(), '#1');
  check('no buttons or links to navigate with', await page.evaluate(() => document.querySelectorAll('button, [onclick], nav, a[href^="#"]').length === 0));
  await key('ArrowLeft'); eq('prev at the first slide: stays', await st(), [0, 0]);

  await key('ArrowRight'); eq('ArrowRight: slide 1', await st(), [1, 0]);
  eq('hash follows the slide', await hash(), '#2');
  await key('ArrowRight'); eq('ArrowRight: fragment 1', await st(), [1, 1]);
  await key('PageDown');   eq('PageDown: next slide', await st(), [2, 0]);
  eq('hash follows the slide (2)', await hash(), '#3');
  await key('ArrowLeft');  eq('ArrowLeft: slide 1 with every fragment shown', await st(), [1, 1]);
  await key('ArrowLeft');  eq('ArrowLeft: hides the last fragment', await st(), [1, 0]);
  await key('ArrowLeft');  eq('ArrowLeft: slide 0', await st(), [0, 0]);
  eq('hash follows going back', await hash(), '#1');
  check('progress bar at the first slide', Math.abs(parseFloat(await bar()) - 100 / 15) < 1e-3, await bar());

  await key('End');  eq('End: last slide', await st(), [14, 0]);
  eq('hash at the last slide', await hash(), '#15');
  eq('progress bar at the last slide', await bar(), '100%');
  await key('ArrowRight'); eq('next at the last slide: stays', await st(), [14, 0]);
  await key('Home'); eq('Home: first slide', await st(), [0, 0]);
  await key('ArrowRight'); await key('ArrowRight'); await key('ArrowRight');
  await key('Home'); eq('Home from the middle of a slide: first slide, nothing shown', await st(), [0, 0]);
  eq('Home hides the fragments again on the slide it jumps to (and re-entering resets)',
     (await key('ArrowRight'), await st()), [1, 0]);
  await key('Control+ArrowRight');
  eq('Control+ArrowRight is next in plain (plain.js checks no modifiers)', await st(), [1, 1]);
  await key('Control+ArrowLeft');
  // plain.js ignores modifiers: Shift+Space is `next` here, but `prev` in reveal (pinned divergence)
  eq('Shift+Space is next in plain (reveal: prev)', (await key('Shift+Space'), await st()), [1, 1]);
  eq('letter keys are not bound in plain', (await key('o'), await key('n'), await st()), [1, 1]);

  // hashchange is NOT handled by plain.js (it reads the hash once, on load): pinned as it is today
  await page.evaluate(() => { location.hash = '#7'; });
  await page.waitForTimeout(300);
  eq('hashchange is ignored after load (current behaviour)', await st(), [1, 1]);

  // whole-deck walk
  await key('Home');
  const shape = await plainShape(page);
  plainTrace = await walk(page, 'Space', st);
  eq('Space walk visits every slide and fragment once, in order', plainTrace, expectedForward(shape));
  const back = await walk(page, 'ArrowLeft', st);
  eq('ArrowLeft walk is the forward walk reversed', back, plainTrace.slice().reverse());
  eq('no page errors', errors.length, 0);
  await page.close();
}

// goto on load: `index.html#n` is one-based
{
  const { page, errors } = await open('showcase-plain', '.slide.active', '#7');
  eq('load with #7: slide 7 (one-based)', await plainState(page), [6, 0]);
  eq('hash is normalised to the same', await page.evaluate(() => location.hash), '#7');
  await page.close();
  const p2 = await open('showcase-plain', '.slide.active', '#99');
  eq('load with #99: clamped to the last slide', await plainState(p2.page), [14, 0]);
  await p2.page.close();
  const p3 = await open('showcase-plain', '.slide.active', '#nonsense');
  eq('load with a bad hash: first slide', await plainState(p3.page), [0, 0]);
  await p3.page.close();
  eq('no page errors', errors.length, 0);
}

// ---- the two backends agree -------------------------------------------------------------
console.log('-- backends agree');
eq('reveal and plain showcase: same navigation trace', revealTrace, plainTrace);
for (const [r, p, name] of [['talk', 'plain', 'talk'], ['intro', null, 'intro']]) {
  const a = await open(r, '.reveal.ready');
  const ra = await walk(a.page, 'Space', revealState.bind(null));
  const sh = await revealShape(a.page);
  eq(`${name} (reveal): Space walk = slides and fragments in order`, ra, expectedForward(sh));
  eq(`${name} (reveal): no page errors`, a.errors.length, 0);
  await a.page.close();
  if (p) {
    const b = await open(p, '.slide.active');
    const rb = await walk(b.page, 'Space', plainState);
    eq(`${name} (plain): same trace as reveal`, rb, ra);
    eq(`${name} (plain): no page errors`, b.errors.length, 0);
    await b.page.close();
  }
}
// the lowered / still variants navigate like the full deck, minus the steps of animations
for (const d of ['showcase-lowered', 'showcase-still']) {
  const b = await open(d, '.slide.active');
  // lowering drops the animation's steps (they are stills / placeholders), nothing else
  const shape = await plainShape(b.page);
  const fullShape = await (async () => { const f = await open('showcase-plain', '.slide.active'); const x = await plainShape(f.page); await f.page.close(); return x; })();
  eq(`${d}: same slides`, shape.length, fullShape.length);
  check(`${d}: fragments only removed`, shape.every((n, i) => n <= fullShape[i]), JSON.stringify([shape, fullShape]));
  eq(`${d}: Space walk visits every slide and fragment once`, await walk(b.page, 'Space', plainState), expectedForward(shape));
  await b.page.close();
}

await browser.close();
console.log(failures === 0 ? 'all navigation tests passed' : `${failures} failure(s)`);
process.exit(failures === 0 ? 0 : 1);
