// Drives the rendered showcase deck in a real browser: keyboard navigation,
// fragment stepping, configuration, and the standalone backend's navigation.
//
// usage: node run.mjs [outdir]      (default: ../../out)
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
const eq = (name, got, want) => check(name, got === want, `got ${JSON.stringify(got)}, want ${JSON.stringify(want)}`);

const browser = await chromium.launch({ executablePath: chrome, headless: true });

async function open(dir, ready) {
  const page = await browser.newPage({ viewport: { width: 1280, height: 800 } });
  const errors = [];
  page.on('pageerror', e => errors.push(e.message));
  await page.goto(pathToFileURL(path.join(out, dir, 'index.html')).href);
  await page.waitForSelector(ready, { timeout: 10000 });
  return { page, errors };
}

// ---------------------------------------------------------------- reveal.js
{
  const { page, errors } = await open('showcase', '.reveal.ready');
  const ev = f => page.evaluate(f);
  const idx = async () => ev(() => Reveal.getIndices());
  const visible = () => ev(() => Reveal.getCurrentSlide().querySelectorAll('.fragment.visible').length);
  const key = k => page.keyboard.press(k);

  console.log('-- reveal.js');
  eq('width from JSON number', await ev(() => Reveal.getConfig().width), 960);
  eq('height from JSON number', await ev(() => Reveal.getConfig().height), 700);
  eq('transition option', await ev(() => Reveal.getConfig().transition), 'fade');
  eq('slideNumber option', await ev(() => Reveal.getConfig().slideNumber), true);
  eq('horizontal slides', await ev(() => Reveal.getHorizontalSlides().length), 11);
  eq('total slides (stack counts twice)', await ev(() => Reveal.getTotalSlides()), 12);

  // `pause`: three blocks become fragments; notes do not.
  await ev(() => Reveal.slide(1));
  eq('pause: fragments on the slide', await ev(() => Reveal.getCurrentSlide().querySelectorAll('.fragment').length), 3);
  eq('pause: none visible at first', await visible(), 0);
  await key('ArrowRight'); eq('pause: step 1', await visible(), 1);
  await key('ArrowRight'); eq('pause: step 2', await visible(), 2);
  await key('ArrowRight'); eq('pause: step 3', await visible(), 3);
  await key('ArrowRight'); eq('pause: next key moves to the next slide', (await idx()).h, 2);
  await key('ArrowLeft');  eq('back: returns to the paused slide', (await idx()).h, 1);
  check('notes are not in a fragment',
        await ev(() => !document.querySelector('.fragment aside.notes') && !!document.querySelector('section aside.notes')));

  // explicit fragments
  await ev(() => Reveal.slide(2));
  eq('explicit fragments: count', await ev(() => Reveal.getCurrentSlide().querySelectorAll('.fragment').length), 4);
  check('explicit fragment style class', await ev(() => !!Reveal.getCurrentSlide().querySelector('.fragment.fade-up')));

  // typed math rendered by KaTeX
  await ev(() => Reveal.slide(3));
  check('math: KaTeX rendered display and inline formulas',
        await ev(() => Reveal.getCurrentSlide().querySelectorAll('.katex').length) >= 4);

  // marked-up text
  await ev(() => Reveal.slide(4));
  check('inline markup elements', await ev(() => {
    const s = Reveal.getCurrentSlide();
    return !!(s.querySelector('em') && s.querySelector('strong') && s.querySelector('p code') && s.querySelector('a[href]'));
  }));

  // resources
  await ev(() => Reveal.slide(5));
  check('figure and citations rendered', await ev(() => {
    const s = Reveal.getCurrentSlide();
    return !!s.querySelector('figure img[src="plot.svg"]') && s.querySelectorAll('.cite').length === 2;
  }));
  check('figure file loads', await ev(() => document.querySelector('figure img').complete && document.querySelector('figure img').naturalWidth > 0));

  // placed boxes (percent coordinates relative to the slide canvas)
  await ev(() => Reveal.slide(10));
  eq('placed: two boxes, one on a later step', await ev(() => {
    const s = Reveal.getCurrentSlide();
    return [s.querySelectorAll('.placed').length, s.querySelectorAll('.placed.fragment').length].join(',');
  }), '2,1');
  check('placed: box is at 10% / 50% of the slide canvas', await ev(() => {
    const c = document.querySelector('.slides').getBoundingClientRect();
    const b = Reveal.getCurrentSlide().querySelector('.placed').getBoundingClientRect();
    return Math.abs((b.left - c.left) / c.width - 0.10) < 0.01 && Math.abs((b.top - c.top) / c.height - 0.50) < 0.01;
  }));
  await key('ArrowRight');
  eq('placed: fragment appears on the first step', await ev(() => Reveal.getCurrentSlide().querySelectorAll('.placed.fragment.visible').length), 1);

  // background
  await ev(() => Reveal.slide(7));
  eq('slide background colour', await ev(() => getComputedStyle(document.querySelector('.slide-background.present')).backgroundColor), 'rgb(27, 58, 75)');

  // vertical stack
  await ev(() => Reveal.slide(8));
  eq('stack: starts at the top', (await idx()).v, 0);
  await key('ArrowDown'); eq('stack: down moves vertically', (await idx()).v, 1);
  eq('stack: transition attribute', await ev(() => document.querySelector('section.stack').getAttribute('data-transition')), 'zoom');
  // reveal.js updates the hash after a short delay
  check('url hash tracks the slide',
        await page.waitForFunction(() => location.hash === '#/8/1', null, { timeout: 5000 }).then(() => true, () => false));

  eq('no page errors', errors.length, 0);
  await page.close();
}

// ------------------------------------------------------------- standalone
{
  const { page, errors } = await open('showcase-plain', '.slide.active');
  const ev = f => page.evaluate(f);
  const active = () => ev(() => Array.from(document.querySelectorAll('.slide')).findIndex(s => s.classList.contains('active')));
  const visible = () => ev(() => document.querySelectorAll('.slide.active .fragment.visible').length);
  const key = k => page.keyboard.press(k);

  console.log('-- standalone HTML');
  eq('slides (stack flattened)', await ev(() => document.querySelectorAll('.slide').length), 12);
  eq('exactly one active slide', await ev(() => document.querySelectorAll('.slide.active').length), 1);
  eq('starts on the first slide', await active(), 0);
  await key('ArrowRight'); eq('right: next slide', await active(), 1);
  eq('hash is the slide number', await ev(() => location.hash), '#2');
  eq('pause: fragments hidden at first', await visible(), 0);
  await key('Space');      eq('pause: step 1', await visible(), 1);
  await key('ArrowRight'); eq('pause: step 2', await visible(), 2);
  await key('ArrowRight'); eq('pause: step 3', await visible(), 3);
  await key('ArrowRight'); eq('pause: then the next slide', await active(), 2);
  await key('ArrowLeft');  eq('back: previous slide with all fragments shown', [await active(), await visible()].join(','), '1,3');
  await key('ArrowLeft');  eq('back: unreveals the last fragment', await visible(), 2);
  await page.evaluate(() => { location.hash = '#12'; });
  await page.reload(); await page.waitForSelector('.slide.active');
  check('placed: box is at 10% / 50% of the window', await ev(() => {
    const b = document.querySelector('.slide.active .placed').getBoundingClientRect();
    return Math.abs(b.left / innerWidth - 0.10) < 0.01 && Math.abs(b.top / innerHeight - 0.50) < 0.01;
  }));
  eq('placed: fragment hidden then shown', [await visible(), (await key('Space'), await visible())].join(','), '0,1');
  await key('Home');
  await key('End');        eq('End: last slide', await active(), 11);
  await key('Home');       eq('Home: first slide', await active(), 0);
  check('background applied by the script', await (async () => {
    await page.evaluate(() => { location.hash = '#8'; });
    await page.reload(); await page.waitForSelector('.slide.active');
    return (await ev(() => document.body.style.background)).includes('rgb(27, 58, 75)');
  })());
  eq('no page errors', errors.length, 0);
  await page.close();
}

await browser.close();
console.log(failures === 0 ? 'all browser tests passed' : `${failures} failure(s)`);
process.exit(failures === 0 ? 0 : 1);
