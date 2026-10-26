Reveal.initialize(Object.assign({"hash":true,"transition":"slide","slideNumber":true,"controls":true,"progress":true,"width":1280,"height":720}, {plugins: [RevealNotes, RevealHighlight, RevealMath.KaTeX]}));
(function () {
  var done = new WeakSet();
  function run(slide) {
    if (!slide) return;
    slide.querySelectorAll('.js[data-js]').forEach(function (e) {
      if (done.has(e)) return;
      done.add(e);
      try { new Function('slide', e.getAttribute('data-js'))(slide); }
      catch (x) { console.error(x); }
    });
  }
  Reveal.on('ready', function (e) { run(e.currentSlide); });
  Reveal.on('slidechanged', function (e) { run(e.currentSlide); });
})();
(function () {
  function target(a) {
    var n = a.querySelectorAll('.anim-step.visible').length;
    if (n === 0) return 0;
    var r = a.dataset.rests.split(',');
    return +r[Math.min(n, r.length) - 1];
  }
  function geom(a) {
    var n = a.querySelectorAll(':scope > .frame').length, v = a.getAttribute('data-loop');
    var p = v === null ? 1 : (v === '' ? n : +v);
    return { n: n, p: p, steps: n / p };
  }
  function draw(a) {
    var g = geom(a), i = (+(a.dataset.phase || 0)) * g.steps + (+(a.dataset.cur || 0));
    a.querySelectorAll(':scope > .frame').forEach(function (f, k) { f.hidden = (k !== i); });
  }
  function show(a, i) { a.dataset.cur = String(i); draw(a); }
  function sync(a, jump) {
    if (!a) return;
    clearInterval(a._timer);
    var t = target(a), ms = +a.dataset.ms, cur = +(a.dataset.cur || 0);
    if (jump || ms === 0 || t === cur) { show(a, t); return; }
    a._timer = setInterval(function () {
      cur += (t > cur ? 1 : -1);
      show(a, cur);
      if (cur === t) clearInterval(a._timer);
    }, ms);
  }
  function spin(a) {
    var p = geom(a).p, ms = Math.max(+a.dataset.ms, 16);
    setInterval(function () {
      if (p > 1 && a.closest('section').classList.contains('present')) {
        a.dataset.phase = String(((+(a.dataset.phase || 0)) + 1) % p);
        draw(a);
      }
    }, ms);
  }
  document.querySelectorAll('.animation[data-loop]').forEach(spin);
  function all(slide) { if (slide) slide.querySelectorAll('.animation').forEach(function (a) { sync(a, true); }); }
  Reveal.on('ready', function (e) { all(e.currentSlide); });
  Reveal.on('slidechanged', function (e) { all(e.currentSlide); });
  Reveal.on('fragmentshown', function (e) { sync(e.fragment.closest('.animation'), false); });
  Reveal.on('fragmenthidden', function (e) { sync(e.fragment.closest('.animation'), false); });
})();
Reveal.configure({center: false});
