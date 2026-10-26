Reveal.initialize(Object.assign({"hash":true,"transition":"fade","slideNumber":true,"controls":true,"progress":true,"width":960,"height":700}, {plugins: [RevealNotes, RevealHighlight, RevealMath.KaTeX]}));
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
  var SVGNS = 'http://www.w3.org/2000/svg';
  var NUMS = { rect: ['x', 'y', 'width', 'height'], circle: ['cx', 'cy', 'r'], line: ['x1', 'y1', 'x2', 'y2'], text: ['x', 'y'] };
  function parse(s) {
    return document.importNode(new DOMParser().parseFromString(s, 'image/svg+xml').documentElement.firstChild, true);
  }
  // apply a list of edits to the children of `parent` (skipping `offset` of them)
  function patch(parent, items, offset) {
    var kids = parent.children, n = 0, rest = [];
    items.forEach(function (it) {
      if (it !== null && typeof it === 'object' && !Array.isArray(it) && 'r' in it) { rest = it.r; return; }
      var el = kids[offset + n]; n++;
      if (it === 0) return;
      if (Array.isArray(it)) { NUMS[el.localName].forEach(function (k, j) { el.setAttribute(k, it[j]); }); return; }
      if (typeof it === 'string') { parent.replaceChild(parse(it), el); return; }
      patch(el, it.g, 0);
    });
    while (kids.length > offset + n) parent.removeChild(kids[offset + n]);
    rest.forEach(function (s) { parent.appendChild(parse(s)); });
  }
  // show frame `k`: rebuild from the first frame when going back, else apply the next edits
  function frame(a, k) {
    var d = a._d || (a._d = JSON.parse(a.dataset.deltas || '[]'));
    var svg = a.querySelector(':scope > .frame svg');
    if (!a._base) { a._base = svg.cloneNode(true); a._at = 0; }
    if (k < a._at) { var fresh = a._base.cloneNode(true); svg.parentNode.replaceChild(fresh, svg); svg = fresh; a._at = 0; }
    for (; a._at < k; a._at++) patch(svg, d[a._at], 1);
  }
  function geom(a) {
    var n = JSON.parse(a.dataset.deltas || '[]').length + 1, v = a.getAttribute('data-loop');
    var p = v === null ? 1 : (v === '' ? n : +v);
    return { n: n, p: p, steps: n / p };
  }
  function draw(a) {
    var g = geom(a);
    frame(a, (+(a.dataset.phase || 0)) * g.steps + (+(a.dataset.cur || 0)));
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
window.deckLoaded = true;
