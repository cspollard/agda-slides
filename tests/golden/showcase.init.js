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
      if (typeof it === 'number' && it < 0) { n -= it; return; }
      var el = kids[offset + n]; n++;
      if (it === 0) return;
      if (Array.isArray(it)) { it.forEach(function (v, j) { var k = NUMS[el.localName][j]; el.setAttribute(k, +el.getAttribute(k) + v); }); return; }
      if (typeof it === 'string') { parent.replaceChild(parse(it), el); return; }
      patch(el, it.g, 0);
    });
    while (kids.length > offset + n) parent.removeChild(kids[offset + n]);
    rest.forEach(function (s) { parent.appendChild(parse(s)); });
  }
  // A parametric animation (`data-param`, see `renderParamAnimation`): a formula is a number, a
  // string (the parameter of that segment, from `r`) or `[op, a, b]`; `["h", a]` is half of `a`,
  // positions being in half units.
  function ev(e, r) {
    if (typeof e === 'number') return e;
    if (typeof e === 'string') return r[+e];
    var o = e[0], x = ev(e[1], r);
    if (o === 'h') return Math.floor(x / 2);
    var y = ev(e[2], r);
    return o === '+' ? x + y : o === '-' ? Math.max(0, x - y) : o === 'm' ? Math.max(x, y) : Math.floor(x * y / 100);
  }
  // show tick `k`: swap in the elements of its phase, then set every number that depends on a parameter
  function pframe(a, k) {
    var P = a._p || (a._p = JSON.parse(a.dataset.param)), i = 0;
    while (i + 1 < P.p.length && P.p[i + 1].s <= k) i++;
    var svg = a.querySelector(':scope > .frame svg');
    if (a._ph !== i) {
      while (svg.children.length > 1) svg.removeChild(svg.lastChild);
      P.p[i].b.forEach(function (s) { svg.appendChild(parse(s)); });
      a._ph = i;
    }
    var r = P.v.map(function (v) { return v[1][k - v[0]] || 0; });
    P.p[i].c.forEach(function (cs, j) {
      if (cs === null) return;
      var el = svg.children[1 + j];
      cs.forEach(function (c, m) { if (c !== null) el.setAttribute(NUMS[el.localName][m], ev(c, r)); });
    });
  }
  // show frame `k`: rebuild from the first frame when going back, else apply the next edits
  function frame(a, k) {
    if (a.dataset.param) { pframe(a, k); return; }
    var d = a._d || (a._d = JSON.parse(a.dataset.deltas || '[]'));
    var svg = a.querySelector(':scope > .frame svg');
    if (!a._base) { a._base = svg.cloneNode(true); a._at = 0; }
    if (k < a._at) { var fresh = a._base.cloneNode(true); svg.parentNode.replaceChild(fresh, svg); svg = fresh; a._at = 0; }
    for (; a._at < k; a._at++) patch(svg, d[a._at], 1);
  }
  function geom(a) {
    var n = a.dataset.n ? +a.dataset.n : JSON.parse(a.dataset.deltas || '[]').length + 1, v = a.getAttribute('data-loop');
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
  document.querySelectorAll('.animation').forEach(function (a) { a._show = function (k) { frame(a, k); }; });
  document.querySelectorAll('.animation[data-loop]').forEach(spin);
  function all(slide) { if (slide) slide.querySelectorAll('.animation').forEach(function (a) { sync(a, true); }); }
  Reveal.on('ready', function (e) { all(e.currentSlide); });
  Reveal.on('slidechanged', function (e) { all(e.currentSlide); });
  Reveal.on('fragmentshown', function (e) { sync(e.fragment.closest('.animation'), false); });
  Reveal.on('fragmenthidden', function (e) { sync(e.fragment.closest('.animation'), false); });
})();
window.deckLoaded = true;
