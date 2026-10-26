// The animation player, shared by the reveal.js and the standalone backends (a deck
// loads it before its own script, which supplies how to tell that an animation's slide is
// shown and calls `sync`/`syncAll` when a fragment appears or the slide changes).
//
//   var player = SlidesAnimation(function (a) { return <is animation element `a`'s slide shown> });
//
// An animation (`.animation`, see `renderAnimation` in `Slides.Backend.Diagram`) shows the
// first frame and rebuilds the others from the edits in `data-deltas`, or, with
// `data-param`, evaluates its tracks and formulas at a real time.
function SlidesAnimation(shown) {
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
  // A parametric animation (`data-param`, see `renderParamAnimation`) is a small simulator: the
  // tracks of its segments and symbolic layouts, evaluated at the real time `t` (in ticks) and
  // drawn without rounding.  An easing `e` is 0 (linear), 1 (step), 2 (step start) or a cubic
  // Bezier [x1, y1, x2, y2] in hundredths, as in `Slides.Anim.Track.progress`: the curve
  // parameter with x(s) = p is found by 16 bisection steps.
  function cubic(c1, c2, s) { var u = 1 - s; return 3 * u * u * s * c1 + 3 * u * s * s * c2 + s * s * s; }
  function ease(e, p) {
    if (e === 0) return p;
    if (e === 1) return p >= 1 ? 1 : 0;
    if (e === 2) return p <= 0 ? 0 : 1;
    if (p <= 0) return 0;
    if (p >= 1) return 1;
    var lo = 0, hi = 1, i;
    for (i = 0; i < 16; i++) { if (cubic(e[0] / 100, e[2] / 100, (lo + hi) / 2) <= p) lo = (lo + hi) / 2; else hi = (lo + hi) / 2; }
    return cubic(e[1] / 100, e[3] / 100, (lo + hi) / 2);
  }
  function rat(x) { return typeof x === 'number' ? x : x[0] / x[1]; }
  // a segment's parameter `u` ticks after its start: its pieces [ticks, from, to, easing] in
  // order, the last holding its end value
  function track(ps, u) {
    for (var i = 0; i < ps.length; i++) {
      var d = ps[i][0];
      if (u < d || i === ps.length - 1) {
        var a = rat(ps[i][1]), b = rat(ps[i][2]);
        return a + ease(ps[i][3], u < d ? u / d : 1) * (b - a);
      }
      u -= d;
    }
    return 0;
  }
  // a formula: a number, a string (the parameter of that segment, from `r`) or `[op, a, b]`;
  // `["h", a]` is half of `a`, positions being in half units
  function ev(e, r) {
    if (typeof e === 'number') return e;
    if (typeof e === 'string') return r[+e];
    var o = e[0], x = ev(e[1], r);
    if (o === 'h') return x / 2;
    var y = ev(e[2], r);
    return o === '+' ? x + y : o === '-' ? x - y : o === 'm' ? Math.max(x, y) : x * y / 100;
  }
  // show time `t`: swap in the elements of the phase of tick `floor(t)`, then set every number
  // that depends on a parameter
  function pframe(a, t) {
    var P = a._p || (a._p = JSON.parse(a.dataset.param)), i = 0;
    var k = Math.max(0, Math.min(Math.floor(t), +a.dataset.n - 1));
    while (i + 1 < P.p.length && P.p[i + 1].s <= k) i++;
    var svg = a.querySelector(':scope > .frame svg');
    if (a._ph !== i) {
      while (svg.children.length > 1) svg.removeChild(svg.lastChild);
      P.p[i].b.forEach(function (s) { svg.appendChild(parse(s)); });
      a._ph = i;
    }
    var r = P.v.map(function (v) { return track(v[1], t - v[0]); });
    P.p[i].c.forEach(function (cs, j) {
      if (cs === null) return;
      var el = svg.children[1 + j];
      cs.forEach(function (c, m) { if (c !== null) el.setAttribute(NUMS[el.localName][m], ev(c, r)); });
    });
  }
  // show frame `k` (a real time for a parametric animation): rebuild from the first frame when
  // going back, else apply the next edits
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
    cancelAnimationFrame(a._raf);
    var t = target(a), ms = +a.dataset.ms, cur = +(a.dataset.cur || 0);
    if (jump || ms === 0 || t === cur) { show(a, t); return; }
    if (a.dataset.param) {
      // continuous time: one tick every `ms` milliseconds, on every animation frame
      var t0 = null, c0 = cur;
      a._raf = requestAnimationFrame(function go(now) {
        if (t0 === null) t0 = now;
        cur = c0 + (t > c0 ? 1 : -1) * (now - t0) / ms;
        if (t > c0 ? cur >= t : cur <= t) cur = t;
        show(a, cur);
        if (cur !== t) a._raf = requestAnimationFrame(go);
      });
      return;
    }
    a._timer = setInterval(function () {
      cur += (t > cur ? 1 : -1);
      show(a, cur);
      if (cur === t) clearInterval(a._timer);
    }, ms);
  }
  function spin(a) {
    var p = geom(a).p, ms = Math.max(+a.dataset.ms, 16);
    if (a.dataset.param) {
      // continuous time: the phase is the real time in ticks, modulo the length of the loop
      var t0 = null;
      requestAnimationFrame(function go(now) {
        if (p > 1 && shown(a)) {
          if (t0 === null) t0 = now;
          a.dataset.phase = String(((now - t0) / Math.max(+a.dataset.ms, 1)) % p);
          draw(a);
        } else t0 = null;
        requestAnimationFrame(go);
      });
      return;
    }
    setInterval(function () {
      if (p > 1 && shown(a)) {
        a.dataset.phase = String(((+(a.dataset.phase || 0)) + 1) % p);
        draw(a);
      }
    }, ms);
  }
  // for tests: show frame `k` directly
  document.querySelectorAll('.animation').forEach(function (a) { a._show = function (k) { frame(a, k); }; });
  document.querySelectorAll('.animation[data-loop]').forEach(spin);
  // printing shows every fragment, so show every animation at its last step
  window.addEventListener('beforeprint', function () {
    document.querySelectorAll('.animation').forEach(function (a) {
      a._printed = [a.dataset.cur, a.dataset.phase];
      var r = a.dataset.rests;
      a.dataset.cur = r ? r.split(',').pop() : '0';
      a.dataset.phase = '0';
      draw(a);
    });
  });
  window.addEventListener('afterprint', function () {
    document.querySelectorAll('.animation').forEach(function (a) {
      if (!a._printed) return;
      a.dataset.cur = a._printed[0] || '0';
      if (a._printed[1] !== undefined) a.dataset.phase = a._printed[1];
      draw(a);
    });
  });
  return {
    // `sync(a, jump)`: bring animation `a` to the step its fragments are at
    sync: sync,
    // `syncAll(slide, jump)`: the same for every animation of a slide
    syncAll: function (slide, jump) {
      if (slide) slide.querySelectorAll('.animation').forEach(function (a) { sync(a, jump); });
    }
  };
}
