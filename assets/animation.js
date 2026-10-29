// The animation player, shared by the reveal.js and the standalone backends (a deck loads it before
// its own script, which supplies how to tell that an animation's slide is shown and calls
// `sync`/`syncAll` when a fragment appears or the slide changes).
//
//   var player = SlidesAnimation(function (a) { return <is animation element `a`'s slide shown> });
//
// An animation (`.animation`, see `Slides.Backend.Animation`) ships the *event list* of its scene
// as JSON in its `script.events` child: {n: table of nodes, e: events}.  An event has an onset, a
// span, a driver and a leaf, the leaf a diagram whose scalars are expression trees over one variable;
// equal subtrees (of diagrams and terms) are one node of the table, referred to by the string of its
// position.  The page evaluates it at a real time `t` (in ticks):
// the events active at `t` are laid out at their parameter (the value of the driver at the event's
// local time, 0 without one), overlaid in the join of their frames, and drawn as SVG.  This is
// `Slides.Scene.Animation.frame`, once more, in JavaScript: the operations below are the Space,
// Time and Coupling signatures, and `lay` is `Slides.Diagram.Place`.  Tested against the frames
// Agda computes (`make test-anim-ref`).
//
//   scalar/driver term   null (the variable), a number, or [op, args...]:
//     [0,n,d] the fraction n/d  2 plus  3 max  4 minus  5 [5,a,b,x,y] x if a<=b else y
//     6 [6,p,a] p percent of a  7 hold (floor)  8 ratio  9 [9,r,a,b] a+r(b-a)  10 [10,e,a] easing
//     e of a (0 linear, 1 step, 2 step start, [x1,y1,x2,y2] a cubic Bezier in hundredths)
//   diagram              [op, ...] with op one of R S D T P _ b a @ l L p o n c (see `lay`)
//   style                {stroke, fill, cls, id, dash, anchor, sw, rx, op}
function SlidesAnimation(shown) {
  var SVGNS = 'http://www.w3.org/2000/svg';
  function fl(x) { return Math.floor(x + 1e-9); }
  function rat(x) { return typeof x === 'number' ? x : x[0] / x[1]; }
  // a cubic Bezier [x1, y1, x2, y2] in hundredths: the parameter with x(s) = r by 16 bisection steps
  function cubic(c1, c2, s) { var u = 1 - s; return 3 * u * u * s * c1 + 3 * u * s * s * c2 + s * s * s; }
  function ease(e, r) {
    if (e === 0) return r;
    if (e === 1) return r >= 1 ? 1 : 0;
    if (e === 2) return r <= 0 ? 0 : 1;
    if (r <= 0) return 0;
    if (r >= 1) return 1;
    var lo = 0, hi = 1, i;
    for (i = 0; i < 16; i++) { if (cubic(e[0] / 100, e[2] / 100, (lo + hi) / 2) <= r) lo = (lo + hi) / 2; else hi = (lo + hi) / 2; }
    return cubic(e[1] / 100, e[3] / 100, (lo + hi) / 2);
  }
  // a term or diagram that is shared is the string of its position in the table `TAB` (of the animation drawn)
  var TAB;
  function ev(e, v) {
    if (typeof e === 'string') e = TAB[e];
    if (e === null) return v;
    if (typeof e === 'number') return e;
    var o = e[0];
    if (o === 0) return e[1] / e[2];
    var a = ev(e[1], v);
    if (o === 7) return fl(a);
    if (o === 6) return ev(e[2], v) * e[1] / 100;
    if (o === 10) return ease(e[1], ev(e[2], v));
    var b = ev(e[2], v);
    switch (o) {
      case 2: return a + b;
      case 3: return Math.max(a, b);
      case 4: return a - b;
      case 5: return a <= b ? ev(e[3], v) : ev(e[4], v);
      case 8: return b === 0 ? 0 : a / b;
      case 9: return b + a * (ev(e[3], v) - b);
    }
    return 0;
  }
  // ---- layout: Slides.Diagram.Place (sizes in units, positions in half units)
  function sh(d, dx, dy) {
    var r = Object.assign({}, d);
    if (d.k === 'line' || d.k === 'arrow') { r.a += dx; r.b += dy; r.c += dx; r.d += dy; } else { r.x += dx; r.y += dy; }
    return r;
  }
  function inFrame(w, h, dx, dy, L) {
    return { w: w, h: h, ds: L.ds.map(function (d) { return sh(d, dx, dy); }),
             as: L.as.map(function (a) { return [a[0], { l: a[1].l + dx, t: a[1].t + dy, w: a[1].w, h: a[1].h }]; }) };
  }
  function overlay(w, h, A, B) { return { w: w, h: h, ds: A.ds.concat(B.ds), as: A.as.concat(B.as) }; }
  function combine(w, h, p, A, q, B) { return overlay(w, h, inFrame(w, h, p[0], p[1], A), inFrame(w, h, q[0], q[1], B)); }
  function prim(w, h, ds) { return { w: w, h: h, ds: ds, as: [] }; }
  function vOff(al, outer, inner) { return al === 0 ? 0 : al === 1 ? outer - inner : 2 * (outer - inner); }
  function ovl(A, B) { return overlay(Math.max(A.w, B.w), Math.max(A.h, B.h), A, B); }
  function point(port, b) {
    var s = typeof port === 'number' ? port : port[0], p = typeof port === 'number' ? 0 : port[1];
    var m = typeof port === 'number' || s === 4;
    // sides: 0 north 1 south 2 east 3 west 4 middle
    if (m) return s === 0 ? [b.l + b.w, b.t] : s === 1 ? [b.l + b.w, b.t + 2 * b.h] : s === 2 ? [b.l + 2 * b.w, b.t + b.h]
                : s === 3 ? [b.l, b.t + b.h] : [b.l + b.w, b.t + b.h];
    return s === 0 ? [b.l + p * 2 * b.w / 100, b.t] : s === 1 ? [b.l + p * 2 * b.w / 100, b.t + 2 * b.h]
         : s === 2 ? [b.l + 2 * b.w, b.t + p * 2 * b.h / 100] : [b.l, b.t + p * 2 * b.h / 100];
  }
  function find(as, n) { for (var i = 0; i < as.length; i++) if (as[i][0] === n) return as[i][1]; return null; }
  function lay(n, p) {
    if (typeof n === 'string') n = TAB[n];
    var o = n[0], x, y, A, B, w, h;
    switch (o) {
      case 'R': w = ev(n[1], p); h = ev(n[2], p); return prim(w, h, [{ k: 'rect', x: 0, y: 0, w: w, h: h, s: n[3] }]);
      case 'S': w = ev(n[1], p); h = ev(n[2], p); return prim(w, h, [{ k: 'line', a: 0, b: 0, c: 2 * w, d: 2 * h, s: n[3] }]);
      case 'D': x = ev(n[1], p); return prim(2 * x, 2 * x, [{ k: 'circle', x: 2 * x, y: 2 * x, r: x, s: n[2] }]);
      case 'T': w = ev(n[1], p); h = ev(n[2], p); return prim(w, h, [{ k: 'label', x: w, y: h, n: n[3], t: n[4], s: n[5] }]);
      case 'P': w = ev(n[1], p); h = ev(n[2], p); return prim(w, h, [{ k: 'path', x: 0, y: 0, d: n[3], s: n[4] }]);
      case '_': return prim(ev(n[1], p), ev(n[2], p), []);
      case 'b': A = lay(n[2], p); B = lay(n[3], p); h = Math.max(A.h, B.h);
        return combine(A.w + B.w, h, [0, vOff(n[1], h, A.h)], A, [2 * A.w, vOff(n[1], h, B.h)], B);
      case 'a': A = lay(n[2], p); B = lay(n[3], p); w = Math.max(A.w, B.w);
        return combine(w, A.h + B.h, [vOff(n[1], w, A.w), 0], A, [vOff(n[1], w, B.w), 2 * A.h], B);
      case '@': A = lay(n[1], p); B = lay(n[2], p); w = Math.max(A.w, B.w); h = Math.max(A.h, B.h);
        return combine(w, h, [w - A.w, h - A.h], A, [w - B.w, h - B.h], B);
      case 'l': A = lay(n[1], p); B = lay(n[2], p); w = Math.max(A.w, B.w);
        return combine(w, A.h + (B.h + A.h), [w - A.w, 0], A, [w - B.w, 2 * A.h], B);
      case 'L': A = lay(n[1], p); B = lay(n[2], p); w = Math.max(A.w, B.w);
        return combine(w, A.h + (B.h + A.h), [w - B.w, 2 * A.h], B, [w - A.w, 2 * (A.h + B.h)], A);
      case 'p': return inFrame(ev(n[1], p), ev(n[2], p), 2 * ev(n[3], p), 2 * ev(n[4], p), lay(n[5], p));
      case 'o': return overlay(ev(n[1], p), ev(n[2], p), lay(n[3], p), lay(n[4], p));
      case 'n': A = lay(n[2], p); return { w: A.w, h: A.h, ds: A.ds, as: [[n[1], { l: 0, t: 0, w: A.w, h: A.h }]].concat(A.as) };
      case 'c': A = lay(n[6], p);
        var ba = find(A.as, n[1]), bb = find(A.as, n[3]);
        if (!ba || !bb) return A;
        var pa = point(n[2], ba), pb = point(n[4], bb);
        return { w: A.w, h: A.h, ds: A.ds.concat([{ k: 'arrow', a: pa[0], b: pa[1], c: pb[0], d: pb[1], s: n[5] }]), as: A.as };
    }
    return prim(0, 0, []);
  }
  // ---- the frame at time t: events active at t, overlaid in order
  function frameAt(E, t) {
    var L = null;
    E.forEach(function (e) {
      var o = rat(e.o), s = e.s === null ? null : rat(e.s);
      if (o > t + 1e-9 || (s !== null && t >= o + s - 1e-9)) return;
      var p = e.d === null ? 0 : ev(e.d, t - o), F = lay(e.l, p);
      L = L === null ? F : ovl(L, F);
    });
    return L;
  }
  // ---- drawing: Slides.Diagram.Print
  function r3(x) { return String(Math.round(x * 1000) / 1000); }
  function el(tag, attrs, kids) {
    var e = document.createElementNS(SVGNS, tag);
    Object.keys(attrs).forEach(function (k) { e.setAttribute(k, attrs[k]); });
    (kids || []).forEach(function (c) { e.appendChild(c); });
    return e;
  }
  function common(s, a) {
    if (s.cls) a['class'] = s.cls;
    if (s.id) a.id = s.id;
    if (s.dash) a['stroke-dasharray'] = s.dash;
    if (s.op !== undefined) a.opacity = s.op + '%';
    return a;
  }
  function shape(s, a) {
    a.stroke = s.stroke || 'currentColor'; a.fill = s.fill || 'none';
    if (s.sw !== undefined) a['stroke-width'] = s.sw;
    return common(s, a);
  }
  function segs(t) {
    var out = [], acc = '', i = 0;
    function flush() { if (acc) out.push(['f', acc]); acc = ''; }
    function scripted(k) {
      i++; var u = '';
      if (t[i] === '{') { i++; while (i < t.length && t[i] !== '}') u += t[i++]; i++; } else if (i < t.length) u = t[i++];
      out.push([k, u]);
    }
    while (i < t.length) {
      var c = t[i];
      if (c === '\\' && i + 1 < t.length) { acc += t[i + 1]; i += 2; }
      else if (c === '_') { flush(); scripted('s'); }
      else if (c === '^') { flush(); scripted('u'); }
      else { acc += c; i++; }
    }
    flush();
    return out;
  }
  function draw(d, name) {
    var s = d.s || {}, a;
    switch (d.k) {
      case 'rect': a = { x: r3(d.x / 2), y: r3(d.y / 2), width: r3(d.w), height: r3(d.h) }; if (s.rx !== undefined) a.rx = s.rx;
        return el('rect', shape(s, a));
      case 'circle': return el('circle', shape(s, { cx: r3(d.x / 2), cy: r3(d.y / 2), r: r3(d.r) }));
      case 'line': return el('line', shape(s, { x1: r3(d.a / 2), y1: r3(d.b / 2), x2: r3(d.c / 2), y2: r3(d.d / 2) }));
      case 'arrow': a = shape(s, { x1: r3(d.a / 2), y1: r3(d.b / 2), x2: r3(d.c / 2), y2: r3(d.d / 2) });
        a['marker-end'] = 'url(#' + name + '-arrow)'; return el('line', a);
      case 'label':
        a = common(s, { x: r3(d.x / 2), y: r3(d.y / 2), 'font-size': d.n, 'text-anchor': s.anchor || 'middle',
                        'dominant-baseline': 'central', fill: s.fill || 'currentColor' });
        var sg = segs(d.t), e = el('text', a), pend = '';
        sg.forEach(function (g) {
          var t = document.createElementNS(SVGNS, 'tspan');
          if (g[0] === 'f') { if (pend) t.setAttribute('dy', pend); pend = ''; }
          else if (g[0] === 's') { t.setAttribute('font-size', Math.floor(d.n * 7 / 10)); t.setAttribute('dy', Math.floor(d.n / 4)); pend = '-' + Math.floor(d.n / 4); }
          else { t.setAttribute('font-size', Math.floor(d.n * 7 / 10)); t.setAttribute('dy', '-' + Math.floor(d.n / 3)); pend = String(Math.floor(d.n / 3)); }
          t.textContent = g[1] || ' ';
          if (sg.length > 1 || g[0] !== 'f') e.appendChild(t); else e.textContent = g[1] || ' ';
        });
        return e;
      case 'path': a = shape(s, { transform: 'translate(' + r3(d.x / 2) + ' ' + r3(d.y / 2) + ')' }); a.d = d.d; return el('path', a);
    }
    return el('g', {});
  }
  function paint(a, L) {
    var svg = a.querySelector(':scope > .frame svg'), name = a.id.replace(/-frames$/, '');
    while (svg.children.length > 1) svg.removeChild(svg.lastChild);
    if (L === null) { svg.setAttribute('viewBox', '0 0 0 0'); return; }
    svg.setAttribute('viewBox', '0 0 ' + r3(L.w) + ' ' + r3(L.h));
    L.ds.forEach(function (d) { svg.appendChild(draw(d, name)); });
  }
  // ---- the player
  function events(a) {
    if (!a._e) { var j = JSON.parse(a.querySelector(':scope > script.events').textContent); a._t = j.n; a._e = j.e; }
    return a._e;
  }
  function frame(a, t) { var E = events(a); TAB = a._t; paint(a, frameAt(E, t)); }
  function target(a) {
    var n = a.querySelectorAll('.anim-step.visible').length;
    if (n === 0) return 0;
    var r = JSON.parse(a.dataset.rests);
    // a step rests at the last instant of its act: at the rest itself the next act has begun
    return rat(r[Math.min(n, r.length) - 1]) - 1e-6;
  }
  // a loop shows the time `phase`; steps over a loop of `data-phases` phases show the step time
  // within the current phase (a phase is `duration / phases` ticks long)
  function draw1(a) {
    var loop = a.getAttribute('data-loop') !== null, n = +(a.dataset.phases || 0), cur = +(a.dataset.cur || 0);
    frame(a, !loop ? cur : n ? Math.floor(+(a.dataset.phase || 0)) * (+a.dataset.duration / n) + cur : +(a.dataset.phase || 0));
  }
  function show(a, t) { a.dataset.cur = String(t); draw1(a); }
  // one tick every `data-ms` milliseconds, on every animation frame
  function sync(a, jump) {
    if (!a) return;
    cancelAnimationFrame(a._raf);
    var t = target(a), ms = +a.dataset.ms, cur = +(a.dataset.cur || 0);
    if (jump || ms === 0 || t === cur) { show(a, t); return; }
    var t0 = null, c0 = cur;
    a._raf = requestAnimationFrame(function go(now) {
      if (t0 === null) t0 = now;
      cur = c0 + (t > c0 ? 1 : -1) * (now - t0) / ms;
      if (t > c0 ? cur >= t : cur <= t) cur = t;
      show(a, cur);
      if (cur !== t) a._raf = requestAnimationFrame(go);
    });
  }
  // a loop runs while its slide is shown: the phase is the real time in ticks modulo its duration;
  // it stands still while printing (see below)
  var printing = false;
  function spin(a) {
    var d = +(a.dataset.phases || a.dataset.duration), ms = Math.max(+a.dataset.ms, 1), t0 = null;
    requestAnimationFrame(function go(now) {
      if (!printing && shown(a)) {
        if (t0 === null) t0 = now;
        a.dataset.phase = String(d > 0 ? ((now - t0) / ms) % d : 0);
        draw1(a);
      } else t0 = null;
      requestAnimationFrame(go);
    });
  }
  // for tests: show time `t` directly
  document.querySelectorAll('.animation').forEach(function (a) { a._show = function (t) { frame(a, t); }; });
  document.querySelectorAll('.animation[data-loop]').forEach(spin);
  // printing shows every fragment, so show every animation at its last step, and stop the clocks
  // (a loop's timer and a step in flight would draw over it) until `afterprint`
  window.addEventListener('beforeprint', function () {
    printing = true;
    document.querySelectorAll('.animation').forEach(function (a) {
      cancelAnimationFrame(a._raf);
      a._printed = [a.dataset.cur, a.dataset.phase];
      var r = a.dataset.rests;
      a.dataset.cur = r ? String(rat(JSON.parse(r).pop()) - 1e-6) : '0';
      a.dataset.phase = '0';
      draw1(a);
    });
  });
  window.addEventListener('afterprint', function () {
    printing = false;
    document.querySelectorAll('.animation').forEach(function (a) {
      if (!a._printed) return;
      if (a._printed[1] !== undefined) a.dataset.phase = a._printed[1];
      sync(a, true);   // a step that was in flight is finished
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
