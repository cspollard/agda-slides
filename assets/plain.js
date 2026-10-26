// Minimal navigation for the standalone HTML backend: arrow keys / space
// step through fragments and slides; the slide number lives in the URL hash.
// It also plays animations.
(function () {
  var slides = Array.prototype.slice.call(document.querySelectorAll('.slide'));
  var bar = document.querySelector('.progress');
  var current = 0;

  function fragments(slide) {
    return Array.prototype.slice.call(slide.querySelectorAll('.fragment'));
  }

  // `script` commands: run once, the first time their slide is shown
  var ran = [];
  function runScripts(slide) {
    Array.prototype.forEach.call(slide.querySelectorAll('.js[data-js]'), function (e) {
      if (ran.indexOf(e) >= 0) return;
      ran.push(e);
      try { new Function('slide', e.getAttribute('data-js'))(slide); }
      catch (x) { console.error(x); }
    });
  }

  // Animations (`.animation`, see `renderAnimation`): the same player as the
  // reveal.js backend's `animationSync`.  The step is the number of visible
  // `.anim-step` fragments; the page moves one frame per `data-ms` towards the
  // frame that step rests on, and a `data-loop` animation also advances a phase
  // every `data-ms` while its slide is shown (frame = phase * steps + step).  A frame is rebuilt from the first one by the
  // edits in `data-deltas` (see `renderAnimation`).
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
  function target(a) {
    var n = a.querySelectorAll('.anim-step.visible').length;
    if (n === 0) return 0;
    var r = a.dataset.rests.split(',');
    return +r[Math.min(n, r.length) - 1];
  }
  function sync(a, jump) {
    clearInterval(a._timer);
    var t = target(a), ms = +a.dataset.ms, cur = +(a.dataset.cur || 0);
    function at(i) { a.dataset.cur = String(i); draw(a); }
    if (jump || ms === 0 || t === cur) { at(t); return; }
    a._timer = setInterval(function () {
      cur += (t > cur ? 1 : -1);
      at(cur);
      if (cur === t) clearInterval(a._timer);
    }, ms);
  }
  function syncAll(slide, jump) {
    Array.prototype.forEach.call(slide.querySelectorAll('.animation'), function (a) { sync(a, jump); });
  }
  Array.prototype.forEach.call(document.querySelectorAll('.animation[data-loop]'), function (a) {
    var p = geom(a).p, ms = Math.max(+a.dataset.ms, 16);
    setInterval(function () {
      if (p > 1 && a.closest('.slide').classList.contains('active')) {
        a.dataset.phase = String(((+(a.dataset.phase || 0)) + 1) % p);
        draw(a);
      }
    }, ms);
  });
  // printing shows every fragment, so show every animation at its last step
  window.addEventListener('beforeprint', function () {
    Array.prototype.forEach.call(document.querySelectorAll('.animation'), function (a) {
      a._printed = [a.dataset.cur, a.dataset.phase];
      var r = a.dataset.rests;
      a.dataset.cur = r ? r.split(',').pop() : '0';
      a.dataset.phase = '0';
      draw(a);
    });
  });
  window.addEventListener('afterprint', function () {
    Array.prototype.forEach.call(document.querySelectorAll('.animation'), function (a) {
      if (!a._printed) return;
      a.dataset.cur = a._printed[0] || '0';
      if (a._printed[1] !== undefined) a.dataset.phase = a._printed[1];
      draw(a);
    });
  });

  function show(i, revealAll) {
    current = Math.max(0, Math.min(slides.length - 1, i));
    slides.forEach(function (s, j) { s.classList.toggle('active', j === current); });
    fragments(slides[current]).forEach(function (f) {
      f.classList.toggle('visible', !!revealAll);
    });
    var bg = slides[current].getAttribute('data-background-color');
    document.body.style.background = bg || '';
    if (bar) bar.style.width = (100 * (current + 1) / slides.length) + '%';
    history.replaceState(null, '', '#' + (current + 1));
    runScripts(slides[current]);
    syncAll(slides[current], true);
  }

  function next() {
    var hidden = fragments(slides[current]).filter(function (f) {
      return !f.classList.contains('visible');
    });
    if (hidden.length) { hidden[0].classList.add('visible'); syncAll(slides[current], false); }
    else if (current < slides.length - 1) show(current + 1, false);
  }

  function prev() {
    var shown = fragments(slides[current]).filter(function (f) {
      return f.classList.contains('visible');
    });
    if (shown.length) { shown[shown.length - 1].classList.remove('visible'); syncAll(slides[current], false); }
    else if (current > 0) show(current - 1, true);
  }

  document.addEventListener('keydown', function (e) {
    if (e.key === 'ArrowRight' || e.key === 'ArrowDown' || e.key === ' ' || e.key === 'PageDown') next();
    else if (e.key === 'ArrowLeft' || e.key === 'ArrowUp' || e.key === 'PageUp') prev();
    else if (e.key === 'Home') show(0, false);
    else if (e.key === 'End') show(slides.length - 1, true);
    else return;
    e.preventDefault();
  });

  if (window.renderMathInElement) {
    window.renderMathInElement(document.body, {
      delimiters: [{ left: '\\[', right: '\\]', display: true },
                   { left: '\\(', right: '\\)', display: false }]
    });
  }

  var start = parseInt(location.hash.slice(1), 10);
  show(isNaN(start) ? 0 : start - 1, false);
})();
