// Animations for the "It Just Takes Two" deck.  Loaded by the page before
// `init.js`; each slide calls one of these from a `script` command, with the
// slide element (the loader runs a slide's scripts once, when first shown).
//
//   PAIRS.title(slide, id)         drifting point pairs on a canvas in #id
//   PAIRS.flow(slide)              pulses travelling along every .flow line
//   PAIRS.cycle(slide, ids, opts)  light up the nodes with these ids in turn
//   PAIRS.bump(slide, id)          a histogram filling with simulated events
//   PAIRS.grow(slide)              grow .bar rectangles, count up .stat numbers
//
// Animations only advance while their slide is the current one.
(function () {
  var NS = 'http://www.w3.org/2000/svg';

  function mulberry(seed) {
    return function () {
      seed |= 0; seed = seed + 0x6D2B79F5 | 0;
      var t = Math.imul(seed ^ seed >>> 15, 1 | seed);
      t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
      return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
  }

  function normal(rand) {
    var u = 1 - rand(), v = rand();
    return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v);
  }

  function active(slide) { return slide.classList.contains('present'); }

  // Call fn(now, dt) every frame while the slide is current.
  function loop(slide, fn) {
    var last = performance.now();
    (function tick(now) {
      if (active(slide)) fn(now, Math.min(0.1, (now - last) / 1000));
      last = now;
      requestAnimationFrame(tick);
    })(last);
  }

  function svgEl(name, attrs) {
    var e = document.createElementNS(NS, name);
    for (var k in attrs) e.setAttribute(k, attrs[k]);
    return e;
  }

  // ------------------------------------------------------------ title
  function title(slide, id) {
    var host = slide.querySelector('#' + id);
    if (!host) return;
    var cv = document.createElement('canvas');
    host.appendChild(cv);
    var ctx = cv.getContext('2d'), rand = mulberry(7), pairs = [], W = 1, H = 1;

    function size() {
      var r = host.getBoundingClientRect(), s = window.devicePixelRatio || 1;
      // the slide is scaled by reveal.js: use the unscaled layout size
      W = host.offsetWidth; H = host.offsetHeight;
      cv.width = W * s; cv.height = H * s; ctx.setTransform(s, 0, 0, s, 0, 0);
    }
    size();
    window.addEventListener('resize', size);

    for (var i = 0; i < 26; i++) {
      var cx = rand() * W, cy = rand() * H;
      pairs.push({ cx: cx, cy: cy, vx: (rand() - .5) * 18, vy: (rand() - .5) * 18,
                   r: 26 + rand() * 60, a: rand() * 6.28, w: (rand() - .5) * 1.4,
                   hue: rand() < .5 ? 212 : 350 });
    }

    loop(slide, function (now, dt) {
      ctx.clearRect(0, 0, W, H);
      pairs.forEach(function (p) {
        p.cx += p.vx * dt; p.cy += p.vy * dt; p.a += p.w * dt;
        if (p.cx < -80) p.cx = W + 80; if (p.cx > W + 80) p.cx = -80;
        if (p.cy < -80) p.cy = H + 80; if (p.cy > H + 80) p.cy = -80;
        var x1 = p.cx + Math.cos(p.a) * p.r, y1 = p.cy + Math.sin(p.a) * p.r;
        var x2 = p.cx - Math.cos(p.a) * p.r, y2 = p.cy - Math.sin(p.a) * p.r;
        var col = 'hsl(' + p.hue + ',48%,40%)';
        ctx.strokeStyle = 'hsla(' + p.hue + ',48%,40%,.3)'; ctx.lineWidth = 1.5;
        ctx.beginPath(); ctx.moveTo(x1, y1); ctx.lineTo(x2, y2); ctx.stroke();
        ctx.fillStyle = col;
        [[x1, y1], [x2, y2]].forEach(function (q) {
          ctx.beginPath(); ctx.arc(q[0], q[1], 4.5, 0, 6.2832); ctx.fill();
        });
      });
    });
  }

  // ------------------------------------------------------------ flow
  function flow(slide) {
    Array.prototype.forEach.call(slide.querySelectorAll('.diagram svg'), function (svg) {
      var pulses = [];
      Array.prototype.forEach.call(svg.querySelectorAll('line.flow'), function (ln, i) {
        var a = [+ln.getAttribute('x1'), +ln.getAttribute('y1')];
        var b = [+ln.getAttribute('x2'), +ln.getAttribute('y2')];
        for (var k = 0; k < 2; k++) {
          var c = svgEl('circle', { r: 5, class: 'pulse' });
          svg.appendChild(c);
          pulses.push({ c: c, a: a, b: b, t: (i * .13 + k * .5) % 1 });
        }
      });
      if (!pulses.length) return;
      loop(slide, function (now, dt) {
        pulses.forEach(function (p) {
          p.t = (p.t + dt * .45) % 1;
          p.c.setAttribute('cx', p.a[0] + (p.b[0] - p.a[0]) * p.t);
          p.c.setAttribute('cy', p.a[1] + (p.b[1] - p.a[1]) * p.t);
        });
      });
    });
  }

  // ------------------------------------------------------------ cycle
  // opts.accumulate: keep earlier nodes lit (a chain builds up, then restarts)
  function cycle(slide, ids, opts) {
    var acc = opts && opts.accumulate, step = (opts && opts.seconds) || 1.6;
    var nodes = ids.map(function (i) { return slide.querySelector('#' + i); }).filter(Boolean);
    if (!nodes.length) return;
    var clock = 0, shown = -1;
    loop(slide, function (now, dt) {
      clock += dt;
      var n = Math.floor(clock / step) % (nodes.length + (acc ? 1 : 0));
      if (n === shown) return;
      shown = n;
      nodes.forEach(function (e, j) {
        e.classList.toggle('on', acc ? j < n : j === n);
      });
    });
  }

  // ------------------------------------------------------------ bump
  function bump(slide, id) {
    var host = slide.querySelector('#' + id);
    if (!host) return;
    var W = 560, H = 320, L = 40, R = 540, B = 270, T = 30;
    var lo = -4, hi = 5, nb = 36, bw = (R - L) / nb;
    var theta = .12, psi = 1.8, total = 2500, rand = mulberry(11);
    var bkg = [], sig = [], n = 0;
    for (var i = 0; i < nb; i++) { bkg.push(0); sig.push(0); }

    var svg = svgEl('svg', { viewBox: '0 0 ' + W + ' ' + H });
    svg.appendChild(svgEl('line', { x1: L, y1: B, x2: R, y2: B, class: 'axis' }));
    var bars = [];
    for (i = 0; i < nb; i++) {
      var b = svgEl('rect', { x: L + i * bw + 1, y: B, width: bw - 2, height: 0, class: 'hist-bkg' });
      var s = svgEl('rect', { x: L + i * bw + 1, y: B, width: bw - 2, height: 0, class: 'hist-sig' });
      svg.appendChild(b); svg.appendChild(s); bars.push([b, s]);
    }
    [-4, -2, 0, 2, 4].forEach(function (v) {
      var x = L + (v - lo) / (hi - lo) * (R - L);
      var t = svgEl('text', { x: x, y: B + 24, 'text-anchor': 'middle', 'font-size': 16, class: 'dim' });
      t.textContent = v; svg.appendChild(t);
    });
    var cap = svgEl('text', { x: L, y: 18, 'font-size': 18 });
    svg.appendChild(cap);
    host.appendChild(svg);

    function add() {
      var isSig = rand() < theta;
      var x = isSig ? psi + .1 * normal(rand) : normal(rand);
      var k = Math.floor((x - lo) / (hi - lo) * nb);
      if (k < 0 || k >= nb) return;
      (isSig ? sig : bkg)[k]++;
    }
    function draw() {
      var m = 1;
      for (var i = 0; i < nb; i++) m = Math.max(m, bkg[i] + sig[i]);
      var scale = (B - T - 10) / m;
      for (i = 0; i < nb; i++) {
        var hb = bkg[i] * scale, hs = sig[i] * scale;
        bars[i][0].setAttribute('y', B - hb); bars[i][0].setAttribute('height', hb);
        bars[i][1].setAttribute('y', B - hb - hs); bars[i][1].setAttribute('height', hs);
      }
      cap.textContent = 'N = ' + n + ' events';
    }
    loop(slide, function () {
      for (var j = 0; j < 14 && n < total; j++) { add(); n++; }
      draw();
    });
  }

  // ------------------------------------------------------------ grow
  function countUp(el) {
    var m = /^([^0-9.]*)([0-9]+(?:\.[0-9]+)?)(.*)$/.exec(el.textContent.trim());
    if (!m) return;
    var to = parseFloat(m[2]), dec = (m[2].split('.')[1] || '').length, t0 = performance.now();
    (function step(now) {
      var f = Math.min(1, (now - t0) / 1500), e = 1 - Math.pow(1 - f, 3);
      el.textContent = m[1] + (to * e).toFixed(dec) + m[3];
      if (f < 1) requestAnimationFrame(step);
    })(t0);
  }

  function grow(slide) {
    Array.prototype.forEach.call(slide.querySelectorAll('.bar'), function (b, i) {
      b.style.transitionDelay = (i * .25) + 's';
      requestAnimationFrame(function () { requestAnimationFrame(function () { b.classList.add('go'); }); });
    });
    Array.prototype.forEach.call(slide.querySelectorAll('.count'), countUp);
  }

  window.PAIRS = { title: title, flow: flow, cycle: cycle, bump: bump, grow: grow };
})();
