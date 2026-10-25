// Animations for the "It Just Takes Two" deck.  Loaded by the page before
// `init.js`; each slide calls one of these from a `script` command, with the
// slide element (the loader runs a slide's scripts once, when first shown).
//
//   PAIRS.title(slide, id)         drifting point pairs on a canvas in #id
//
// Free-running random decoration.  Everything else is `Slides.Anim`: what follows
// the slide's steps (lit stages, growing bars, the histogram) is an `animate`, and
// the marching arrows are a `loop`; neither needs a script.  Animations only advance while their slide is the
// current one.
(function () {
  function mulberry(seed) {
    return function () {
      seed |= 0; seed = seed + 0x6D2B79F5 | 0;
      var t = Math.imul(seed ^ seed >>> 15, 1 | seed);
      t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
      return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
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

  window.PAIRS = { title: title };
})();
