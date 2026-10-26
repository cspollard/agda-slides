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

  // Animations: the player shared with the reveal.js backend, `animation.js`; an animation
  // is shown while its slide is the active one
  var player = SlidesAnimation(function (a) { return a.closest('.slide').classList.contains('active'); });
  function syncAll(slide, jump) { player.syncAll(slide, jump); }

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
