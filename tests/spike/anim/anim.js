// the step of a slide is the number of its visible fragments; copy it to the svg
(function () {
  function sync(section) {
    if (!section) return;
    var n = section.querySelectorAll('.fragment.visible').length;
    section.querySelectorAll('svg.anim').forEach(function (s) { s.setAttribute('data-step', String(n)); });
  }
  Reveal.on('ready', function (e) { sync(e.currentSlide); });
  Reveal.on('slidechanged', function (e) { sync(e.currentSlide); });
  Reveal.on('fragmentshown', function (e) { sync(e.fragment.closest('section')); });
  Reveal.on('fragmenthidden', function (e) { sync(e.fragment.closest('section')); });
})();
