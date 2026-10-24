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
window.deckLoaded = true;
