Reveal.initialize(Object.assign({"hash":true,"transition":"slide","slideNumber":true,"controls":true,"progress":true,"width":1280,"height":720}, {plugins: [RevealNotes, RevealHighlight, RevealMath.KaTeX]}));
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
  function sync(a) {
    if (!a) return;
    var n = a.querySelectorAll('.anim-step.visible').length;
    a.querySelectorAll(':scope > .frame').forEach(function (f, i) { f.hidden = (i !== n); });
  }
  function all(slide) { if (slide) slide.querySelectorAll('.animation').forEach(sync); }
  Reveal.on('ready', function (e) { all(e.currentSlide); });
  Reveal.on('slidechanged', function (e) { all(e.currentSlide); });
  Reveal.on('fragmentshown', function (e) { sync(e.fragment.closest('.animation')); });
  Reveal.on('fragmenthidden', function (e) { sync(e.fragment.closest('.animation')); });
})();
Reveal.configure({center: false});
