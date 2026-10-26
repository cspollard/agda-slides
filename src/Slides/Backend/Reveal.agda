{-# OPTIONS --safe --without-K #-}

-- The reveal.js backend.
--
-- A backend is an algebra for each level of the vocabulary
-- (`Container.Interpret`).  Both algebras here have the same carrier, a
-- forest of XML documents (`List XMLDoc` with pointwise `_≈ₓ_`): the content
-- algebra renders the commands of a slide, and the deck algebra wraps the
-- rendered content of each slide in a `<section>`.  Rendering a deck is
-- the unique fold out of the free algebra.
--
-- The page is printed with parsnip's `renderXML`, which has the proved round
-- trip `parse (print x) ≈ₓ x`; the options for `Reveal.initialize` are a
-- JSON value printed with parsnip's JSON printer.

module Slides.Backend.Reveal where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; concat) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Container.FreeMonad using (pure; impure)
import Data.Container.FreeMonad as FM
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; trans; sym)
import Data.List.Relation.Binary.Pointwise as PW

open import Data.Container.Relation.Binary.Pointwise
  using () renaming (_,_ to _,ₚ_)

open import Categories.Functor.Algebra using (F-Algebra)

open import Data.XML.AST using (XMLDoc)
open import Data.XML.Equality using (_≈ₓ_; XMLSetoid)
open import Data.XML.Print using (renderXML)
open import Data.JSON.AST using (JSON; objectFromList; trueⱼ; boolⱼ; stringⱼ; numberⱼ; jsonNumber)
import Data.Sign.Base as Sign
import Data.Integer.Base as ℤ
open import Data.JSON.Print using (renderJSON)

open import Container.Polynomial using (Poly; Poly₀)
open import Container.Sum using (copair)
open import Container.FreeMonad.Algebraic using (module Alg)
open import Slides.Core
open import Slides.Steps using (steps)
open import Slides.Backend.HTML
open import Slides.Backend.Common public

module D = Alg 0ℓ 0ℓ DeckC

-- The deck algebra: each slide is a `<section>`; a stack is a `<section>`
-- of `<section>`s.
deckAlg : F-Algebra D.F
deckAlg = record
  { A = ForestSetoid
  ; α = record
      { to   = λ { (slide o b , k)  → section (slideAttrs o) (renderBody (steps b)) ∷ k tt
                 ; (stack o bs , k) →
                     section (slideAttrs o) (map (section [] ∘ renderBody ∘ steps) bs) ∷ k tt }
      ; cong = λ { {slide _ _ , _} {slide _ _ , _} (refl ,ₚ k≈) →
                     Setoid.refl XMLSetoid PW.∷ k≈ tt
                 ; {stack _ _ , _} {stack _ _ , _} (refl ,ₚ k≈) →
                     Setoid.refl XMLSetoid PW.∷ k≈ tt }
      }
  }

renderDeck : Deck → Forest
renderDeck = D.fold deckAlg {⊤ˢ} nil

------------------------------------------------------------------------
-- The page

-- The look of a deck: a reveal.js theme, a highlight.js style, and extra
-- stylesheets (paths relative to the page).  `slides.css` styles the layout
-- vocabulary (columns, boxes).
record Theme : Set where
  field
    revealTheme : String   -- a file in reveal.js's dist/theme/ (without .css)
    highlight   : String   -- a file in dist/plugin/highlight/ (without .css)
    stylesheets : List String

blackTheme whiteTheme serifTheme solarizedTheme : Theme
blackTheme     = record { revealTheme = "black"     ; highlight = "monokai" ; stylesheets = "slides.css" ∷ [] }
whiteTheme     = record { revealTheme = "white"     ; highlight = "github"  ; stylesheets = "slides.css" ∷ [] }
serifTheme     = record { revealTheme = "serif"     ; highlight = "github"  ; stylesheets = "slides.css" ∷ [] }
solarizedTheme = record { revealTheme = "solarized" ; highlight = "base16/solarized-light" ; stylesheets = "slides.css" ∷ [] }

-- Where reveal.js comes from: a copy next to the page, or a pinned version on
-- the jsDelivr CDN (nothing to install; the browser needs network access).
data Source : Set where
  local : (path : String) → Source      -- a directory with a trailing slash
  cdn   : (version : String) → Source   -- for example "6.0.2"

sourceBase : Source → String
sourceBase (local p) = p
sourceBase (cdn v)   = "https://cdn.jsdelivr.net/npm/reveal.js@" ++ˢ v ++ˢ "/"

record RevealConfig : Set where
  field
    title       : String
    -- URL or path of the reveal.js distribution, with a trailing slash
    base        : String
    theme       : Theme
    transition  : String
    slideNumber : Bool
    controls    : Bool
    progress    : Bool
    -- the size reveal.js lays slides out in (it scales to the window)
    width       : Maybe ℕ
    height      : Maybe ℕ
    -- JavaScript appended to `init.js`, after `Reveal.initialize`
    scripts     : List String
    -- extra JavaScript files (paths relative to the page), loaded after the
    -- reveal.js plugins and before `init.js`
    scriptFiles : List String

defaultConfig : RevealConfig
defaultConfig = record
  { title       = "Slides"
  ; base        = "reveal/"
  ; theme       = blackTheme
  ; transition  = "slide"
  ; slideNumber = false
  ; controls    = true
  ; progress    = true
  ; width       = nothing
  ; height      = nothing
  ; scripts     = []
  ; scriptFiles = []
  }

private
  scriptTag : String → XMLDoc
  scriptTag src = hText "script" (("src" , src) ∷ []) " "

  stylesheet : String → XMLDoc
  stylesheet href = hElement "link" (("rel" , "stylesheet") ∷ ("href" , href) ∷ []) []

  div : String → List XMLDoc → XMLDoc
  div cls = hElement "div" (("class" , cls) ∷ [])

page : RevealConfig → Forest → XMLDoc
page cfg slides =
  hElement "html" (("lang" , "en") ∷ [])
    ( hElement "head" []
        ( hElement "meta" (("charset" , "utf-8") ∷ []) []
        ∷ hText "title" [] title
        ∷ stylesheet (dist ++ˢ "reset.css")
        ∷ stylesheet (dist ++ˢ "reveal.css")
        ∷ stylesheet (dist ++ˢ "theme/" ++ˢ Theme.revealTheme theme ++ˢ ".css")
        ∷ stylesheet (dist ++ˢ "plugin/highlight/" ++ˢ Theme.highlight theme ++ˢ ".css")
        ∷ map stylesheet (Theme.stylesheets theme) ++ [] )
    ∷ hElement "body" []
        ( div "reveal" (div "slides" slides ∷ [])
        ∷ scriptTag (dist ++ˢ "reveal.js")
        ∷ scriptTag (dist ++ˢ "plugin/notes.js")
        ∷ scriptTag (dist ++ˢ "plugin/highlight.js")
        ∷ scriptTag (dist ++ˢ "plugin/math.js")
        ∷ map scriptTag (RevealConfig.scriptFiles cfg)
        ++ scriptTag "init.js"
        ∷ [] )
    ∷ [] )
  where
    open RevealConfig cfg
    dist = base ++ˢ "dist/"

-- Choose where reveal.js is loaded from.
withSource : Source → RevealConfig → RevealConfig
withSource s cfg = record cfg { base = sourceBase s }

-- The options for `Reveal.initialize`, as JSON.
options : RevealConfig → JSON
options cfg = objectFromList
  ( ("hash" , trueⱼ)
  ∷ ("transition" , stringⱼ (RevealConfig.transition cfg))
  ∷ ("slideNumber" , boolⱼ (RevealConfig.slideNumber cfg))
  ∷ ("controls" , boolⱼ (RevealConfig.controls cfg))
  ∷ ("progress" , boolⱼ (RevealConfig.progress cfg))
  ∷ optNat "width" (RevealConfig.width cfg)
  ++ optNat "height" (RevealConfig.height cfg) )
  where
    natⱼ : ℕ → JSON
    natⱼ n = numberⱼ (jsonNumber Sign.+ n [] (ℤ.+ 0))

    optNat : String → Maybe ℕ → List (String × JSON)
    optNat k nothing  = []
    optNat k (just n) = (k , natⱼ n) ∷ []

-- Runs the `script` commands of a slide (`.js` elements carrying their code
-- in `data-js`) once, the first time the slide is shown.
scriptLoader : String
scriptLoader =
  "(function () {\n" ++ˢ
  "  var done = new WeakSet();\n" ++ˢ
  "  function run(slide) {\n" ++ˢ
  "    if (!slide) return;\n" ++ˢ
  "    slide.querySelectorAll('.js[data-js]').forEach(function (e) {\n" ++ˢ
  "      if (done.has(e)) return;\n" ++ˢ
  "      done.add(e);\n" ++ˢ
  "      try { new Function('slide', e.getAttribute('data-js'))(slide); }\n" ++ˢ
  "      catch (x) { console.error(x); }\n" ++ˢ
  "    });\n" ++ˢ
  "  }\n" ++ˢ
  "  Reveal.on('ready', function (e) { run(e.currentSlide); });\n" ++ˢ
  "  Reveal.on('slidechanged', function (e) { run(e.currentSlide); });\n" ++ˢ
  "})();\n"

-- Plays animations (`.animation`, see `renderAnimation`).  The step is the number
-- of visible `.anim-step` fragments; it rests on frame 0 at step 0 and on
-- `rests[step-1]` after, and the page moves one frame towards the target every
-- `data-ms` milliseconds (forward or backward).  A `data-loop` animation also
-- advances a phase every `data-ms` while its slide is shown; the frame shown is
-- `phase * steps + step`.  Changing slide jumps.
animationSync : String
animationSync =
  "(function () {\n" ++ˢ
  "  function target(a) {\n" ++ˢ
  "    var n = a.querySelectorAll('.anim-step.visible').length;\n" ++ˢ
  "    if (n === 0) return 0;\n" ++ˢ
  "    var r = a.dataset.rests.split(',');\n" ++ˢ
  "    return +r[Math.min(n, r.length) - 1];\n" ++ˢ
  "  }\n" ++ˢ
  "  var SVGNS = 'http://www.w3.org/2000/svg';\n" ++ˢ
  "  var NUMS = { rect: ['x', 'y', 'width', 'height'], circle: ['cx', 'cy', 'r'], line: ['x1', 'y1', 'x2', 'y2'], text: ['x', 'y'] };\n" ++ˢ
  "  function parse(s) {\n" ++ˢ
  "    return document.importNode(new DOMParser().parseFromString(s, 'image/svg+xml').documentElement.firstChild, true);\n" ++ˢ
  "  }\n" ++ˢ
  "  // apply a list of edits to the children of `parent` (skipping `offset` of them)\n" ++ˢ
  "  function patch(parent, items, offset) {\n" ++ˢ
  "    var kids = parent.children, n = 0, rest = [];\n" ++ˢ
  "    items.forEach(function (it) {\n" ++ˢ
  "      if (it !== null && typeof it === 'object' && !Array.isArray(it) && 'r' in it) { rest = it.r; return; }\n" ++ˢ
  "      if (typeof it === 'number' && it < 0) { n -= it; return; }\n" ++ˢ
  "      var el = kids[offset + n]; n++;\n" ++ˢ
  "      if (it === 0) return;\n" ++ˢ
  "      if (Array.isArray(it)) { it.forEach(function (v, j) { var k = NUMS[el.localName][j]; el.setAttribute(k, +el.getAttribute(k) + v); }); return; }\n" ++ˢ
  "      if (typeof it === 'string') { parent.replaceChild(parse(it), el); return; }\n" ++ˢ
  "      patch(el, it.g, 0);\n" ++ˢ
  "    });\n" ++ˢ
  "    while (kids.length > offset + n) parent.removeChild(kids[offset + n]);\n" ++ˢ
  "    rest.forEach(function (s) { parent.appendChild(parse(s)); });\n" ++ˢ
  "  }\n" ++ˢ
  "  // A parametric animation (`data-param`, see `renderParamAnimation`): a formula is a number, a\n" ++ˢ
  "  // string (the parameter of that segment, from `r`) or `[op, a, b]`; `[\"h\", a]` is half of `a`,\n" ++ˢ
  "  // positions being in half units.\n" ++ˢ
  "  function ev(e, r) {\n" ++ˢ
  "    if (typeof e === 'number') return e;\n" ++ˢ
  "    if (typeof e === 'string') return r[+e];\n" ++ˢ
  "    var o = e[0], x = ev(e[1], r);\n" ++ˢ
  "    if (o === 'h') return Math.floor(x / 2);\n" ++ˢ
  "    var y = ev(e[2], r);\n" ++ˢ
  "    return o === '+' ? x + y : o === '-' ? Math.max(0, x - y) : o === 'm' ? Math.max(x, y) : Math.floor(x * y / 100);\n" ++ˢ
  "  }\n" ++ˢ
  "  // show tick `k`: swap in the elements of its phase, then set every number that depends on a parameter\n" ++ˢ
  "  function pframe(a, k) {\n" ++ˢ
  "    var P = a._p || (a._p = JSON.parse(a.dataset.param)), i = 0;\n" ++ˢ
  "    while (i + 1 < P.p.length && P.p[i + 1].s <= k) i++;\n" ++ˢ
  "    var svg = a.querySelector(':scope > .frame svg');\n" ++ˢ
  "    if (a._ph !== i) {\n" ++ˢ
  "      while (svg.children.length > 1) svg.removeChild(svg.lastChild);\n" ++ˢ
  "      P.p[i].b.forEach(function (s) { svg.appendChild(parse(s)); });\n" ++ˢ
  "      a._ph = i;\n" ++ˢ
  "    }\n" ++ˢ
  "    var r = P.v.map(function (v) { return v[1][k - v[0]] || 0; });\n" ++ˢ
  "    P.p[i].c.forEach(function (cs, j) {\n" ++ˢ
  "      if (cs === null) return;\n" ++ˢ
  "      var el = svg.children[1 + j];\n" ++ˢ
  "      cs.forEach(function (c, m) { if (c !== null) el.setAttribute(NUMS[el.localName][m], ev(c, r)); });\n" ++ˢ
  "    });\n" ++ˢ
  "  }\n" ++ˢ
  "  // show frame `k`: rebuild from the first frame when going back, else apply the next edits\n" ++ˢ
  "  function frame(a, k) {\n" ++ˢ
  "    if (a.dataset.param) { pframe(a, k); return; }\n" ++ˢ
  "    var d = a._d || (a._d = JSON.parse(a.dataset.deltas || '[]'));\n" ++ˢ
  "    var svg = a.querySelector(':scope > .frame svg');\n" ++ˢ
  "    if (!a._base) { a._base = svg.cloneNode(true); a._at = 0; }\n" ++ˢ
  "    if (k < a._at) { var fresh = a._base.cloneNode(true); svg.parentNode.replaceChild(fresh, svg); svg = fresh; a._at = 0; }\n" ++ˢ
  "    for (; a._at < k; a._at++) patch(svg, d[a._at], 1);\n" ++ˢ
  "  }\n" ++ˢ
  "  function geom(a) {\n" ++ˢ
  "    var n = a.dataset.n ? +a.dataset.n : JSON.parse(a.dataset.deltas || '[]').length + 1, v = a.getAttribute('data-loop');\n" ++ˢ
  "    var p = v === null ? 1 : (v === '' ? n : +v);\n" ++ˢ
  "    return { n: n, p: p, steps: n / p };\n" ++ˢ
  "  }\n" ++ˢ
  "  function draw(a) {\n" ++ˢ
  "    var g = geom(a);\n" ++ˢ
  "    frame(a, (+(a.dataset.phase || 0)) * g.steps + (+(a.dataset.cur || 0)));\n" ++ˢ
  "  }\n" ++ˢ
  "  function show(a, i) { a.dataset.cur = String(i); draw(a); }\n" ++ˢ
  "  function sync(a, jump) {\n" ++ˢ
  "    if (!a) return;\n" ++ˢ
  "    clearInterval(a._timer);\n" ++ˢ
  "    var t = target(a), ms = +a.dataset.ms, cur = +(a.dataset.cur || 0);\n" ++ˢ
  "    if (jump || ms === 0 || t === cur) { show(a, t); return; }\n" ++ˢ
  "    a._timer = setInterval(function () {\n" ++ˢ
  "      cur += (t > cur ? 1 : -1);\n" ++ˢ
  "      show(a, cur);\n" ++ˢ
  "      if (cur === t) clearInterval(a._timer);\n" ++ˢ
  "    }, ms);\n" ++ˢ
  "  }\n" ++ˢ
  "  function spin(a) {\n" ++ˢ
  "    var p = geom(a).p, ms = Math.max(+a.dataset.ms, 16);\n" ++ˢ
  "    setInterval(function () {\n" ++ˢ
  "      if (p > 1 && a.closest('section').classList.contains('present')) {\n" ++ˢ
  "        a.dataset.phase = String(((+(a.dataset.phase || 0)) + 1) % p);\n" ++ˢ
  "        draw(a);\n" ++ˢ
  "      }\n" ++ˢ
  "    }, ms);\n" ++ˢ
  "  }\n" ++ˢ
  "  document.querySelectorAll('.animation').forEach(function (a) { a._show = function (k) { frame(a, k); }; });\n" ++ˢ
  "  document.querySelectorAll('.animation[data-loop]').forEach(spin);\n" ++ˢ
  "  function all(slide) { if (slide) slide.querySelectorAll('.animation').forEach(function (a) { sync(a, true); }); }\n" ++ˢ
  "  Reveal.on('ready', function (e) { all(e.currentSlide); });\n" ++ˢ
  "  Reveal.on('slidechanged', function (e) { all(e.currentSlide); });\n" ++ˢ
  "  Reveal.on('fragmentshown', function (e) { sync(e.fragment.closest('.animation'), false); });\n" ++ˢ
  "  Reveal.on('fragmenthidden', function (e) { sync(e.fragment.closest('.animation'), false); });\n" ++ˢ
  "})();\n"

-- `init.js`: the options plus the plugins (which are JavaScript values, not
-- JSON), the script loader, and the deck's own scripts.
initScript : RevealConfig → String
initScript cfg =
  "Reveal.initialize(Object.assign(" ++ˢ renderJSON (options cfg) ++ˢ
  ", {plugins: [RevealNotes, RevealHighlight, RevealMath.KaTeX]}));\n" ++ˢ
  scriptLoader ++ˢ
  animationSync ++ˢ
  concat (map (_++ˢ "\n") (RevealConfig.scripts cfg))

-- `index.html`, with the (unverified, constant) doctype prefix.
renderReveal : RevealConfig → Deck → String
renderReveal cfg d = doctype ++ˢ renderXML (page cfg (renderDeck d))

------------------------------------------------------------------------
-- Structural properties of the rendering

-- The number of slide commands (slides and stacks) in a deck.
count : Deck → ℕ
count (pure _)         = 0
count (impure (_ , k)) = suc (count (k tt))

-- One top-level `<section>` per slide command, in order.
renderDeck-length : ∀ d → length (renderDeck d) ≡ count d
renderDeck-length (pure tt)                = refl
renderDeck-length (impure (slide _ _ , k)) = cong suc (renderDeck-length (k tt))
renderDeck-length (impure (stack _ _ , k)) = cong suc (renderDeck-length (k tt))

renderDeck-bind : ∀ (d₁ d₂ : Deck) →
                  renderDeck (d₁ FM.>>= λ _ → d₂) ≡ renderDeck d₁ ++ renderDeck d₂
renderDeck-bind (pure tt)                 d₂ = refl
renderDeck-bind (impure (slide o b , k))  d₂ =
  cong (section (slideAttrs o) (renderBody (steps b)) ∷_) (renderDeck-bind (k tt) d₂)
renderDeck-bind (impure (stack o bs , k)) d₂ =
  cong (section (slideAttrs o) (map (section [] ∘ renderBody ∘ steps) bs) ∷_) (renderDeck-bind (k tt) d₂)
