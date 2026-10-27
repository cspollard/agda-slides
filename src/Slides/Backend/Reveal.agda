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
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; concat) renaming (_++_ to _++ˢ_)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl; cong)
import Data.List.Relation.Binary.Pointwise as PW

open import Data.Container.Relation.Binary.Pointwise
  using () renaming (_,_ to _,ₚ_)

open import Categories.Functor.Algebra using (F-Algebra)

open import Data.XML.AST using (XMLDoc)
open import Data.XML.Equality using (XMLSetoid)
open import Data.XML.Print using (renderXML)
open import Data.JSON.AST using (JSON; objectFromList; trueⱼ; boolⱼ; stringⱼ; numberⱼ; jsonNumber)
import Data.Sign.Base as Sign
import Data.Integer.Base as ℤ
open import Data.JSON.Print using (renderJSON)

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
        ∷ scriptTag "animation.js"
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

-- Plays animations (`.animation`, see `renderAnimation`) with the player shared with the
-- standalone backend, `assets/animation.js` (loaded before `init.js`; it describes the
-- playback).  This is the glue: an animation is shown while its slide is the current one,
-- and it is brought to the step its fragments are at when the slide changes or a fragment
-- is shown or hidden.
animationSync : String
animationSync =
  "(function () {\n" ++ˢ
  "  var player = SlidesAnimation(function (a) { return a.closest('section').classList.contains('present'); });\n" ++ˢ
  "  Reveal.on('ready', function (e) { player.syncAll(e.currentSlide, true); });\n" ++ˢ
  "  Reveal.on('slidechanged', function (e) { player.syncAll(e.currentSlide, true); });\n" ++ˢ
  "  Reveal.on('fragmentshown', function (e) { player.sync(e.fragment.closest('.animation'), false); });\n" ++ˢ
  "  Reveal.on('fragmenthidden', function (e) { player.sync(e.fragment.closest('.animation'), false); });\n" ++ˢ
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
