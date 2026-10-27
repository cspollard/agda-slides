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
open import Data.List using (List; []; _∷_; _++_; map; mapMaybe)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
import Data.Maybe.Base as Maybe
open import Data.Maybe.Properties using (≡-dec)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; concat) renaming (_++_ to _++ˢ_)
open import Data.Unit using (tt)
open import Data.Container.Core using (Shape)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Nullary using (yes; no)
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
open import Slides.Lower using (presentBody)
open import Slides.Input.Binding using (Decoder)
open import Slides.Input.Supports (Shape BlockC) using (Supports; NavTotal)
open import Slides.Input.Nav using (next; prev)
open import Slides.Backend.Input
open import Slides.Backend.Reveal.Supports
open import Slides.Backend.HTML
open import Slides.Backend.Common public

module D = Alg 0ℓ 0ℓ DeckC

-- The deck algebra, given what is done to each slide body `f` (`steps` for the old
-- renderer, `presentBody b` for a backend `b`): each slide is a `<section>`; a stack is a
-- `<section>` of `<section>`s.
deckAlgBy : (Body → Body) → F-Algebra D.F
deckAlgBy f = record
  { A = ForestSetoid
  ; α = record
      { to   = λ { (slide o b , k)  → section (slideAttrs o) (renderBody (f b)) ∷ k tt
                 ; (stack o bs , k) →
                     section (slideAttrs o) (map (section [] ∘ renderBody ∘ f) bs) ∷ k tt }
      ; cong = λ { {slide _ _ , _} {slide _ _ , _} (refl ,ₚ k≈) →
                     Setoid.refl XMLSetoid PW.∷ k≈ tt
                 ; {stack _ _ , _} {stack _ _ , _} (refl ,ₚ k≈) →
                     Setoid.refl XMLSetoid PW.∷ k≈ tt }
      }
  }

renderDeckBy : (Body → Body) → Deck → Forest
renderDeckBy f = D.fold (deckAlgBy f) {⊤ˢ} nil

renderDeck : Deck → Forest
renderDeck = renderDeckBy steps

-- Reveal navigates a deck on a grid when it has a vertical stack, linearly otherwise.
modeOf : Deck → Mode
modeOf (pure _)                 = linear
modeOf (impure (slide _ _ , k)) = modeOf (k tt)
modeOf (impure (stack _ _ , _)) = stacked

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
    -- how keys are read (`revealKeys` is reveal's own); `init.js` configures reveal.js
    -- for the keys where this differs
    binding     : Mode → Decoder Key RCmd

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
  ; binding     = revealKeys
  }

private
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

-- The `keyboard` option of reveal.js: its key code and what the key does, for each key where
-- the binding `r` differs from reveal's own table `revealKeys`.  reveal.js runs the method
-- named by a string, and ignores the key (and its default) for any other value, so a command
-- with no method, or no command, turns the key off.  The option is keyed by key code, so
-- only the unmodified key is compared (and `otherKey`, which has no code, is not).
keyCode : KeyName → Maybe ℕ
keyCode arrowLeft  = just 37
keyCode arrowUp    = just 38
keyCode arrowRight = just 39
keyCode arrowDown  = just 40
keyCode space      = just 32
keyCode pageUp     = just 33
keyCode pageDown   = just 34
keyCode end        = just 35
keyCode home       = just 36
keyCode escape     = just 27
keyCode keyH       = just 72
keyCode keyJ       = just 74
keyCode keyK       = just 75
keyCode keyL       = just 76
keyCode keyN       = just 78
keyCode keyO       = just 79
keyCode keyP       = just 80
keyCode keyQ       = just 81
keyCode otherKey   = nothing

-- The `Reveal` method a command runs.
method : RCmd → Maybe String
method (nav next)      = just "next"
method (nav prev)      = just "prev"
method (ext overview)  = just "toggleOverview"
method (move right)    = just "right"
method (move left)     = just "left"
method (move down)     = just "down"
method (move up)       = just "up"
method _               = nothing

keyboard : Mode → Decoder Key RCmd → List (String × JSON)
keyboard m r = mapMaybe differs names
  where
    differs : KeyName → Maybe (String × JSON)
    differs n with keyCode n
    ... | nothing = nothing
    ... | just c with ≡-dec _≟R_ (revealKeys m (n , bare)) (r (n , bare))
    ...   | yes _ = nothing
    ...   | no _  = just (showℕ c , maybe′ stringⱼ (boolⱼ false) (r (n , bare) Maybe.>>= method))

-- The options for `Reveal.initialize`, as JSON.
options : Mode → RevealConfig → JSON
options m cfg = objectFromList
  ( ("hash" , trueⱼ)
  ∷ ("transition" , stringⱼ (RevealConfig.transition cfg))
  ∷ ("slideNumber" , boolⱼ (RevealConfig.slideNumber cfg))
  ∷ ("controls" , boolⱼ (RevealConfig.controls cfg))
  ∷ ("progress" , boolⱼ (RevealConfig.progress cfg))
  ∷ optNat "width" (RevealConfig.width cfg)
  ++ optNat "height" (RevealConfig.height cfg)
  ++ optKeyboard (keyboard m (RevealConfig.binding cfg m)) )
  where
    natⱼ : ℕ → JSON
    natⱼ n = numberⱼ (jsonNumber Sign.+ n [] (ℤ.+ 0))

    optNat : String → Maybe ℕ → List (String × JSON)
    optNat k nothing  = []
    optNat k (just n) = (k , natⱼ n) ∷ []

    optKeyboard : List (String × JSON) → List (String × JSON)
    optKeyboard []       = []
    optKeyboard kvs@(_ ∷ _) = ("keyboard" , objectFromList kvs) ∷ []

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
initScript : Mode → RevealConfig → String
initScript m cfg =
  scriptNote ++ˢ
  "Reveal.initialize(Object.assign(" ++ˢ renderJSON (options m cfg) ++ˢ
  ", {plugins: [RevealNotes, RevealHighlight, RevealMath.KaTeX]}));\n" ++ˢ
  scriptLoader ++ˢ
  animationSync ++ˢ
  concat (map (_++ˢ "\n") (RevealConfig.scripts cfg))

-- `index.html`: a backend `b` presents a deck when it supports all of `Nav`
-- (`Slides.Input.Supports`): each slide body is elaborated (`pause` is `await next`), its
-- awaited commands are lowered to `b`'s and the steps it gives are shown (`presentBody`).
-- The prologue (doctype and generator comment) is constant and unverified.
present : ∀ {C} (b : Supports C) → NavTotal b → RevealConfig → Deck → String
present b _ cfg d = prologue ++ˢ renderXML (page cfg (renderDeckBy (presentBody b) d))

renderReveal : RevealConfig → Deck → String
renderReveal = present (revealSupports (Shape BlockC)) (revealSupports-total (Shape BlockC))
