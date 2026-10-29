{-# OPTIONS --safe --without-K #-}

-- The reveal.js backend: a shell over the shared core (`Slides.Backend.Render`) and a page.
--
-- Each slide is a `<section>`; a vertical stack is a `<section>` of `<section>`s.  The page loads
-- reveal.js and its plugins, the shared animation player and `init.js`; the options of
-- `Reveal.initialize` are a JSON value printed with parsnip's printer, among them the `keyboard`
-- table for the keys where the binding differs from reveal's own (`Slides.Backend.Input`).

module Slides.Backend.Reveal where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; _++_; map; mapMaybe)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
import Data.Maybe.Base as Maybe
open import Data.Maybe.Properties using (≡-dec)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.String.Base using (String; concat) renaming (_++_ to _++ˢ_)
open import Relation.Nullary using (yes; no)
import Data.Sign.Base as Sign
import Data.Integer.Base as ℤ

open import Data.XML.AST using (XMLDoc)
open import Data.XML.Print using (renderXML)
open import Data.JSON.AST using (JSON; objectFromList; trueⱼ; boolⱼ; stringⱼ; numberⱼ; jsonNumber)
open import Data.JSON.Print using (renderJSON)

open import Slides.Program.Navigation using (next; prev)
open import Slides.Deck.Talk using (Talk; mode; Mode)
open import Slides.Backend.HTML
open import Slides.Backend.Input
open import Slides.Backend.Render

-- how a slide and a stack are wrapped
shell : Shell
shell = record
  { wrapSlide = λ a x → hElement "section" a x ∷ []
  ; wrapStack = λ a xs → hElement "section" a (map (λ x → hElement "section" [] x) xs) ∷ [] }

------------------------------------------------------------------------
-- The page

-- The look of a deck: a reveal.js theme, a highlight.js style, and extra stylesheets (paths
-- relative to the page; reveal.js 6 ships the highlight styles `monokai` and `zenburn`, both dark).  `slides.css` styles the layout vocabulary (columns, boxes).
record Theme : Set where
  field
    revealTheme : String   -- a file in reveal.js's dist/theme/ (without .css)
    highlight   : String   -- a file in dist/plugin/highlight/ (without .css)
    stylesheets : List String

blackTheme whiteTheme : Theme
blackTheme = record { revealTheme = "black" ; highlight = "monokai" ; stylesheets = "slides.css" ∷ [] }
whiteTheme = record { revealTheme = "white" ; highlight = "monokai" ; stylesheets = "slides.css" ∷ [] }

-- Where reveal.js comes from: a copy next to the page, or a pinned version on the jsDelivr CDN.
data Source : Set where
  local : (path : String) → Source      -- a directory with a trailing slash
  cdn   : (version : String) → Source   -- for example "6.0.2"

sourceBase : Source → String
sourceBase (local p) = p
sourceBase (cdn v)   = "https://cdn.jsdelivr.net/npm/reveal.js@" ++ˢ v ++ˢ "/"

record RevealConfig : Set where
  field
    title       : String
    base        : String        -- URL or path of the reveal.js distribution, with a trailing slash
    theme       : Theme
    transition  : String
    slideNumber controls progress : Bool
    width height : Maybe ℕ      -- the size reveal.js lays slides out in (it scales to the window)
    scripts     : List String   -- JavaScript appended to `init.js`, after `Reveal.initialize`
    scriptFiles : List String   -- extra JavaScript files, loaded before `init.js`
    binding     : Mode → Key → Maybe RCmd   -- how keys are read (`revealKeys` is reveal's own)

defaultConfig : RevealConfig
defaultConfig = record
  { title = "Slides" ; base = "reveal/" ; theme = blackTheme ; transition = "slide"
  ; slideNumber = false ; controls = true ; progress = true ; width = nothing ; height = nothing
  ; scripts = [] ; scriptFiles = [] ; binding = revealKeys }

withSource : Source → RevealConfig → RevealConfig
withSource s cfg = record cfg { base = sourceBase s }

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
        ∷ map stylesheet (Theme.stylesheets theme) )
    ∷ hElement "body" []
        ( div "reveal" (div "slides" slides ∷ [])
        ∷ scriptTag (dist ++ˢ "reveal.js")
        ∷ scriptTag (dist ++ˢ "plugin/notes.js")
        ∷ scriptTag (dist ++ˢ "plugin/highlight.js")
        ∷ scriptTag (dist ++ˢ "plugin/math.js")
        ∷ scriptTag "animation.js"
        ∷ map scriptTag (RevealConfig.scriptFiles cfg)
        ++ scriptTag "init.js" ∷ [] )
    ∷ [] )
  where
    open RevealConfig cfg
    dist = base ++ˢ "dist/"

-- `index.html`; the prologue (doctype and generator comment) is constant
renderReveal : RevealConfig → Talk → String
renderReveal cfg t = prologue ++ˢ renderXML (page cfg (renderTalk shell t))

------------------------------------------------------------------------
-- `init.js`

-- the `Reveal` method a command runs
method : RCmd → Maybe String
method (nav next)      = just "next"
method (nav prev)      = just "prev"
method (aux overview)  = just "toggleOverview"
method (aux right)     = just "right"
method (aux left)      = just "left"
method (aux down)      = just "down"
method (aux up)        = just "up"
method _               = nothing

-- the keys reveal.js binds itself
revealCodes : List KeyCode
revealCodes = arrowLeft ∷ arrowUp ∷ arrowRight ∷ arrowDown ∷ space ∷ pageUp ∷ pageDown ∷ end ∷ home ∷ escape
            ∷ keyH ∷ keyJ ∷ keyK ∷ keyL ∷ keyN ∷ keyO ∷ keyP ∷ keyQ ∷ []

-- The `keyboard` option: for each key code where the binding differs from reveal's own table,
-- what the key does.  reveal.js runs the method named by a string and ignores the key (and its
-- default) for any other value, so a command with no method, or no command, turns the key off.
keyboard : Mode → (Key → Maybe RCmd) → List (String × JSON)
keyboard m r = mapMaybe differs revealCodes
  where
    differs : KeyCode → Maybe (String × JSON)
    differs c with ≡-dec _≟R_ (revealKeys m (⟨ c ⟩)) (r ⟨ c ⟩)
    ... | yes _ = nothing
    ... | no _  = just (showℕ c , maybe′ stringⱼ (boolⱼ false) (r ⟨ c ⟩ Maybe.>>= method))

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
    optKeyboard []          = []
    optKeyboard kvs@(_ ∷ _) = ("keyboard" , objectFromList kvs) ∷ []

-- runs the `script` blocks of a slide (`.js` elements carrying their code in `data-js`) once,
-- the first time the slide is shown
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

-- plays the animations with the player shared with the standalone backend (`assets/animation.js`):
-- an animation is shown while its slide is current and brought to the step its fragments are at
animationSync : String
animationSync =
  "(function () {\n" ++ˢ
  "  var player = SlidesAnimation(function (a) { return a.closest('section').classList.contains('present'); });\n" ++ˢ
  "  Reveal.on('ready', function (e) { player.syncAll(e.currentSlide, true); });\n" ++ˢ
  "  Reveal.on('slidechanged', function (e) { player.syncAll(e.currentSlide, true); });\n" ++ˢ
  "  Reveal.on('fragmentshown', function (e) { player.sync(e.fragment.closest('.animation'), false); });\n" ++ˢ
  "  Reveal.on('fragmenthidden', function (e) { player.sync(e.fragment.closest('.animation'), false); });\n" ++ˢ
  "})();\n"

initScript : Talk → RevealConfig → String
initScript t cfg =
  scriptNote ++ˢ
  "Reveal.initialize(Object.assign(" ++ˢ renderJSON (options (mode t) cfg) ++ˢ
  ", {plugins: [RevealNotes, RevealHighlight, RevealMath.KaTeX]}));\n" ++ˢ
  scriptLoader ++ˢ
  animationSync ++ˢ
  concat (map (_++ˢ "\n") (RevealConfig.scripts cfg))
