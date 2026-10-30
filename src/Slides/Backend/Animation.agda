{-# OPTIONS --safe --without-K #-}

-- Shipping an animation: its meaning (`Slides.Scene.Events`) is a duration and a sparse event
-- list, and the page gets exactly that as JSON in a `script` child of the animation:
--
--   {"n": table, "e": events}
--   event  {"o": onset, "s": span or null, "d": driver term or null, "l": leaf}
--   leaf   a diagram `["R", w, h, style]`, `["b", align, a, b]`, ...: one letter per constructor
--          of `Slides.Diagram.Syntax`, its scalars terms
--   term   null (the parameter), a number, or `[op, args...]`: numbered Space, Time and
--          Coupling operations (see `assets/animation.js`)
--
-- Diagrams and terms are trees; equal subtrees are shipped once (`Slides.Backend.Share`), and a
-- string where a diagram or term may stand is a position in `"n"`.  The page evaluates terms,
-- lays out (`Slides.Diagram.Place`) and prints (`Slides.Diagram.Print`) at each time:
-- `assets/animation.js` is `Slides.Scene.Animation.frame` in JavaScript, tested against Agda's
-- frames (`make test-anim-ref`).  The first frame is printed here, so the page works without it.
--
-- Reveal steps: acts `a₁ … aₙ` are the scene `a₁ ⨾ … ⨾ aₙ`, and the page plays from one `rests`
-- entry to the next per fragment.  Steps over a loop: `n` phases end to end; the loop picks
-- the phase, the steps play within it.

module Slides.Backend.Animation where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Char.Base using (Char)
open import Data.Fin using (zero; suc)
import Data.List.Base as L
open import Data.List.Base using (List; []; _∷_; _++_; map; reverse; concatMap; zipWith)
open import Function.Base using (_∘_)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Nat.Base using (ℕ; _+_; _*_; _/_; _%_; _≡ᵇ_; _<ᵇ_) renaming (suc to sucℕ)
open import Data.Nat.Show using (show)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ) renaming (_*_ to _*ℚ_)
import Data.Rational as ℚ
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.String.Base using (String; fromList; toList; intersperse; concat) renaming (_++_ to _++ˢ_)
open import Data.Container.FreeMonad using (pure; impure)
import Data.Integer.Base as ℤ
import Data.Sign.Base as Sign
open import Data.Integer.Base using (ℤ)

open import Data.XML.AST using (XMLDoc)
open import Data.JSON.AST using (JSON; objectFromList; stringⱼ; numberⱼ; arrayⱼ; nullⱼ; jsonNumber)
open import Data.JSON.Print using (renderJSON)

open import Slides.Scalar.Model.Rat using (ratSpace; ratTime; ratCoupling; ι)
open import Slides.Scalar.Space using (Zero; Plus; Max; Minus; Lt; Pct)
open import Slides.Scalar.Time using (Hold)
open import Slides.Scalar.Coupling using (Ratio; Lerp; Ease; Easing; Linear; Step; StepStart; Bezier)
open import Slides.Diagram.Style using (Style)
open import Slides.Diagram.Geometry
open import Slides.Diagram.Syntax
open import Slides.Diagram.Draw using (Layout; mkLayout)
open import Slides.Diagram.Print using (Print; renderSVG)
open import Slides.Scene.Syntax using (_⨾_)
open import Slides.Text using (markup)
import Slides.Scene.Moving ratSpace ratTime ratCoupling as Mv
open Mv using (Anim; Leaf; Sc; Drv; Event; onset; span; driver; leaf)
open import Slides.Backend.Share using (Tree; tree; ship; shareTop)
open import Slides.Backend.HTML using (hElement; hText; Attrs)

-- JSON values

natⱼ : ℕ → JSON
natⱼ n = numberⱼ (jsonNumber Sign.+ n [] (ℤ.+ 0))

intⱼ : ℤ → JSON
intⱼ (ℤ.+ n)      = natⱼ n
intⱼ (ℤ.-[1+ m ]) = numberⱼ (jsonNumber Sign.- (sucℕ m) [] (ℤ.+ 0))

-- a rational: a number if whole, else `[n, d]`
qⱼ : ℚ → JSON
qⱼ q = if ℚ.denominatorℕ q ≡ᵇ 1 then intⱼ (ℚ.numerator q) else arrayⱼ (intⱼ (ℚ.numerator q) ∷ natⱼ (ℚ.denominatorℕ q) ∷ [])

-- a constant in a term: a plain number if whole, else `[0, n, d]`
constⱼ : ℚ → JSON
constⱼ q = if ℚ.denominatorℕ q ≡ᵇ 1 then intⱼ (ℚ.numerator q) else arrayⱼ (natⱼ 0 ∷ intⱼ (ℚ.numerator q) ∷ natⱼ (ℚ.denominatorℕ q) ∷ [])

arr : List JSON → JSON
arr = arrayⱼ

easingⱼ : Easing → JSON
easingⱼ Linear    = natⱼ 0
easingⱼ Step      = natⱼ 1
easingⱼ StepStart = natⱼ 2
easingⱼ (Bezier a b c d) = arr (natⱼ a ∷ natⱼ b ∷ natⱼ c ∷ natⱼ d ∷ [])

-- Terms (operation numbers: see `assets/animation.js`)

-- An item of a printed array: text, or a subtree that is shared (the page finds it by its position
-- in the table, written as a string).  Constants and the parameter stay in the text.
Item : Set
Item = String ⊎ Tree

txt : JSON → Item
txt = inj₁ ∘ renderJSON

-- an array of items
arrT : List Item → Tree
arrT xs = tree (inj₁ "[" ∷ L.intersperse (inj₁ ",") xs ++ inj₁ "]" ∷ [])

-- an operation applied to items
opT : ℕ → List Item → Item
opT n xs = inj₂ (arrT (txt (natⱼ n) ∷ xs))

-- a scalar: the Space and Time operations over the parameter and constants
scI : Sc → Item
scI (pure nothing)                   = txt nullⱼ
scI (pure (just q))                  = txt (constⱼ q)
scI (impure (inj₁ Zero , k))         = txt (natⱼ 0)
scI (impure (inj₁ Plus , k))         = opT 2 (scI (k zero) ∷ scI (k (suc zero)) ∷ [])
scI (impure (inj₁ Max , k))          = opT 3 (scI (k zero) ∷ scI (k (suc zero)) ∷ [])
scI (impure (inj₁ Minus , k))        = opT 4 (scI (k zero) ∷ scI (k (suc zero)) ∷ [])
scI (impure (inj₁ Lt , k))           = opT 5 (scI (k zero) ∷ scI (k (suc zero)) ∷ scI (k (suc (suc zero))) ∷ scI (k (suc (suc (suc zero)))) ∷ [])
scI (impure (inj₁ (Pct p) , k))      = opT 6 (txt (natⱼ p) ∷ scI (k _) ∷ [])
scI (impure (inj₂ Hold , k))         = opT 7 (scI (k _) ∷ [])

-- a driver: a Coupling term over the local time and constants
drvI : Drv → Item
drvI (pure nothing)                  = txt nullⱼ
drvI (pure (just q))                 = txt (constⱼ q)
drvI (impure (Ratio , k))            = opT 8 (drvI (k zero) ∷ drvI (k (suc zero)) ∷ [])
drvI (impure (Lerp , k))             = opT 9 (drvI (k zero) ∷ drvI (k (suc zero)) ∷ drvI (k (suc (suc zero))) ∷ [])
drvI (impure (Ease e , k))           = opT 10 (txt (easingⱼ e) ∷ drvI (k _) ∷ [])

-- Leaves

private
  opt : String → Maybe String → List (String × JSON)
  opt k nothing  = []
  opt k (just v) = (k , stringⱼ v) ∷ []

  optN : String → Maybe ℕ → List (String × JSON)
  optN k nothing  = []
  optN k (just v) = (k , natⱼ v) ∷ []

  valignⱼ : VAlign → JSON
  valignⱼ top    = natⱼ 0
  valignⱼ middle = natⱼ 1
  valignⱼ bottom = natⱼ 2

  alignⱼ : Align → JSON
  alignⱼ left    = natⱼ 0
  alignⱼ centred = natⱼ 1
  alignⱼ right   = natⱼ 2

  sideⱼ : Side → ℕ
  sideⱼ north  = 0
  sideⱼ south  = 1
  sideⱼ east   = 2
  sideⱼ west   = 3
  sideⱼ middle = 4

  portⱼ : Port → JSON
  portⱼ (side s) = natⱼ (sideⱼ s)
  portⱼ (at s p) = arr (natⱼ (sideⱼ s) ∷ natⱼ p ∷ [])

  maybeⱼ : ∀ {A : Set} → (A → JSON) → Maybe A → JSON
  maybeⱼ f nothing  = nullⱼ
  maybeⱼ f (just x) = f x

styleⱼ : Style → JSON
styleⱼ s = objectFromList
  ( opt "stroke" (Style.stroke s) ++ opt "fill" (Style.fill s) ++ opt "cls" (Style.cls s)
  ++ opt "id" (Style.ident s) ++ opt "dash" (Style.dash s) ++ opt "anchor" (Style.anchor s)
  ++ optN "sw" (Style.strokeWidth s) ++ optN "rx" (Style.rx s) ++ optN "op" (Style.opacity s) )

-- a diagram over terms: one letter per constructor, children last
op : String → List Item → Item
op c xs = inj₂ (arrT (txt (stringⱼ c) ∷ xs))

-- the points of a polyline, x then y of each, are terms like any other scalar
pointsT : List (Sc × Sc) → List Item
pointsT []             = []
pointsT ((x , y) ∷ ps) = scI x ∷ scI y ∷ pointsT ps

diaT : Dia Sc → Item
diaT (impure (Rectangle w h s , k))   = op "R" (scI w ∷ scI h ∷ txt (styleⱼ s) ∷ [])
diaT (impure (Segment w h s , k))     = op "S" (scI w ∷ scI h ∷ txt (styleⱼ s) ∷ [])
diaT (impure (Disc r s , k))          = op "D" (scI r ∷ txt (styleⱼ s) ∷ [])
diaT (impure (Ellipse a b s , k))     = op "E" (scI a ∷ scI b ∷ txt (styleⱼ s) ∷ [])
diaT (impure (Polyline c ps s , k))   = op "Y" (txt (natⱼ (if c then 1 else 0)) ∷ txt (styleⱼ s) ∷ pointsT ps)
diaT (impure (Text w h n t s , k))    = op "T" (scI w ∷ scI h ∷ txt (natⱼ n) ∷ txt (stringⱼ (markup t)) ∷ txt (styleⱼ s) ∷ [])
diaT (impure (Path w h d s , k))      = op "P" (scI w ∷ scI h ∷ txt (stringⱼ d) ∷ txt (styleⱼ s) ∷ [])
diaT (impure (Spacer w h , k))        = op "_" (scI w ∷ scI h ∷ [])
diaT (impure (Beside al , k))         = op "b" (txt (valignⱼ al) ∷ diaT (k zero) ∷ diaT (k (suc zero)) ∷ [])
diaT (impure (Above al , k))          = op "a" (txt (alignⱼ al) ∷ diaT (k zero) ∷ diaT (k (suc zero)) ∷ [])
diaT (impure (Atop , k))              = op "@" (diaT (k zero) ∷ diaT (k (suc zero)) ∷ [])
diaT (impure (LabelAbove , k))        = op "l" (diaT (k zero) ∷ diaT (k (suc zero)) ∷ [])
diaT (impure (LabelBelow , k))        = op "L" (diaT (k zero) ∷ diaT (k (suc zero)) ∷ [])
diaT (impure (Place w h x y , k))     = op "p" (scI w ∷ scI h ∷ scI x ∷ scI y ∷ diaT (k _) ∷ [])
diaT (impure (Overlay w h , k))       = op "o" (scI w ∷ scI h ∷ diaT (k zero) ∷ diaT (k (suc zero)) ∷ [])
diaT (impure (Named n , k))           = op "n" (txt (stringⱼ n) ∷ diaT (k _) ∷ [])
diaT (impure (Connect a pa b pb s , k)) = op "c" (txt (stringⱼ a) ∷ txt (portⱼ pa) ∷ txt (stringⱼ b) ∷ txt (portⱼ pb) ∷ txt (styleⱼ s) ∷ diaT (k _) ∷ [])

-- an event: its driver and leaf are shared
eventT : Event Leaf → Tree
eventT e = tree
  ( inj₁ ("{\"o\":" ++ˢ renderJSON (qⱼ (onset e)) ++ˢ ",\"s\":" ++ˢ renderJSON (maybeⱼ qⱼ (span e)) ++ˢ ",\"d\":")
  ∷ maybe′ drvI (inj₁ "null") (driver e) ∷ inj₁ ",\"l\":" ∷ diaT (leaf e) ∷ inj₁ "}" ∷ [] )

-- the events with their diagrams and terms shared: {"n": table of nodes, "e": events}.  A node
-- is an array (a term or a diagram), a reference to a node the string of its position in the table
eventsJSON : Anim → String
eventsJSON a with shareTop (map eventT (Mv.events a)) []
... | es , d with ship es d
...   | tbl , evs = "{\"n\":[" ++ˢ intersperse "," tbl ++ˢ "],\"e\":[" ++ˢ intersperse "," evs ++ˢ "]}"

-- The first frame, printed here

-- a number with up to three decimals, trailing zeros dropped (the page prints the same)
showQ : ℚ → String
showQ q = sign (ℚ.numerator q) ++ˢ show (total / 1000) ++ˢ frac
  where
    n = ℤ.∣ ℚ.numerator q ∣
    d = ℚ.denominatorℕ q
    total = (n * 1000 + d / 2) / d
    sign : ℤ → String
    sign (ℤ.+ _)    = ""
    sign ℤ.-[1+ _ ] = if total ≡ᵇ 0 then "" else "-"
    pad : ℕ → String
    pad r = (if r <ᵇ 10 then "00" else if r <ᵇ 100 then "0" else "") ++ˢ show r
    dropZeros : List Char → List Char
    dropZeros ('0' ∷ r) = dropZeros r
    dropZeros r         = r
    frac : String
    frac with total % 1000
    ... | 0 = ""
    ... | r = "." ++ˢ fromList (reverse (dropZeros (reverse (toList (pad r)))))

-- positions are in half units
qPrint : Print ℚ
qPrint = record { unit = showQ ; pos = λ x → showQ (ℚ.½ *ℚ x) }

firstFrame : Anim → Layout ℚ
firstFrame a with Mv.frame a 0
... | nothing = mkLayout (ι 0) (ι 0) [] []
... | just l  = l

-- The element

-- a laid-out drawing at rest, as a `diagram` element
stillEl : String → ℕ → Layout ℚ → XMLDoc
stillEl n pct l = hElement "div" (("class" , "diagram") ∷ ("id" , n) ∷ []) (renderSVG qPrint n pct l ∷ [])

-- JSON in a `script` element is raw text to the browser, which must not see `<`, `&` or `>`:
-- inside JSON they occur only in strings, where `\uXXXX` is the same character
htmlSafe : String → String
htmlSafe = fromList ∘ concatMap esc ∘ toList
  where
    esc : Char → List Char
    esc '<' = toList "\\u003c"
    esc '>' = toList "\\u003e"
    esc '&' = toList "\\u0026"
    esc c   = c ∷ []

-- how the clock runs: only at the steps, in a loop while the slide is shown, or the steps within
-- a loop of `n` phases (a phase is a copy of the acts; the page shows phase `⌊t⌋ mod n`)
data Play : Set where
  steps loop : Play
  both       : ℕ → Play

-- the element: the first frame, the data, one fragment per step
animationEl : (name : String) (percent ms : ℕ) (play : Play) → Anim → List ℚ → XMLDoc
animationEl name pct ms play a rs =
  hElement "div"
    ( ("class" , "animation") ∷ ("id" , name ++ˢ "-frames") ∷ ("data-ms" , show ms)
    ∷ ("data-duration" , renderJSON (qⱼ (Mv.duration a)))
    ∷ restsAttr rs ++ playAttr play )
    ( hElement "div" (("class" , "frame") ∷ [])
        ( hElement "div" (("class" , "diagram") ∷ ("id" , name) ∷ [])
            (renderSVG qPrint name pct (firstFrame a) ∷ []) ∷ [] )
    ∷ hText "script" (("type" , "application/json") ∷ ("class" , "events") ∷ []) (htmlSafe (eventsJSON a))
    ∷ map (λ _ → hElement "span" (("class" , "fragment anim-step") ∷ []) []) rs )
  where
    restsAttr : List ℚ → List (String × String)
    restsAttr []        = []
    restsAttr r@(_ ∷ _) = ("data-rests" , renderJSON (arr (map qⱼ r))) ∷ []
    playAttr : Play → List (String × String)
    playAttr steps    = []
    playAttr loop     = ("data-loop" , "") ∷ []
    playAttr (both n) = ("data-loop" , "") ∷ ("data-phases" , show n) ∷ []
