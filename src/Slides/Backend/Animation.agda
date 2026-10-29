{-# OPTIONS --safe --without-K #-}

-- Shipping an animation to the page: the event list with parametric leaves.
--
-- The meaning of an animation (`Slides.Scene.Events`) is a duration and a sparse list of events
-- (onset, span, driver, leaf).  The page gets exactly that, as JSON in `data-events`:
--
--   event      {"o": onset, "s": span or null, "d": driver term or null, "l": leaf}
--   leaf       a diagram `["R", w, h, style]`, `["b", align, a, b]`, ...: the constructors of
--              `Slides.Diagram.Syntax`, one letter each, its scalars *terms*
--   term       null (the parameter), a number, or `[op, args...]`: the operations of the Space,
--              Time and Coupling signatures, numbered (see `assets/animation.js`)
--
-- and the page evaluates the terms, lays the leaves out (`Slides.Diagram.Place`) and draws them
-- (`Slides.Diagram.Print`) at each time: `assets/animation.js` is `Slides.Scene.Animation.frame`
-- in JavaScript.  Nothing is shared between formulas (no phases, no subformula tables): the
-- size of the page is the size of the scene.  The first frame is printed here, so a page without
-- JavaScript shows it.  The JavaScript is hand-written (a table of the signatures' operations
-- would be as long as the evaluator) and tested against Agda's frames (`make test-anim-ref`).
--
-- Reveal steps: an animation of acts `a₁ … aₙ` is the scene `a₁ ⨾ … ⨾ aₙ`; its *rests* are the
-- cumulative durations, the page plays from one rest to the next when a fragment appears.

module Slides.Backend.Animation where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Char.Base using (Char)
open import Data.Fin using (zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; map; reverse)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; _+_; _*_; _/_; _%_; _≡ᵇ_; _<ᵇ_) renaming (suc to sucℕ)
open import Data.Nat.Show using (show)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational using (ℚ) renaming (_*_ to _*ℚ_)
import Data.Rational as ℚ
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.String.Base using (String; fromList; toList; intersperse) renaming (_++_ to _++ˢ_)
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
open import Slides.Scalar.Coupling using (Ratio; Lerp; Ease; Easing; Linear; Step; StepStart)
open import Slides.Diagram.Style using (Style)
open import Slides.Diagram.Geometry
open import Slides.Diagram.Syntax
open import Slides.Diagram.Draw using (Layout; mkLayout)
open import Slides.Diagram.Print using (Print; renderSVG)
open import Slides.Scene.Syntax using (_⨾_)
import Slides.Scene.Moving ratSpace ratTime ratCoupling as Mv
open Mv using (Anim; Leaf; Sc; Drv; Event; onset; span; driver; leaf)
open import Slides.Backend.HTML using (hElement; Attrs)

------------------------------------------------------------------------
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

------------------------------------------------------------------------
-- Terms (operation numbers: see `assets/animation.js`)

-- a scalar: the Space and Time operations over the parameter and constants
scⱼ : Sc → JSON
scⱼ (pure nothing)                   = nullⱼ
scⱼ (pure (just q))                  = constⱼ q
scⱼ (impure (inj₁ Zero , k))         = natⱼ 0
scⱼ (impure (inj₁ Plus , k))         = arr (natⱼ 2 ∷ scⱼ (k zero) ∷ scⱼ (k (suc zero)) ∷ [])
scⱼ (impure (inj₁ Max , k))          = arr (natⱼ 3 ∷ scⱼ (k zero) ∷ scⱼ (k (suc zero)) ∷ [])
scⱼ (impure (inj₁ Minus , k))        = arr (natⱼ 4 ∷ scⱼ (k zero) ∷ scⱼ (k (suc zero)) ∷ [])
scⱼ (impure (inj₁ Lt , k))           = arr (natⱼ 5 ∷ scⱼ (k zero) ∷ scⱼ (k (suc zero)) ∷ scⱼ (k (suc (suc zero))) ∷ scⱼ (k (suc (suc (suc zero)))) ∷ [])
scⱼ (impure (inj₁ (Pct p) , k))      = arr (natⱼ 6 ∷ natⱼ p ∷ scⱼ (k _) ∷ [])
scⱼ (impure (inj₂ Hold , k))         = arr (natⱼ 7 ∷ scⱼ (k _) ∷ [])

-- a driver: a Coupling term over the local time and constants
drvⱼ : Drv → JSON
drvⱼ (pure nothing)                  = nullⱼ
drvⱼ (pure (just q))                 = constⱼ q
drvⱼ (impure (Ratio , k))            = arr (natⱼ 8 ∷ drvⱼ (k zero) ∷ drvⱼ (k (suc zero)) ∷ [])
drvⱼ (impure (Lerp , k))             = arr (natⱼ 9 ∷ drvⱼ (k zero) ∷ drvⱼ (k (suc zero)) ∷ drvⱼ (k (suc (suc zero))) ∷ [])
drvⱼ (impure (Ease e , k))           = arr (natⱼ 10 ∷ easingⱼ e ∷ drvⱼ (k _) ∷ [])

------------------------------------------------------------------------
-- Leaves

private
  opt : String → Maybe String → List (String × JSON)
  opt k nothing  = []
  opt k (just v) = (k , stringⱼ v) ∷ []

  optN : String → Maybe ℕ → List (String × JSON)
  optN k nothing  = []
  optN k (just v) = (k , natⱼ v) ∷ []

  op : String → List JSON → JSON
  op c xs = arr (stringⱼ c ∷ xs)

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
diaⱼ : Dia Sc → JSON
diaⱼ (impure (Rectangle w h s , k))   = op "R" (scⱼ w ∷ scⱼ h ∷ styleⱼ s ∷ [])
diaⱼ (impure (Segment w h s , k))     = op "S" (scⱼ w ∷ scⱼ h ∷ styleⱼ s ∷ [])
diaⱼ (impure (Disc r s , k))          = op "D" (scⱼ r ∷ styleⱼ s ∷ [])
diaⱼ (impure (Text w h n t s , k))    = op "T" (scⱼ w ∷ scⱼ h ∷ natⱼ n ∷ stringⱼ t ∷ styleⱼ s ∷ [])
diaⱼ (impure (Path w h d s , k))      = op "P" (scⱼ w ∷ scⱼ h ∷ stringⱼ d ∷ styleⱼ s ∷ [])
diaⱼ (impure (Spacer w h , k))        = op "_" (scⱼ w ∷ scⱼ h ∷ [])
diaⱼ (impure (Beside al , k))         = op "b" (valignⱼ al ∷ diaⱼ (k zero) ∷ diaⱼ (k (suc zero)) ∷ [])
diaⱼ (impure (Above al , k))          = op "a" (alignⱼ al ∷ diaⱼ (k zero) ∷ diaⱼ (k (suc zero)) ∷ [])
diaⱼ (impure (Atop , k))              = op "@" (diaⱼ (k zero) ∷ diaⱼ (k (suc zero)) ∷ [])
diaⱼ (impure (LabelAbove , k))        = op "l" (diaⱼ (k zero) ∷ diaⱼ (k (suc zero)) ∷ [])
diaⱼ (impure (LabelBelow , k))        = op "L" (diaⱼ (k zero) ∷ diaⱼ (k (suc zero)) ∷ [])
diaⱼ (impure (Place w h x y , k))     = op "p" (scⱼ w ∷ scⱼ h ∷ scⱼ x ∷ scⱼ y ∷ diaⱼ (k _) ∷ [])
diaⱼ (impure (Overlay w h , k))       = op "o" (scⱼ w ∷ scⱼ h ∷ diaⱼ (k zero) ∷ diaⱼ (k (suc zero)) ∷ [])
diaⱼ (impure (Named n , k))           = op "n" (stringⱼ n ∷ diaⱼ (k _) ∷ [])
diaⱼ (impure (Connect a pa b pb s , k)) = op "c" (stringⱼ a ∷ portⱼ pa ∷ stringⱼ b ∷ portⱼ pb ∷ styleⱼ s ∷ diaⱼ (k _) ∷ [])

-- an event
eventⱼ : Event Leaf → JSON
eventⱼ e = objectFromList
  ( ("o" , qⱼ (onset e)) ∷ ("s" , maybeⱼ qⱼ (span e)) ∷ ("d" , maybeⱼ drvⱼ (driver e))
  ∷ ("l" , diaⱼ (leaf e)) ∷ [] )

eventsⱼ : Anim → JSON
eventsⱼ a = arr (map eventⱼ (Mv.events a))

------------------------------------------------------------------------
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

------------------------------------------------------------------------
-- The element

-- the acts in sequence, and the cumulative durations: the rests of the reveal steps
sequence : Anim → List Anim → Anim
sequence a []       = a
sequence a (b ∷ bs) = a ⨾ sequence b bs

rests : Anim → List Anim → List ℚ
rests a as = go (ι 0) (a ∷ as)
  where go : ℚ → List Anim → List ℚ
        go t []       = []
        go t (x ∷ xs) = let t′ = t ℚ.+ Mv.duration x in t′ ∷ go t′ xs

-- the element: the first frame, the data, one fragment per step; `loop` runs while shown
animationEl : (name : String) (percent ms : ℕ) (loop : Bool) → Anim → List ℚ → XMLDoc
animationEl name pct ms loop a rs =
  hElement "div"
    ( ("class" , "animation") ∷ ("id" , name ++ˢ "-frames") ∷ ("data-ms" , show ms)
    ∷ ("data-events" , renderJSON (eventsⱼ a)) ∷ ("data-duration" , renderJSON (qⱼ (Mv.duration a)))
    ∷ restsAttr rs ++ loopAttr loop )
    ( hElement "div" (("class" , "frame") ∷ [])
        ( hElement "div" (("class" , "diagram") ∷ ("id" , name) ∷ [])
            (renderSVG qPrint name pct (firstFrame a) ∷ []) ∷ [] )
    ∷ map (λ _ → hElement "span" (("class" , "fragment anim-step") ∷ []) []) rs )
  where
    restsAttr : List ℚ → List (String × String)
    restsAttr []        = []
    restsAttr r@(_ ∷ _) = ("data-rests" , renderJSON (arr (map qⱼ r))) ∷ []
    loopAttr : Bool → List (String × String)
    loopAttr true  = ("data-loop" , "") ∷ []
    loopAttr false = []
