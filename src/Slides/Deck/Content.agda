{-# OPTIONS --safe --without-K #-}

-- Content: the leaves of a slide.  A `Flow` is a list of `Block`s, the free monoid on them,
-- laid out by the browser; overlaying two leaves of a scene is `++`, all that
-- `Slides.Scene.Sample` asks of a leaf carrier.  Blocks nest (columns, boxes, fragments hold
-- flows), so folds recurse through `List` by mutual functions.
--
-- Meaning: a monoid homomorphism to lines of plain text.
--   `plain-++`   plain (xs ++ ys) ≡ plain xs ++ plain ys
--   `plain-flat` a flat bullet list reads as one "- " line per item
-- The HTML reading is the other homomorphism (`Slides.Backend.Render`).

module Slides.Deck.Content where

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap)
open import Data.Maybe.Base using (Maybe)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; proj₁; proj₂)
open import Data.String.Base using (String; intersperse; concat) renaming (_++_ to _++ˢ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
import Data.List.Properties as ListP

open import Slides.Math using (Math; toLaTeX)
open import Slides.Text public
open import Data.Rational using (ℚ)
open import Slides.Diagram.Syntax using (Dia)
open import Slides.Diagram.Draw using (Layout)
open import Slides.Scalar.Model.Rat using (ratSpace; ratTime; ratCoupling)
import Slides.Scene.Moving ratSpace ratTime ratCoupling as Mv

-- a bullet with its sub-bullets (a rose tree); a flat list is a list of `leaf`s
data Bullet : Set where
  bullet : Text → List Bullet → Bullet

leaf : Text → Bullet
leaf t = bullet t []

data Block : Set where
  heading     : ℕ → Text → Block
  paragraph   : Text → Block
  bulletTree  : (incremental : Bool) → List Bullet → Block
  code        : (language source : String) → Block
  displayMath : Math → Block
  -- an image file with a caption; the width is a percent of the slide's content width (none: the
  -- image's own size, as the stylesheet leaves it), as for `diagram` and `animation`
  figure      : (src : String) (width : Maybe ℕ) (caption : Text) → Block
  notes       : Text → Block
  table       : (header : List Text) (rows : List (List Text)) → Block
  references  : List (String × Text) → Block
  diagram     : (name : String) (percent : ℕ) → Dia ℕ → Block
  -- an animation: a name (unique in the deck), the displayed percent, milliseconds per tick, and
  -- its acts, one reveal step each: a step plays the next act (`Slides.Backend.Animation`)
  animation   : String → ℕ → ℕ → List Mv.Anim → Block
  -- an animation that loops while its slide is shown
  animationLoop : String → ℕ → ℕ → Mv.Anim → Block
  -- steps over a loop: `phases` copies of the acts one after the other, the loop cycling through
  -- the phases (one per tick) while the steps play within the current one; the rests are those of
  -- one phase (`Slides.Backend.Animation`, `animateBoth`)
  animationBoth : (name : String) (percent ms phases : ℕ) → Mv.Anim → (rests : List ℚ) → Block
  -- a laid-out drawing at rest (what an animation is lowered to by `Slides.Deck.Lower`)
  still       : String → ℕ → Layout ℚ → Block
  script      : String → Block       -- JavaScript run once when its slide is shown (`slide`)
  mount       : String → Block       -- an empty element with this id, for scripts
  columns     : List (List Block) → Block
  box         : Text → List Block → Block
  fragment    : Maybe String → List Block → Block   -- a reveal.js fragment (style class)
  classed     : String → List Block → Block         -- a division with CSS classes
  placed      : (x y w h : ℕ) → List Block → Block  -- percentages of the slide

Flow : Set
Flow = List Block

bullets : Bool → List Text → Block
bullets inc ts = bulletTree inc (map leaf ts)

-- Plain text

-- a bullet is a line indented by its depth, then its sub-bullets
mutual
  plainBullet : ℕ → Bullet → List String
  plainBullet d (bullet t cs) = indent d (plainT t) ∷ plainBullets (suc d) cs
    where indent : ℕ → String → String
          indent zero    s = "- " ++ˢ s
          indent (suc n) s = "  " ++ˢ indent n s

  plainBullets : ℕ → List Bullet → List String
  plainBullets d []       = []
  plainBullets d (i ∷ is) = plainBullet d i ++ plainBullets d is

plain-flat : ∀ ts → plainBullets 0 (map leaf ts) ≡ map (λ t → "- " ++ˢ plainT t) ts
plain-flat []       = refl
plain-flat (t ∷ ts) = cong (_ ∷_) (plain-flat ts)

mutual
  plainB : Block → List String
  plainB (heading _ t)   = plainT t ∷ []
  plainB (paragraph t)   = plainT t ∷ []
  plainB (bulletTree _ is) = plainBullets 0 is
  plainB (code _ s)      = s ∷ []
  plainB (displayMath m) = toLaTeX m ∷ []
  plainB (figure _ _ c)  = plainT c ∷ []
  plainB (notes _)       = []
  plainB (table h rows)  = row h ∷ map row rows
    where row = λ cs → intersperse " | " (map plainT cs)
  plainB (references rs) = map (λ r → plainT (proj₂ r)) rs
  plainB (diagram _ _ _) = []
  plainB (animation _ _ _ _) = []
  plainB (animationLoop _ _ _ _) = []
  plainB (animationBoth _ _ _ _ _ _) = []
  plainB (still _ _ _)   = []
  plainB (script _)      = []
  plainB (mount _)       = []
  plainB (columns cs)    = plains cs
  plainB (box _ f)       = plain f
  plainB (fragment _ f)  = plain f
  plainB (classed _ f)   = plain f
  plainB (placed _ _ _ _ f) = plain f

  plain : Flow → List String
  plain []       = []
  plain (b ∷ bs) = plainB b ++ plain bs

  plains : List Flow → List String
  plains []       = []
  plains (f ∷ fs) = plain f ++ plains fs

plain-++ : ∀ xs ys → plain (xs ++ ys) ≡ plain xs ++ plain ys
plain-++ []       ys = refl
plain-++ (b ∷ xs) ys = trans (cong (plainB b ++_) (plain-++ xs ys)) (sym (ListP.++-assoc (plainB b) (plain xs) (plain ys)))
