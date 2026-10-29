{-# OPTIONS --safe --without-K #-}

-- Lowerings of the deck vocabulary: for a backend that lacks a feature.
--
-- A lowering replaces each block by a flow (`Lowering = Block → Flow`: speaker notes by nothing,
-- an animation by its last frame).  `lowerFlow` extends it to every place blocks occur (columns,
-- boxes, fragments, styled and placed divisions), and `lowerTalk` to the chunks of every slide.
-- A lowering acts on the leaf blocks; the containers are rebuilt around the lowered contents.
--
--   lowerFlow-++    `lowerFlow l` is a monoid homomorphism of flows (`concatMap` of the blocks)
--   lowerFlow-id    the identity lowering is the identity
--   lowerFlow-fuse  lowerings compose before they are lifted: `lowerFlow (l₁ ⋙ l₂)` is
--                   `lowerFlow l₂ ∘ lowerFlow l₁`, so a backend lacking several features applies
--                   one combined lowering
--
-- The chunks of a slide are lowered one by one, so a pause survives its content (`slides-lower`:
-- the slides of a lowered talk are the lowered slides).

module Slides.Deck.Lower where

open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.NonEmpty using (List⁺; _∷_)
import Data.List.NonEmpty as L⁺
open import Data.Nat.Base using (ℕ)
open import Data.Rational using (ℚ)
open import Data.String.Base using (String)
import Data.List.Properties as ListP
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

open import Slides.Deck.Content
open import Slides.Deck.Syntax
open import Slides.Deck.Talk
open import Slides.Deck.Anim using (sequence; layoutAt; lastTick; totalDuration; zeroQ)

Lowering : Set
Lowering = Block → Flow

------------------------------------------------------------------------
-- Lifting a lowering of blocks to flows

module _ (l : Lowering) where
  mutual
    lowerBlock : Block → Flow
    lowerBlock (columns cs)       = columns (lowerFlows cs) ∷ []
    lowerBlock (box t f)          = box t (lowerFlow f) ∷ []
    lowerBlock (fragment s f)     = fragment s (lowerFlow f) ∷ []
    lowerBlock (classed c f)      = classed c (lowerFlow f) ∷ []
    lowerBlock (placed x y w h f) = placed x y w h (lowerFlow f) ∷ []
    lowerBlock b                  = l b

    lowerFlow : Flow → Flow
    lowerFlow []       = []
    lowerFlow (b ∷ bs) = lowerBlock b ++ lowerFlow bs

    lowerFlows : List Flow → List Flow
    lowerFlows []       = []
    lowerFlows (f ∷ fs) = lowerFlow f ∷ lowerFlows fs

  lowerFlow-++ : ∀ xs ys → lowerFlow (xs ++ ys) ≡ lowerFlow xs ++ lowerFlow ys
  lowerFlow-++ []       ys = refl
  lowerFlow-++ (b ∷ xs) ys = trans (cong (lowerBlock b ++_) (lowerFlow-++ xs ys)) (sym (ListP.++-assoc (lowerBlock b) (lowerFlow xs) (lowerFlow ys)))

-- the identity lowering, and composition: the second lowering runs over the result of the first
idL : Lowering
idL b = b ∷ []

infixl 5 _⋙_
_⋙_ : Lowering → Lowering → Lowering
(l₁ ⋙ l₂) b = lowerFlow l₂ (l₁ b)

mutual
  lowerFlow-id : ∀ f → lowerFlow idL f ≡ f
  lowerFlow-id []       = refl
  lowerFlow-id (b ∷ bs) = cong₂ _++_ (lowerBlock-id b) (lowerFlow-id bs)

  lowerBlock-id : ∀ b → lowerBlock idL b ≡ b ∷ []
  lowerBlock-id (columns cs)       = cong (λ x → columns x ∷ []) (lowerFlows-id cs)
  lowerBlock-id (box t f)          = cong (λ x → box t x ∷ []) (lowerFlow-id f)
  lowerBlock-id (fragment s f)     = cong (λ x → fragment s x ∷ []) (lowerFlow-id f)
  lowerBlock-id (classed c f)      = cong (λ x → classed c x ∷ []) (lowerFlow-id f)
  lowerBlock-id (placed x y w h f) = cong (λ z → placed x y w h z ∷ []) (lowerFlow-id f)
  lowerBlock-id (heading _ _)      = refl
  lowerBlock-id (paragraph _)      = refl
  lowerBlock-id (bullets _ _)      = refl
  lowerBlock-id (code _ _)         = refl
  lowerBlock-id (displayMath _)    = refl
  lowerBlock-id (figure _ _ _)     = refl
  lowerBlock-id (notes _)          = refl
  lowerBlock-id (table _ _)        = refl
  lowerBlock-id (references _)     = refl
  lowerBlock-id (diagram _ _ _)    = refl
  lowerBlock-id (animation _ _ _ _) = refl
  lowerBlock-id (animationLoop _ _ _ _) = refl
  lowerBlock-id (animationBoth _ _ _ _ _ _) = refl
  lowerBlock-id (still _ _ _)      = refl
  lowerBlock-id (script _)         = refl
  lowerBlock-id (mount _)          = refl

  lowerFlows-id : ∀ fs → lowerFlows idL fs ≡ fs
  lowerFlows-id []       = refl
  lowerFlows-id (f ∷ fs) = cong₂ _∷_ (lowerFlow-id f) (lowerFlows-id fs)

private
  single : ∀ l b → lowerFlow l (b ∷ []) ≡ lowerBlock l b
  single l b = ListP.++-identityʳ (lowerBlock l b)

mutual
  lowerFlow-fuse : ∀ l₁ l₂ f → lowerFlow (l₁ ⋙ l₂) f ≡ lowerFlow l₂ (lowerFlow l₁ f)
  lowerFlow-fuse l₁ l₂ []       = refl
  lowerFlow-fuse l₁ l₂ (b ∷ bs) =
    trans (cong₂ _++_ (lowerBlock-fuse l₁ l₂ b) (lowerFlow-fuse l₁ l₂ bs))
          (sym (lowerFlow-++ l₂ (lowerBlock l₁ b) (lowerFlow l₁ bs)))

  lowerBlock-fuse : ∀ l₁ l₂ b → lowerBlock (l₁ ⋙ l₂) b ≡ lowerFlow l₂ (lowerBlock l₁ b)
  lowerBlock-fuse l₁ l₂ (columns cs)       = trans (cong (λ x → columns x ∷ []) (lowerFlows-fuse l₁ l₂ cs)) (sym (single l₂ (columns (lowerFlows l₁ cs))))
  lowerBlock-fuse l₁ l₂ (box t f)          = trans (cong (λ x → box t x ∷ []) (lowerFlow-fuse l₁ l₂ f)) (sym (single l₂ (box t (lowerFlow l₁ f))))
  lowerBlock-fuse l₁ l₂ (fragment s f)     = trans (cong (λ x → fragment s x ∷ []) (lowerFlow-fuse l₁ l₂ f)) (sym (single l₂ (fragment s (lowerFlow l₁ f))))
  lowerBlock-fuse l₁ l₂ (classed c f)      = trans (cong (λ x → classed c x ∷ []) (lowerFlow-fuse l₁ l₂ f)) (sym (single l₂ (classed c (lowerFlow l₁ f))))
  lowerBlock-fuse l₁ l₂ (placed x y w h f) = trans (cong (λ z → placed x y w h z ∷ []) (lowerFlow-fuse l₁ l₂ f)) (sym (single l₂ (placed x y w h (lowerFlow l₁ f))))
  lowerBlock-fuse l₁ l₂ (heading _ _) = refl
  lowerBlock-fuse l₁ l₂ (paragraph _) = refl
  lowerBlock-fuse l₁ l₂ (bullets _ _) = refl
  lowerBlock-fuse l₁ l₂ (code _ _) = refl
  lowerBlock-fuse l₁ l₂ (displayMath _) = refl
  lowerBlock-fuse l₁ l₂ (figure _ _ _) = refl
  lowerBlock-fuse l₁ l₂ (notes _) = refl
  lowerBlock-fuse l₁ l₂ (table _ _) = refl
  lowerBlock-fuse l₁ l₂ (references _) = refl
  lowerBlock-fuse l₁ l₂ (diagram _ _ _) = refl
  lowerBlock-fuse l₁ l₂ (animation _ _ _ _) = refl
  lowerBlock-fuse l₁ l₂ (animationLoop _ _ _ _) = refl
  lowerBlock-fuse l₁ l₂ (animationBoth _ _ _ _ _ _) = refl
  lowerBlock-fuse l₁ l₂ (still _ _ _) = refl
  lowerBlock-fuse l₁ l₂ (script _) = refl
  lowerBlock-fuse l₁ l₂ (mount _) = refl

  lowerFlows-fuse : ∀ l₁ l₂ fs → lowerFlows (l₁ ⋙ l₂) fs ≡ lowerFlows l₂ (lowerFlows l₁ fs)
  lowerFlows-fuse l₁ l₂ []       = refl
  lowerFlows-fuse l₁ l₂ (f ∷ fs) = cong₂ _∷_ (lowerFlow-fuse l₁ l₂ f) (lowerFlows-fuse l₁ l₂ fs)

------------------------------------------------------------------------
-- Slides and talks

lowerSlide : Lowering → Slide → Slide
lowerSlide l (slide lab cs) = slide lab (L⁺.map (lowerFlow l) cs)

lowerPart : Lowering → Part → Part
lowerPart l (solo o s)    = solo o (lowerSlide l s)
lowerPart l (vstack o ss) = vstack o (L⁺.map (lowerSlide l) ss)

lowerTalk : Lowering → Talk → Talk
lowerTalk l = map (lowerPart l)

-- the grouping is untouched: the slides of a lowered talk are the lowered slides
slides-lower : ∀ l t → slides (lowerTalk l t) ≡ map (lowerSlide l) (slides t)
slides-lower l []       = refl
slides-lower l (solo o s ∷ t)    = cong (lowerSlide l s ∷_) (slides-lower l t)
slides-lower l (vstack o (s ∷ ss) ∷ t) =
  trans (cong (λ r → lowerSlide l s ∷ map (lowerSlide l) ss ++ r) (slides-lower l t))
        (cong (lowerSlide l s ∷_) (sym (ListP.map-++ (lowerSlide l) ss (slides t))))

------------------------------------------------------------------------
-- The lowerings

-- drop the speaker notes
stripNotes : Lowering
stripNotes (notes _) = []
stripNotes b         = b ∷ []

-- drop the scripts and the elements they draw into, for a backend without JavaScript
stripScripts : Lowering
stripScripts (script _) = []
stripScripts (mount _)  = []
stripScripts b          = b ∷ []

-- replace each diagram and animation by a one-line placeholder, for a backend without vector
-- graphics
diagramPlaceholder : Lowering
diagramPlaceholder (diagram _ _ _)  = paragraph (text "[diagram]" ∷ []) ∷ []
diagramPlaceholder (still _ _ _)    = paragraph (text "[diagram]" ∷ []) ∷ []
diagramPlaceholder (animation _ _ _ _) = paragraph (text "[animation]" ∷ []) ∷ []
diagramPlaceholder (animationLoop _ _ _ _) = paragraph (text "[animation]" ∷ []) ∷ []
diagramPlaceholder (animationBoth _ _ _ _ _ _) = paragraph (text "[animation]" ∷ []) ∷ []
diagramPlaceholder b                = b ∷ []

-- for a backend that cannot play animations (print, a script-free page): an animation as a still
-- of its final frame, the picture the audience is left with: the last tick of the last act (of the
-- first phase, for steps over a loop), the first frame for a loop
animationFinal : Lowering
animationFinal (animation n p ms [])      = []
animationFinal (animation n p ms (a ∷ as)) =
  still n p (layoutAt (sequence (a ∷ as)) (lastTick (totalDuration (a ∷ as)))) ∷ []
animationFinal (animationLoop n p ms a)   = still n p (layoutAt a 0) ∷ []
animationFinal (animationBoth n p ms k a rs) = still n p (layoutAt a (lastTick (lastRest rs))) ∷ []
  where lastRest : List ℚ → ℚ
        lastRest []       = zeroQ
        lastRest (r ∷ []) = r
        lastRest (_ ∷ r ∷ rs) = lastRest (r ∷ rs)
animationFinal b                          = b ∷ []
