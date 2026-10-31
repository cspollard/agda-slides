{-# OPTIONS --safe --without-K #-}

-- Fragments in the elements that hold drawings: a `still`, a `diagram`, an animation.
--
-- The class attributes of the SVG come from the drawings' style strings (`Slides.Diagram.Style.cls`),
-- which `Slides.Diagram.Print` copies into the elements it writes.  `svg?` is the one condition on
-- them: the printed `<svg>` has no element whose class has the token `fragment` (decidable by
-- computation).  Given it, the wrapper `div`s are counted exactly, and an animation is its
-- `rests`: one `span.fragment.anim-step` per reveal step.
--
--   `still-count`      a still holds the fragments of its SVG
--   `animation-count`  an animation holds the fragments of its first frame, then one per rest
--
-- `animationEl` builds its attributes in local functions, so `animationEl′` restates it with
-- them named; `animationEl≡` (by `refl`) keeps the restatement honest.

module Slides.Backend.Render.Svg where

open import Data.Bool.Base using (Bool; true; false; T)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product.Base using (_,_)
open import Data.Rational using (ℚ)
open import Data.String.Base using (String) renaming (_++_ to _++ˢ_)
open import Data.XML.AST using (XMLDoc)
open import Data.JSON.Print using (renderJSON)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
import Data.Nat.Properties as ℕP

open import Slides.Scalar.Model.Rat using (ratSpace; ratTime; ratCoupling)
import Slides.Scene.Moving ratSpace ratTime ratCoupling as Mv
open import Slides.Backend.HTML using (hElement; hText; Attrs)
open import Slides.Backend.Animation using (firstFrame; animationEl; stillEl; Play; steps; loop; both; qPrint; qⱼ; arr; eventsJSON; htmlSafe)
open import Slides.Diagram.Print using (Print; renderSVG)
open import Slides.Diagram.Draw using (Layout)
open import Slides.Backend.Fragments

-- the printed SVG has no fragment
svg? : ∀ {S} → Print S → String → ℕ → Layout S → Bool
svg? P n pct l = fragCount (renderSVG P n pct l) ≡ᵇ 0

svg-zero : ∀ {S} (P : Print S) n pct l → T (svg? P n pct l) → fragCount (renderSVG P n pct l) ≡ 0
svg-zero P n pct l h = ℕP.≡ᵇ⇒≡ _ _ h

-- a still: a `div.diagram` around its SVG
still-count : ∀ n pct l → T (svg? qPrint n pct l) → fragCount (stillEl n pct l) ≡ 0
still-count n pct l h =
  trans (hElement-count "div" (("class" , "diagram") ∷ ("id" , n) ∷ []) (renderSVG qPrint n pct l ∷ []))
        (cong (λ x → 0 + (x + 0)) (svg-zero qPrint n pct l h))

-- the element of an animation, its attributes named
private
  restsAttr : List ℚ → Attrs
  restsAttr []        = []
  restsAttr r@(_ ∷ _) = ("data-rests" , renderJSON (arr (map qⱼ r))) ∷ []

  playAttr : Play → Attrs
  playAttr steps    = []
  playAttr loop     = ("data-loop" , "") ∷ []
  playAttr (both n) = ("data-loop" , "") ∷ ("data-phases" , show n) ∷ []

  animAttrs : String → ℕ → Play → Mv.Anim → List ℚ → Attrs
  animAttrs name ms play a rs =
    ("class" , "animation") ∷ ("id" , name ++ˢ "-frames") ∷ ("data-ms" , show ms)
    ∷ ("data-duration" , renderJSON (qⱼ (Mv.duration a))) ∷ restsAttr rs ++ playAttr play

  animKids : String → ℕ → Mv.Anim → List ℚ → List XMLDoc
  animKids name pct a rs =
    hElement "div" (("class" , "frame") ∷ [])
      ( hElement "div" (("class" , "diagram") ∷ ("id" , name) ∷ [])
          (renderSVG qPrint name pct (firstFrame a) ∷ []) ∷ [] )
    ∷ hText "script" (("type" , "application/json") ∷ ("class" , "events") ∷ []) (htmlSafe (eventsJSON a))
    ∷ map (λ _ → hElement "span" (("class" , "fragment anim-step") ∷ []) []) rs

  animationEl≡ : ∀ name pct ms play a rs →
                 animationEl name pct ms play a rs ≡ hElement "div" (animAttrs name ms play a rs) (animKids name pct a rs)
  animationEl≡ name pct ms steps    a []      = refl
  animationEl≡ name pct ms loop     a []      = refl
  animationEl≡ name pct ms (both k) a []      = refl
  animationEl≡ name pct ms steps    a (_ ∷ _) = refl
  animationEl≡ name pct ms loop     a (_ ∷ _) = refl
  animationEl≡ name pct ms (both k) a (_ ∷ _) = refl

  -- no class of the attributes has a fragment
  anim-hit : ∀ name ms play a rs → attrHit (animAttrs name ms play a rs) ≡ 0
  anim-hit name ms steps     a []      = refl
  anim-hit name ms loop      a []      = refl
  anim-hit name ms (both k)  a []      = refl
  anim-hit name ms steps     a (_ ∷ _) = refl
  anim-hit name ms loop      a (_ ∷ _) = refl
  anim-hit name ms (both k)  a (_ ∷ _) = refl

  -- each rest is one fragment
  span-count : ∀ {A : Set} (rs : List A) →
               forestCount (map (λ _ → hElement "span" (("class" , "fragment anim-step") ∷ []) []) rs) ≡ length rs
  span-count []       = refl
  span-count (_ ∷ rs) = cong suc (span-count rs)

  -- the frame, the data and the rests of an animation
  kids-count : ∀ name pct a rs → fragCount (renderSVG qPrint name pct (firstFrame a)) ≡ 0 →
               forestCount (animKids name pct a rs) ≡ length rs
  kids-count name pct a rs h =
    cong₂ _+_ (trans (hElement-count "div" (("class" , "frame") ∷ [])
                        (hElement "div" (("class" , "diagram") ∷ ("id" , name) ∷ []) (renderSVG qPrint name pct (firstFrame a) ∷ []) ∷ []))
                     (cong (λ x → 0 + (x + 0)) diagram-zero))
              (cong₂ _+_ (hText-count "script" (("type" , "application/json") ∷ ("class" , "events") ∷ []) (htmlSafe (eventsJSON a))) (span-count rs))
    where
      diagram-zero : fragCount (hElement "div" (("class" , "diagram") ∷ ("id" , name) ∷ [])
                                  (renderSVG qPrint name pct (firstFrame a) ∷ [])) ≡ 0
      diagram-zero = trans (hElement-count "div" (("class" , "diagram") ∷ ("id" , name) ∷ []) (renderSVG qPrint name pct (firstFrame a) ∷ [])) (cong (λ x → 0 + (x + 0)) h)

  -- an animation: the fragments of its first frame, then one per rest
  animation-count′ : ∀ name pct ms play a rs → fragCount (renderSVG qPrint name pct (firstFrame a)) ≡ 0 →
                     fragCount (animationEl name pct ms play a rs) ≡ length rs
  animation-count′ name pct ms play a rs h =
    trans (cong fragCount (animationEl≡ name pct ms play a rs))
          (trans (hElement-count "div" (animAttrs name ms play a rs) (animKids name pct a rs))
                 (cong₂ _+_ (anim-hit name ms play a rs) (kids-count name pct a rs h)))

animation-count : ∀ name pct ms play a rs → T (svg? qPrint name pct (firstFrame a)) →
                  fragCount (animationEl name pct ms play a rs) ≡ length rs
animation-count name pct ms play a rs h = animation-count′ name pct ms play a rs (svg-zero qPrint name pct (firstFrame a) h)
