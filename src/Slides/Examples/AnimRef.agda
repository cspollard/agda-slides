{-# OPTIONS --safe --without-K #-}

-- Animations for checking the page evaluator against Agda (`make test-anim-ref`).
--
-- `animations` are shipped as in any deck; `reference` computes, with `Slides.Scene.Animation.frameAt`
-- (the exact semantics, in ℚ), the drawing commands of each animation at every quarter tick of its
-- duration, as JSON for `tests/browser/anim-ref.mjs`: for each animation a list of
-- `{"t": time, "ds": [[tag, [numbers]]...]}` with the numbers as the page prints them.

module Slides.Examples.AnimRef where

open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ) renaming (_*_ to _*ℚ_)
import Data.Rational as ℚ
open import Data.String using (String)
open import Data.JSON.AST using (JSON; objectFromList; stringⱼ; arrayⱼ; nullⱼ)
open import Data.JSON.Print using (renderJSON)

open import Slides.Scalar.Model.Rat using (ratTime; ι)
open import Slides.Scalar.Time using (Time)
open import Slides.Deck.Talk using (Talk)
open import Slides.Deck.DSL
open import Slides.Deck.Anim
import Slides.Diagram.Syntax as D
open import Slides.Diagram.Geometry using (east; west)
open import Slides.Diagram.Draw using (Draw; rect; circle; line; arrow; label; path; group; Layout)
open import Slides.Backend.Animation using (qⱼ; natⱼ)
open import Slides.Examples.Intro using (mover; counter)

-- a box easing right, a label that moves with it, an arrow between two named boxes
slider : Anim
slider = tween Linear (ι 0) (ι 120) (ι 6)
  (D.beside (D.spacer now (lit 0)) (D.named "s" (D.rectangle (lit 40) (lit 30) (filled "#c96" defaultStyle))))

stepper : Anim
stepper = tween Step (ι 0) (ι 50) (ι 4)
  (D.beside (D.spacer now (lit 0)) (D.framed (lit 40) (lit 30) defaultStyle (txt 16 "x_i^2" defaultStyle)))

linked : Anim
linked = frame′ 2 (D.connect "a" east "b" west defaultStyle
           (D.beside (D.named "a" (D.rectangle (lit 20) (lit 20) defaultStyle))
                     (D.beside (D.spacer (lit 30) (lit 0)) (D.named "b" (D.disc (lit 10) defaultStyle)))))

named-anims : List (String × Anim)
named-anims =
    ("mover" , mover ∥ counter) ∷ ("slider" , slider) ∷ ("stepper" , stepper) ∷ ("linked" , linked) ∷ []

animations : Talk
animations = do
  slide (do heading 2 "mover";   animate "mover" 60 100 ((mover ∥ counter) ∷ []))
  slide (do heading 2 "slider";  animate "slider" 60 100 (slider ∷ []))
  slide (do heading 2 "stepper"; animate "stepper" 60 100 (stepper ∷ []))
  slide (do heading 2 "linked";  animate "linked" 60 100 (linked ∷ []))

------------------------------------------------------------------------
-- The reference frames

private
  half : ℚ → JSON
  half x = qⱼ (ℚ.½ *ℚ x)

  nums : List JSON → JSON
  nums = arrayⱼ

  cmd : String → List JSON → JSON
  cmd t xs = arrayⱼ (stringⱼ t ∷ nums xs ∷ [])

  drawⱼ : Draw ℚ → List JSON
  drawⱼ (rect x y w h _)    = cmd "rect" (half x ∷ half y ∷ qⱼ w ∷ qⱼ h ∷ []) ∷ []
  drawⱼ (circle x y r _)    = cmd "circle" (half x ∷ half y ∷ qⱼ r ∷ []) ∷ []
  drawⱼ (line a b c d _)    = cmd "line" (half a ∷ half b ∷ half c ∷ half d ∷ []) ∷ []
  drawⱼ (arrow a b c d _)   = cmd "line" (half a ∷ half b ∷ half c ∷ half d ∷ []) ∷ []
  drawⱼ (label x y _ _ _)   = cmd "text" (half x ∷ half y ∷ []) ∷ []
  drawⱼ (path _ _ _ _)      = []
  drawⱼ (group _ _ _)       = []

  drawsⱼ : List (Draw ℚ) → List JSON
  drawsⱼ []       = []
  drawsⱼ (d ∷ ds) = drawⱼ d ++ drawsⱼ ds

  layoutⱼ : Maybe (Layout ℚ) → JSON
  layoutⱼ nothing  = nullⱼ
  layoutⱼ (just l) = arrayⱼ (drawsⱼ (Layout.draws l))

  at : Anim → ℕ → JSON
  at a k = objectFromList (("t" , qⱼ t) ∷ ("ds" , layoutⱼ (frameAt a t)) ∷ [])
    where t = ι k *ℚ ℚ.½ *ℚ ℚ.½

  upto : Anim → ℕ → List JSON
  upto a zero    = at a zero ∷ []
  upto a (suc n) = upto a n ++ at a (suc n) ∷ []

  -- up to the duration, rounded up to whole ticks
  ticks : Anim → ℕ
  ticks a = 4 * suc (Time.floor ratTime (duration a))

reference : String
reference = renderJSON (objectFromList (map (λ p → proj₁ p , arrayⱼ (upto (proj₂ p) (ticks (proj₂ p)))) named-anims))
