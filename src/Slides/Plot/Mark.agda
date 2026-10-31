{-# OPTIONS --safe --without-K #-}

-- What a plot shows: marks in data coordinates, each with a style and an optional legend entry.
-- A mark has no sub-terms, so `MarkC` is a signature of commands of arity ⊥ (as `CurveC` is), and a
-- plot's content is a list of marks (overlay is `++`).  `Slides.Plot.Render.renderMark` lowers it.
--
--   line     a polyline through the points            scatter  a filled dot at each point
--   steps    a filled histogram: bin edges (n + 1) and heights (n), as one closed polygon
--   band     a filled region between a lower and an upper curve, (x, lo, hi) at each x
--   bars     a vertical bar with caps at each (x, lo, hi); `errors` writes them as (x, y, err)
--   hline vline   a reference line across the whole plot
--   note     text at a data position
--   exact    the graph of a function, sampled and drawn as a smooth curve (`Slides.Diagram.Curve`)
--
-- A mark is functorial in the type of its x and y coordinates (`bimap`, `zipWith`), so a map of
-- values is a map of marks: `logMark` maps `log₁₀` over the y's and `lerpMark` zips with `lerp`.
-- The function of `exact` is read at an x in data coordinates (ℚ), so only its values are mapped.

module Slides.Plot.Mark where

open import Level using (0ℓ)
open import Data.Container.Core using (Container; _▷_)
open import Data.Empty using (⊥)
open import Data.List using (List; map; zipWith)
open import Data.List.Properties using (map-id; map-∘)
open import Data.Maybe using (Maybe)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational using (ℚ; _+_; _-_)
open import Data.String using (String)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Slides.Diagram.Style using (Style)

data Mark (X Y : Set) : Set where
  line scatter : Style → List (X × Y) → Mark X Y
  steps        : Style → List X → List Y → Mark X Y
  band bars    : Style → List (X × Y × Y) → Mark X Y
  hline        : Style → Y → Mark X Y
  vline        : Style → X → Mark X Y
  note         : X → Y → String → Mark X Y
  exact        : Style → (ℚ → Y) → Mark X Y

-- error bars at (x, y, err): the ends are y ∓ err
errors : ∀ {X} → Style → List (X × ℚ × ℚ) → Mark X ℚ
errors s = bars s ∘ map (λ { (x , y , e) → x , y - e , y + e })

MarkC : Container 0ℓ 0ℓ
MarkC = Mark ℚ ℚ ▷ λ _ → ⊥

bimap : ∀ {X X′ Y Y′} → (X → X′) → (Y → Y′) → Mark X Y → Mark X′ Y′
bimap f g (line s ps)     = line s (map (λ { (x , y) → f x , g y }) ps)
bimap f g (scatter s ps)  = scatter s (map (λ { (x , y) → f x , g y }) ps)
bimap f g (steps s es hs) = steps s (map f es) (map g hs)
bimap f g (band s ts)     = band s (map (λ { (x , l , h) → f x , g l , g h }) ts)
bimap f g (bars s ts)     = bars s (map (λ { (x , l , h) → f x , g l , g h }) ts)
bimap f g (hline s y)     = hline s (g y)
bimap f g (vline s x)     = vline s (f x)
bimap f g (note x y t)    = note (f x) (g y) t
bimap f g (exact s h)     = exact s (λ x → g (h x))

zipWith⁺ : ∀ {X Y} → (X → X → X) → (Y → Y → Y) → Mark X Y → Mark X Y → Mark X Y
zipWith⁺ f g (line s ps)     (line _ qs)     = line s (zipWith (λ { (x , y) (x′ , y′) → f x x′ , g y y′ }) ps qs)
zipWith⁺ f g (scatter s ps)  (scatter _ qs)  = scatter s (zipWith (λ { (x , y) (x′ , y′) → f x x′ , g y y′ }) ps qs)
zipWith⁺ f g (steps s es hs) (steps _ es′ hs′) = steps s (zipWith f es es′) (zipWith g hs hs′)
zipWith⁺ f g (band s ts)     (band _ us)     = band s (zipWith (λ { (x , l , h) (x′ , l′ , h′) → f x x′ , g l l′ , g h h′ }) ts us)
zipWith⁺ f g (bars s ts)     (bars _ us)     = bars s (zipWith (λ { (x , l , h) (x′ , l′ , h′) → f x x′ , g l l′ , g h h′ }) ts us)
zipWith⁺ f g (hline s y)     (hline _ y′)    = hline s (g y y′)
zipWith⁺ f g (vline s x)     (vline _ x′)    = vline s (f x x′)
zipWith⁺ f g (note x y t)    (note x′ y′ _)  = note (f x x′) (g y y′) t
zipWith⁺ f g (exact s h)     (exact _ h′)    = exact s (λ x → g (h x) (h′ x))
zipWith⁺ f g m               _               = m

bimap-id : ∀ {X Y} (m : Mark X Y) → bimap (λ x → x) (λ y → y) m ≡ m
bimap-id (line s ps)     = cong (line s) (map-id ps)
bimap-id (scatter s ps)  = cong (scatter s) (map-id ps)
bimap-id (steps s es hs) = cong₂ (steps s) (map-id es) (map-id hs)
bimap-id (band s ts)     = cong (band s) (map-id ts)
bimap-id (bars s ts)     = cong (bars s) (map-id ts)
bimap-id (hline s y)     = refl
bimap-id (vline s x)     = refl
bimap-id (note x y t)    = refl
bimap-id (exact s h)     = refl

bimap-∘ : ∀ {X X′ X″ Y Y′ Y″} (f : X → X′) (f′ : X′ → X″) (g : Y → Y′) (g′ : Y′ → Y″) (m : Mark X Y) →
          bimap (λ x → f′ (f x)) (λ y → g′ (g y)) m ≡ bimap f′ g′ (bimap f g m)
bimap-∘ f f′ g g′ (line s ps)     = cong (line s) (map-∘ ps)
bimap-∘ f f′ g g′ (scatter s ps)  = cong (scatter s) (map-∘ ps)
bimap-∘ f f′ g g′ (steps s es hs) = cong₂ (steps s) (map-∘ es) (map-∘ hs)
bimap-∘ f f′ g g′ (band s ts)     = cong (band s) (map-∘ ts)
bimap-∘ f f′ g g′ (bars s ts)     = cong (bars s) (map-∘ ts)
bimap-∘ f f′ g g′ (hline s y)     = refl
bimap-∘ f f′ g g′ (vline s x)     = refl
bimap-∘ f f′ g g′ (note x y t)    = refl
bimap-∘ f f′ g g′ (exact s h)     = refl

record Series : Set where
  constructor series
  field
    mark   : Mark ℚ ℚ
    legend : Maybe String
