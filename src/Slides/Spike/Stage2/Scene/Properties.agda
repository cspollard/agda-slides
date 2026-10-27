{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE (spike): no executable imports it.
--
-- What the Stage 2 container needs beyond Stage 0:
--   * `inj` is a constant (`inj-cst`): a diagram, as a scene, shows the same fold at every time;
--   * the template reading `algD` of a scene agrees with the existing `instQ`/`leafAt`
--     (`fold-algD`, `segS-sample`): a segment IS `Hold n (Drive tr (inj d))`;
--   * the embedding preserves duration (`embed-dur`).
-- Equality of timed values is pointwise (`_≈_`), so no funext.

module Slides.Spike.Stage2.Scene.Properties where

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ; _+_; _∸_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.NatQ.Properties using (ι-∸)
open import Slides.Anim.Arith using (<ᵇ-ge; <ᵇ-false)
import Data.Nat.Properties as ℕP
open import Slides.Diagram.Syntax
open import Slides.Diagram.Expr using (Expr; evalWith)
open import Slides.Diagram.Scalar using (ratOps)
open import Slides.Anim.Continuous using (Timed; seqAt; parAt; sampleAt; leafAt; instQ; _<ᵗ_)
open import Slides.Anim.Continuous.Properties using (sampleAt-dur; ι-<ᵗ; zero≤ι)
import Slides.Anim.Track as Tr
import Slides.Anim.Track.Properties as TrP
import Slides.Anim.Syntax as A
open import Slides.Spike.Timed using (TM; mapT; zipT; zipM; unitT; holdT; gather; fin2)
open import Slides.Spike.Stage2.Scene

------------------------------------------------------------------------
-- Pointwise equality of timed values, and constants

record _≈_ {A : Set} (x y : TM A) : Set where
  constructor mk≈
  field
    dur≈ : proj₁ x ≡ proj₁ y
    at≈  : ∀ τ → proj₂ x τ ≡ proj₂ y τ
open _≈_ public

cst : ∀ {A : Set} → A → TM A
cst a = 0 , λ _ → just a

------------------------------------------------------------------------
-- `rescale` only reads its children at the positions of its operation

rescale-ext : ∀ {S T} (f : S → T) o {x y : arity o → Dia T} → (∀ i → x i ≡ y i) →
              rescale f o x ≡ rescale f o y
rescale-ext f (Rectangle _ _ _)   p = refl
rescale-ext f (Disc _ _)          p = refl
rescale-ext f (Segment _ _ _)     p = refl
rescale-ext f (Text _ _ _ _)      p = refl
rescale-ext f (Spacer _ _)        p = refl
rescale-ext f (Beside al)         p = cong₂ (besideA al) (p zero) (p (suc zero))
rescale-ext f (Above al)          p = cong₂ (aboveA al) (p zero) (p (suc zero))
rescale-ext f Atop                p = cong₂ atop (p zero) (p (suc zero))
rescale-ext f LabelAbove          p = cong₂ labelAbove (p zero) (p (suc zero))
rescale-ext f LabelBelow          p = cong₂ labelBelow (p zero) (p (suc zero))
rescale-ext f (Place w h x y)     p = cong (place (f w) (f h) (f x) (f y)) (p tt)
rescale-ext f (Overlay w h)       p = cong₂ (overlay (f w) (f h)) (p zero) (p (suc zero))
rescale-ext f (Named n)           p = cong (named n) (p tt)
rescale-ext f (Connect a pa b pb s) p = cong (connectP a pa b pb s) (p tt)

-- folding `inj d` in the template algebra is `mapDia`: the template at the parameter `p`
fold-algD : ∀ d p → fold algD d p ≡ mapDia (evalWith ratOps (λ _ → p)) d
fold-algD (pure ()) p
fold-algD (impure (o , k)) p = rescale-ext _ o (λ i → fold-algD (k i) p)

------------------------------------------------------------------------
-- `inj d` is constant, in any extensional algebra

private
  zip-cst : ∀ {A : Set} {u : A → A → A} {a b c X Y} → X ≈ cst a → Y ≈ cst b → u a b ≡ c →
            zipT u X Y ≈ cst c
  zip-cst (mk≈ d p) (mk≈ e q) r = mk≈ (cong₂ ℕ._⊔_ d e) λ τ → trans (cong₂ (zipM _) (p τ) (q τ)) (cong just r)

  map-cst : ∀ {A : Set} {u : A → A} {a c X} → X ≈ cst a → u a ≡ c → mapT u X ≈ cst c
  map-cst (mk≈ d p) r = mk≈ d λ τ → trans (cong (Maybe.map _) (p τ)) (cong just r)

  fin2-ext : ∀ {A : Set} (x : Fin 2 → A) i → fin2 (x zero) (x (suc zero)) i ≡ x i
  fin2-ext x zero          = refl
  fin2-ext x (suc zero)    = refl
  fin2-ext x (suc (suc ()))

module Const {S A : Set} (α : Algebra S A) (bnd : ℚ → A → A)
             (EXT : ∀ o {x y} → (∀ i → x i ≡ y i) → α o x ≡ α o y) where

  gather-cst : ∀ o {k : arity o → TM A} {x : arity o → A} → (∀ i → k i ≈ cst (x i)) →
               gather o k (α o) ≈ cst (α o x)
  gather-cst (Rectangle _ _ _) h = mk≈ refl λ τ → cong just (EXT _ λ ())
  gather-cst (Disc _ _)        h = mk≈ refl λ τ → cong just (EXT _ λ ())
  gather-cst (Segment _ _ _)   h = mk≈ refl λ τ → cong just (EXT _ λ ())
  gather-cst (Text _ _ _ _)    h = mk≈ refl λ τ → cong just (EXT _ λ ())
  gather-cst (Spacer _ _)      h = mk≈ refl λ τ → cong just (EXT _ λ ())
  gather-cst (Beside al)  {x = x} h = zip-cst (h zero) (h (suc zero)) (EXT _ (fin2-ext x))
  gather-cst (Above al)   {x = x} h = zip-cst (h zero) (h (suc zero)) (EXT _ (fin2-ext x))
  gather-cst Atop         {x = x} h = zip-cst (h zero) (h (suc zero)) (EXT _ (fin2-ext x))
  gather-cst LabelAbove   {x = x} h = zip-cst (h zero) (h (suc zero)) (EXT _ (fin2-ext x))
  gather-cst LabelBelow   {x = x} h = zip-cst (h zero) (h (suc zero)) (EXT _ (fin2-ext x))
  gather-cst (Overlay _ _) {x = x} h = zip-cst (h zero) (h (suc zero)) (EXT _ (fin2-ext x))
  gather-cst (Place _ _ _ _) {x = x} h = map-cst (h tt) (EXT _ (λ _ → refl))
  gather-cst (Named _)       {x = x} h = map-cst (h tt) (EXT _ (λ _ → refl))
  gather-cst (Connect _ _ _ _ _) {x = x} h = map-cst (h tt) (EXT _ (λ _ → refl))

  inj-cst : ∀ d → sample α bnd (inj d) ≈ cst (fold α d)
  inj-cst (pure ())
  inj-cst (impure (o , k)) = gather-cst o (λ i → inj-cst (k i))

------------------------------------------------------------------------
-- The reader algebra is extensional (14 clauses: the reader carrier is functions, so equality of
-- children is equality of functions and `cong` is applied to the whole lambda)

algD-ext : ∀ o {x y : arity o → RD} → (∀ i → x i ≡ y i) → algD o x ≡ algD o y
algD-ext (Rectangle _ _ _)   p = refl
algD-ext (Disc _ _)          p = refl
algD-ext (Segment _ _ _)     p = refl
algD-ext (Text _ _ _ _)      p = refl
algD-ext (Spacer _ _)        p = refl
algD-ext (Beside al)         p = cong₂ (λ a b q → besideA al (a q) (b q)) (p zero) (p (suc zero))
algD-ext (Above al)          p = cong₂ (λ a b q → aboveA al (a q) (b q)) (p zero) (p (suc zero))
algD-ext Atop                p = cong₂ (λ a b q → atop (a q) (b q)) (p zero) (p (suc zero))
algD-ext LabelAbove          p = cong₂ (λ a b q → labelAbove (a q) (b q)) (p zero) (p (suc zero))
algD-ext LabelBelow          p = cong₂ (λ a b q → labelBelow (a q) (b q)) (p zero) (p (suc zero))
algD-ext (Place w h x y)     p = cong (λ a q → place _ _ _ _ (a q)) (p tt)
algD-ext (Overlay w h)       p = cong₂ (λ a b q → overlay _ _ (a q) (b q)) (p zero) (p (suc zero))
algD-ext (Named n)           p = cong (λ a q → named n (a q)) (p tt)
algD-ext (Connect a pa b pb s) p = cong (λ x q → connectP a pa b pb s (x q)) (p tt)

open Const algD bindD algD-ext using () renaming (inj-cst to inj-cstD) public

------------------------------------------------------------------------
-- A segment is `Hold n (Drive tr (inj d))`: its frames are the existing `leafAt`

private
  dur-sample : ∀ tr → proj₁ (sampleAt Tr.ℚLerp tr) ≡ Tr.dur tr
  dur-sample tr = trans (sampleAt-dur Tr.ℚLerp tr) (TrP.sample-dur Tr.ℚLerp tr)

-- the sample of a segment at τ: its template at the track's value, on [0, n)
segS-at : ∀ tr d τ → proj₂ (sample algD bindD (segS (tr , d))) τ ≡
          (if (0ℚ ℚ.≤ᵇ τ) ∧ (τ <ᵗ ι (Tr.dur tr))
           then just (bindD (proj₂ (sampleAt Tr.ℚLerp tr) τ) (fold algD d)) else nothing)
segS-at tr d τ rewrite at≈ (inj-cstD d) τ with (0ℚ ℚ.≤ᵇ τ) ∧ (τ <ᵗ ι (Tr.dur tr))
... | true  = refl
... | false = refl

segS-sample : ∀ tr d → framesD (segS (tr , d)) ≈ leafAt tr d
segS-sample tr d = mk≈ (sym (dur-sample tr)) pt
  where
    w = proj₂ (sampleAt Tr.ℚLerp tr)
    pt : ∀ τ → proj₂ (framesD (segS (tr , d))) τ ≡ proj₂ (leafAt tr d) τ
    pt τ rewrite at≈ (inj-cstD d) τ | dur-sample tr
      with (0ℚ ℚ.≤ᵇ τ) ∧ (τ <ᵗ ι (Tr.dur tr))
    ... | true  = cong just (fold-algD d (w τ))
    ... | false = refl

-- the embedding preserves duration: the duration of the sample is `Slides.Anim.Syntax.dur`
embed-dur : ∀ t → proj₁ (sample algD bindD (embed t)) ≡ A.dur (toAnim t)
embed-dur (pure s)                = refl
embed-dur (impure (A.Seq , k))    = cong₂ ℕ._+_ (embed-dur (k zero)) (embed-dur (k (suc zero)))
embed-dur (impure (A.Par , k))    = cong₂ ℕ._⊔_ (embed-dur (k zero)) (embed-dur (k (suc zero)))

------------------------------------------------------------------------
-- ℚ clock to ℕ clock: `Seq` is `seqAt` guarded to its window
seqW-tick : ∀ {A} (X Y : TM A) k →
  proj₂ (seqW X Y) (ι k) ≡
  (if k <ᵇ proj₁ X + proj₁ Y then (if k <ᵇ proj₁ X then proj₂ X (ι k) else proj₂ Y (ι (k ∸ proj₁ X))) else nothing)
seqW-tick (n , f) (m , g) k rewrite zero≤ι k | ι-<ᵗ k (n + m) with k <ᵇ n + m
... | false = refl
... | true rewrite ι-<ᵗ k n with k <ᵇ n in eq
...   | true  = refl
...   | false = cong g (sym (ι-∸ k n (<ᵇ-ge eq)))


-- beyond the end of `x ⨾ y`, the second part is beyond its own end
<ᵇ-shift-false : ∀ {k} n m → (k <ᵇ n + m) ≡ false → (k ∸ n <ᵇ m) ≡ false
<ᵇ-shift-false {k} n m h =
  <ᵇ-false (ℕP.≤-trans (ℕP.≤-reflexive (sym (ℕP.m+n∸m≡n n m))) (ℕP.∸-monoˡ-≤ n (<ᵇ-ge h)))
