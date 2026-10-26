{-# OPTIONS --safe --without-K #-}

-- Continuous time for template animations: the specification the page implements.
--
-- An animation of templates (every segment a `SegBody.template`, `Slides.Anim.Syntax`) is
-- played in real time `τ`, measured in ticks.  The page receives each segment's track as data
-- and the symbolic layout (`Slides.Anim.Param`); this module says what it must draw.
--
-- The formulation.
--
--   * Time is a `ℚ`.  A track sampled at real time is `sampleAt`, the algebra of the track's
--     free monad into `Timed A = ℕ × (ℚ → A)` (the duration and a function of time): a piece
--     is `Lerp (progress e (τ/d))` (`Slides.Anim.Track`, unchanged), and `Seq` is `seqAt`,
--     which switches to the second function at the boundary and offsets its time by the first
--     duration.  Pieces are half-open, so the sample is right-continuous: at a boundary the
--     later piece holds (`seqAt-boundary`), and a piece holds its `to` once over
--     (`piece-hold`).  Time starts at 0; a segment shows nothing outside `[0, ticks)`.
--   * The parameter of a template is a ℚ and is *not* floored: `instQ d q` evaluates the
--     template's `Expr ⊤` in `ratOps` with `t := q`.  `Expr` is unchanged (its signature has
--     no new operation): `evalWith` is already generic in the scalar, `evalWith ratOps ρ` is
--     an `Ops`-homomorphism (`evalWith-hom`) and layout is natural along it
--     (`layout-natural`), so the continuous frame is the evaluation in ℚ of the very symbolic
--     layout the page is sent.  There is no `units` (floor) operation to add: the continuous
--     semantics has none, the page draws fractional coordinates, and the floor belongs only to
--     the discrete reading `bodyAt` (`units q`).
--   * An animation is `animAt`, the `foldA` of the segments into `Timed (Maybe (Dia ℚ))`:
--     `Par` is `parAt` (the same `τ` on both sides, duration the maximum, frames overlaid with
--     `atop` and a side that is not running contributing nothing, as `Slides.Anim.Timeline.merge`)
--     and `Seq` is `seqAt`.  `frameAt a τ` is the layout in ℚ (`Slides.Diagram.Layout`
--     at `ratOps`) of the diagram running at `τ`.
--
-- Where the discrete (ℕ) and continuous (ℚ) readings differ, honestly.  ℚ's `-` is real
-- subtraction where ℕ's is the monus, ℚ's percentage is exact where ℕ's rounds down, and the
-- discrete parameter is floored.  So `100 ⊖ t` is negative in ℚ once `t > 100` (the frame has
-- a negative size, which `Slides.Diagram.Valid` excludes; a template should stay in the
-- domain where its differences are non-negative) and a ℕ frame at the floor of a fractional
-- sample differs from the ℚ frame at the sample itself.
--
-- Proved here.
--   * `sampleAt-ι`: at whole ticks the continuous sample of a track is the discrete one
--     (`Slides.Anim.Track.sample`), exactly; so is `leafAt-ι` for a segment's frame.
--   * `leaf-tick`: if moreover the sample is a whole number and the template's layout is exact
--     (`Slides.Diagram.ExprQ.Faithful`: differences with minuend ≥ subtrahend, percentages that
--     divide), the continuous frame at tick `k` is the discrete frame sent through `ι`.
--   * `parAt-time`, `parAt-dur`, `seqAt-before`, `seqAt-after`, `seqAt-boundary`: `Par` is the
--     same `τ` on both sides and `Seq` offsets time by the duration; `animAt-dur`: the
--     duration is `Slides.Anim.Syntax.dur`.
--   * `piece-hold`, `piece-start`: the sample is `from` at a piece's start and `to` after its end.
--
-- Not proved: that the page's JavaScript (floating point easings, the formula evaluator)
-- computes `frameAt`; it is tested at sampled times against the exact values
-- (`tests/browser/anim-ref.mjs`).  Nor is the assembly of the symbolic phases proved: that for
-- `k ≤ τ < k+1` `frameAt a τ` is the symbolic layout of tick `k` evaluated at each segment's
-- sample at `τ - start`.

module Slides.Anim.Continuous where

open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_; T)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Unit using (⊤)
open import Data.Integer as ℤ using (+_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; _/_)
import Data.Rational.Properties as ℚP
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Data.Fin using (zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Slides.Diagram.NatQ using (ι; ι-≤ᵇ; ι-∸; ι-ratio)
import Slides.Anim.Track as Tr
open import Slides.Anim.Syntax using (units; bodyAt; Anim; Seg; SegBody; foldA; track; content; template; blackBox; dur; Op; Seq; Par)
open import Slides.Diagram.Draw using (Layout; mapLayout)
open import Slides.Diagram.ExprQ using (AllLayout; Faithful; faithful-layout)
open import Slides.Diagram.Expr using (Expr; evalWith; exprOps)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (ratOps; natOps)
open import Slides.Diagram.Syntax using (Dia; atop; mapDia)

------------------------------------------------------------------------
-- Real time on a track

-- strict comparison of times
_<ᵗ_ : ℚ → ℚ → Bool
τ <ᵗ σ = not (σ ℚ.≤ᵇ τ)

-- how far through `d` ticks the time `τ` is (clamped above; a negative time never reaches a
-- piece, see `leafAt`)
ratioAt : ℚ → ℕ → ℚ
ratioAt τ zero    = 1ℚ
ratioAt τ (suc d) = if τ <ᵗ ι (suc d) then τ ℚ.* (+ 1 / suc d) else 1ℚ

pieceAt : ∀ {A} → Tr.Lerp A → Tr.Piece A → ℚ → A
pieceAt L (Tr.piece d a b e) τ = Tr.Lerp.lerp L (Tr.progress e (ratioAt τ d)) a b

-- a length in ticks and a function of real time
Timed : Set → Set
Timed A = ℕ × (ℚ → A)

seqAt : ∀ {A} → Timed A → Timed A → Timed A
seqAt (n , f) (m , g) = n ℕ.+ m , λ τ → if τ <ᵗ ι n then f τ else g (τ ℚ.- ι n)

sampleAt : ∀ {A} → Tr.Lerp A → Tr.Track A → Timed A
sampleAt L = Tr.foldT (λ p → Tr.ticks p , pieceAt L p) seqAt

------------------------------------------------------------------------
-- Whole ticks: the continuous sample is the discrete one

private
  lt-suc : ∀ a b → not (a ℕ.<ᵇ b) ≡ (b ℕ.<ᵇ suc a)
  lt-suc zero    zero    = refl
  lt-suc zero    (suc b) = refl
  lt-suc (suc a) zero    = refl
  lt-suc (suc a) (suc b) = lt-suc a b

  nat-not : ∀ m n → not (n ℕ.≤ᵇ m) ≡ (m ℕ.<ᵇ n)
  nat-not m zero    = refl
  nat-not m (suc n) = lt-suc n m

ι-<ᵗ : ∀ k n → (ι k <ᵗ ι n) ≡ (k ℕ.<ᵇ n)
ι-<ᵗ k n = trans (cong not (ι-≤ᵇ n k)) (nat-not k n)

ratioAt-ι : ∀ k d → ratioAt (ι k) d ≡ Tr.ratio k d
ratioAt-ι k zero    = refl
ratioAt-ι k (suc d) =
  trans (cong (λ c → if c then ι k ℚ.* (+ 1 / suc d) else 1ℚ) (ι-<ᵗ k (suc d))) (go (k ℕ.<ᵇ suc d))
  where go : ∀ b → (if b then ι k ℚ.* (+ 1 / suc d) else 1ℚ) ≡ (if b then + k / suc d else 1ℚ)
        go true  = ι-ratio k d
        go false = refl

pieceAt-ι : ∀ {A} (L : Tr.Lerp A) (p : Tr.Piece A) k →
            pieceAt L p (ι k) ≡ proj₂ (Tr.samplePiece L p) k
pieceAt-ι L (Tr.piece d a b e) k = cong (λ r → Tr.Lerp.lerp L (Tr.progress e r) a b) (ratioAt-ι k d)

sampleAt-dur : ∀ {A} (L : Tr.Lerp A) (tr : Tr.Track A) → proj₁ (sampleAt L tr) ≡ proj₁ (Tr.sample L tr)
sampleAt-dur L (pure p)         = refl
sampleAt-dur L (impure (_ , c)) = cong₂ ℕ._+_ (sampleAt-dur L (c zero)) (sampleAt-dur L (c (suc zero)))

-- A track sampled at whole ticks of real time is the track sampled by ticks.
sampleAt-ι : ∀ {A} (L : Tr.Lerp A) (tr : Tr.Track A) k →
             proj₂ (sampleAt L tr) (ι k) ≡ proj₂ (Tr.sample L tr) k
sampleAt-ι L (pure p) k = pieceAt-ι L p k
sampleAt-ι L (impure (_ , c)) k
  rewrite sampleAt-dur L (c zero) | ι-<ᵗ k (proj₁ (Tr.sample L (c zero)))
  with k ℕ.<ᵇ proj₁ (Tr.sample L (c zero)) in eq
... | true  = sampleAt-ι L (c zero) k
... | false = trans (cong (proj₂ (sampleAt L (c (suc zero))))
                          (sym (ι-∸ k m (ℕP.≮⇒≥ (λ h → subst T eq (ℕP.<⇒<ᵇ h))))))
                    (sampleAt-ι L (c (suc zero)) (k ℕ.∸ m))
  where m = proj₁ (Tr.sample L (c zero))

-- the first facts about the track at real time: a piece holds `to` once it is over, at a
-- boundary the *later* piece takes over (right-continuity), and sequencing offsets time
piece-hold : ∀ {A} (L : Tr.Lerp A) d a b e τ → (τ <ᵗ ι d) ≡ false →
             pieceAt L (Tr.piece d a b e) τ ≡ b
piece-hold L zero    a b e τ _ = trans (cong (λ p → Tr.Lerp.lerp L p a b) (Tr.progress-1 e)) (Tr.Lerp.lerp-1 L a b)
piece-hold L (suc d) a b e τ h
  rewrite h = trans (cong (λ p → Tr.Lerp.lerp L p a b) (Tr.progress-1 e)) (Tr.Lerp.lerp-1 L a b)

seqAt-before : ∀ {A} (n m : ℕ) (f g : ℚ → A) τ → (τ <ᵗ ι n) ≡ true →
               proj₂ (seqAt (n , f) (m , g)) τ ≡ f τ
seqAt-before n m f g τ h rewrite h = refl

seqAt-after : ∀ {A} (n m : ℕ) (f g : ℚ → A) τ → (τ <ᵗ ι n) ≡ false →
              proj₂ (seqAt (n , f) (m , g)) τ ≡ g (τ ℚ.- ι n)
seqAt-after n m f g τ h rewrite h = refl

-- at the boundary the second takes over, from its own time 0
seqAt-boundary : ∀ {A} (n m : ℕ) (f g : ℚ → A) →
                 proj₂ (seqAt (n , f) (m , g)) (ι n) ≡ g 0ℚ
seqAt-boundary n m f g = trans (seqAt-after n m f g (ι n) (trans (ι-<ᵗ n n) (lt-irrefl n)))
                               (cong g (ℚP.+-inverseʳ (ι n)))
  where lt-irrefl : ∀ n → (n ℕ.<ᵇ n) ≡ false
        lt-irrefl zero    = refl
        lt-irrefl (suc n) = lt-irrefl n

------------------------------------------------------------------------
-- Template segments in real time

-- A template at the value `q` of its parameter: the sizes are evaluated *in ℚ*, with
-- `t := q` itself (the discrete reading `bodyAt` puts `fromℕ (units q)`, floored).
instQ : Dia (Expr ⊤) → ℚ → Dia ℚ
instQ d q = mapDia (evalWith ratOps (λ _ → q)) d

-- a segment is running on `0 ≤ τ < ticks`; there its template is at the track's value
leafAt : Tr.Track ℚ → Dia (Expr ⊤) → Timed (Maybe (Dia ℚ))
leafAt tr d =
  proj₁ (sampleAt Tr.ℚLerp tr) ,
  λ τ → if (0ℚ ℚ.≤ᵇ τ) ∧ (τ <ᵗ ι (proj₁ (sampleAt Tr.ℚLerp tr)))
        then just (instQ d (proj₂ (sampleAt Tr.ℚLerp tr) τ)) else nothing

-- what is shown when at most one of two parts is running, or both: they go over each other
mergeM : ∀ {F : Set} → (F → F → F) → Maybe F → Maybe F → Maybe F
mergeM _⊙_ nothing  y        = y
mergeM _⊙_ x        nothing  = x
mergeM _⊙_ (just x) (just y) = just (x ⊙ y)

-- running in parallel: the same time on both sides; a side that is not running adds nothing
-- (`Slides.Anim.Timeline.merge`)
parAt : ∀ {F : Set} → (F → F → F) → Timed (Maybe F) → Timed (Maybe F) → Timed (Maybe F)
parAt _⊙_ (n , f) (m , g) = n ℕ.⊔ m , λ τ → mergeM _⊙_ (f τ) (g τ)

-- the structure-preserving laws of time: `Par` runs both sides at the same `τ` and takes the
-- longer duration; `Seq` runs the first side up to its duration (`seqAt-before`), then the
-- second from its own time 0 (`seqAt-after`, `seqAt-boundary`)
parAt-time : ∀ {F} (_⊙_ : F → F → F) (A B : Timed (Maybe F)) τ →
             proj₂ (parAt _⊙_ A B) τ ≡ mergeM _⊙_ (proj₂ A τ) (proj₂ B τ)
parAt-time _⊙_ A B τ = refl

parAt-dur : ∀ {F} (_⊙_ : F → F → F) (A B : Timed (Maybe F)) →
            proj₁ (parAt _⊙_ A B) ≡ proj₁ A ℕ.⊔ proj₁ B
parAt-dur _⊙_ A B = refl

-- the timed frames of an animation all of whose segments are templates
bodyAt′ : Tr.Track ℚ → SegBody ℕ → Maybe (Timed (Maybe (Dia ℚ)))
bodyAt′ tr (template d) = just (leafAt tr d)
bodyAt′ tr (blackBox _) = nothing

segAt : Seg ℕ → Maybe (Timed (Maybe (Dia ℚ)))
segAt s = bodyAt′ (track s) (content s)

private
  lift2 : ∀ {A : Set} → (A → A → A) → Maybe A → Maybe A → Maybe A
  lift2 f (just x) (just y) = just (f x y)
  lift2 f _        _        = nothing

animAt : Anim ℕ (Seg ℕ) → Maybe (Timed (Maybe (Dia ℚ)))
animAt a = foldA segAt (lift2 seqAt) (lift2 (parAt atop)) a

-- The frame at real time `τ`: the layout, in ℚ, of the template segments running at `τ`.
-- `nothing` when some segment is not a template, or none is running at `τ`.
frameAt : Anim ℕ (Seg ℕ) → ℚ → Maybe (Layout ℚ)
frameAt a τ with animAt a
... | nothing        = nothing
... | just (_ , f)   = Maybe.map (LayoutWith.layout ratOps) (f τ)

-- the duration of the timed frames is the duration of the animation
segAt-dur : ∀ s T → segAt s ≡ just T → proj₁ T ≡ Tr.dur (track s)
segAt-dur s T eq = go (track s) (content s) T eq
  where
    go : ∀ tr b T → bodyAt′ tr b ≡ just T → proj₁ T ≡ Tr.dur tr
    go tr (template d) _ refl = trans (sampleAt-dur Tr.ℚLerp tr) (Tr.sample-dur Tr.ℚLerp tr)
    go tr (blackBox _) _ ()

private
  lift2-just : ∀ {A : Set} (f : A → A → A) x y {T} → lift2 f x y ≡ just T →
               ∃₂ λ a b → x ≡ just a × y ≡ just b × f a b ≡ T
  lift2-just f (just a) (just b) refl = a , b , refl , refl , refl
  lift2-just f (just a) nothing  ()
  lift2-just f nothing  y        ()

animAt-dur : ∀ a T → animAt a ≡ just T → proj₁ T ≡ dur a
animAt-dur (pure s) T eq = segAt-dur s T eq
animAt-dur (impure (Seq , k)) T eq with lift2-just seqAt (animAt (k zero)) (animAt (k (suc zero))) eq
... | A , B , e₁ , e₂ , refl = cong₂ ℕ._+_ (animAt-dur (k zero) A e₁) (animAt-dur (k (suc zero)) B e₂)
animAt-dur (impure (Par , k)) T eq with lift2-just (parAt atop) (animAt (k zero)) (animAt (k (suc zero))) eq
... | A , B , e₁ , e₂ , refl = cong₂ ℕ._⊔_ (animAt-dur (k zero) A e₁) (animAt-dur (k (suc zero)) B e₂)

------------------------------------------------------------------------
-- A template segment at whole ticks

zero≤ι : ∀ k → (0ℚ ℚ.≤ᵇ ι k) ≡ true
zero≤ι k = ι-≤ᵇ 0 k

-- At a whole tick the continuous frame of a segment is its template at the track's tick
-- sample, exactly (no flooring).
leafAt-ι : ∀ tr d k → (k ℕ.<ᵇ Tr.dur tr) ≡ true →
           proj₂ (leafAt tr d) (ι k) ≡ just (instQ d (proj₂ (Tr.sample Tr.ℚLerp tr) k))
leafAt-ι tr d k hk
  rewrite sampleAt-dur Tr.ℚLerp tr | Tr.sample-dur Tr.ℚLerp tr
        | ι-<ᵗ k (Tr.dur tr) | hk | zero≤ι k
  = cong (λ q → just (instQ d q)) (sampleAt-ι Tr.ℚLerp tr k)

-- ... and that is the discrete frame sent through `ι` whenever the discrete reading was
-- exact: the sample is a whole number `m`, and the template's layout is exact at `m`
-- (`Slides.Diagram.ExprQ`: no monus that truncates, no percentage that rounds).
leaf-tick : ∀ tr d k → (k ℕ.<ᵇ Tr.dur tr) ≡ true →
            let q = proj₂ (Tr.sample Tr.ℚLerp tr) k in
            q ≡ ι (units q) →
            AllLayout (Faithful (λ _ → units q)) (LayoutWith.layout exprOps d) →
            Maybe.map (LayoutWith.layout ratOps) (proj₂ (leafAt tr d) (ι k))
            ≡ just (mapLayout ι (LayoutWith.layout natOps (bodyAt natOps (template d) q)))
leaf-tick tr d k hk whole ok rewrite leafAt-ι tr d k hk =
  cong just (trans (cong (λ r → LayoutWith.layout ratOps (instQ d r)) whole)
                   (sym (faithful-layout (λ _ → units q) d ok)))
  where q = proj₂ (Tr.sample Tr.ℚLerp tr) k

-- a piece of positive length starts at `from` (time 0 is the start)
piece-start : ∀ {A} (L : Tr.Lerp A) d a b e → pieceAt L (Tr.piece (suc d) a b e) 0ℚ ≡ a
piece-start L d a b e
  rewrite ι-≤ᵇ (suc d) 0 | ℚP.*-zeroˡ (+ 1 / suc d) | Tr.progress-0 e = Tr.Lerp.lerp-0 L a b
