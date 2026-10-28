{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE: proofs and the vocabulary they need; no executable imports it (`tests/check_closure.py`).
--
-- The assembly of whole frames, continuous reading, at whole ticks: `leaf-tick` lifted from one
-- segment to the whole animation (`Slides.Anim.Continuous`).
--
-- Statement.  Let `a` be an animation built from segments (`AllExact a`: every segment is exact
-- at each of its ticks: the sample of its track is a whole number `q ≡ ι (units q)` and the layout
-- of its template is `Faithful` at `units q`, the hypotheses of `leaf-tick`).  At every whole tick
-- `k`, the frames of the two clocks are related, and in particular if the discrete frame is there
--
--     frameAt a (ι k)  ≡  just (mapLayout ι (layout_ℕ F))            (`frameAt-assembly`)
--
-- the continuous frame at the whole tick is the discrete frame sent through `ι`.
--
-- The proof is the assembly calculus (`Slides.Anim.Assembly.Calculus`, the clocks ℚ and ℕ related
-- by `ι`): a relation over the temporal skeleton closed under `Seq`, `Par`, `Delay`, `Hold` with only
-- the clock laws, so the induction below has one case per connective and the `Faithful` hypotheses
-- are used in one place, the segment.  (The old hypothesis local to the tick, `Good a k`, is not
-- re-derived: it asked the hypotheses of the segments running at `k` only, and no other module
-- used it; here the relation is over all ticks at once.)
--
-- What `atop` needs of `ι`.  `ι` is not an `Ops`-homomorphism (on `∸` it preserves the difference
-- only when the minuend is the larger; on `percentOf` only when exact), so layout is not natural
-- along it in general; that is why the hypotheses `Faithful` are needed for a segment's layout.
-- But `atop` computes only sums, maxima and the differences `(a ⊔ b) - a`, `(a ⊔ b) - b`, whose
-- minuend is the larger by construction.  So `atop` commutes with `mapLayout ι` on every pair of
-- layouts, *with no hypothesis* (`atop-ι`, by `Slides.Diagram.Place.Properties.Atop`).
--
-- Not covered: the frames between whole ticks (`k < τ < k+1`), where `frameAt` is evaluated at
-- the fractional parameters; that is checked in the browser.

module Slides.Anim.Assembly.Continuous where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ; _<ᵇ_)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Rational as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Slides.Diagram.Draw using (Layout; mapLayout)
open import Slides.Diagram.Syntax using (Dia; atop)
open import Slides.Diagram.Ordered using (termOps)
open import Slides.Diagram.Ordered.Properties.Faithful using (AllLayout; FaithfulO)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (natOps; ratOps)
open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.NatQ.Properties using (ι-+; ι-⊔; ι-∸)
import Slides.Diagram.Place natOps as PN
import Slides.Diagram.Place ratOps as PQ
import Slides.Diagram.Place.Properties.Atop as AN
import Slides.Anim.Track as Tr
open import Slides.Time using (mergeM)
open import Slides.Time.Rat using (ratClock)
open import Slides.Time.Nat using (natClock)
open import Slides.Time.Properties using (ratLaws; natLaws; mergeM-map)
open import Slides.Anim.Syntax
open import Slides.Anim.Sample
open import Slides.Anim.Sample.Properties using (win-ι)
open import Slides.Anim.Timeline using (framesN; natVal)
open import Slides.Anim.Continuous
open import Slides.Anim.Continuous.Properties
open import Slides.Anim.Assembly
open Calculus ratClock natClock ratLaws natLaws

private
  layoutN : Dia ℕ → Layout ℕ
  layoutN = LayoutWith.layout natOps

  layoutQ : Dia ℚ → Layout ℚ
  layoutQ = LayoutWith.layout ratOps

------------------------------------------------------------------------
-- `atop` commutes with `ι`, for any layouts

atop-ι : ∀ a b → mapLayout ι (PN.atop a b) ≡ PQ.atop (mapLayout ι a) (mapLayout ι b)
atop-ι = AN.atop-natural′ natOps ratOps ι ι-+ ι-⊔
           (λ a b → ι-∸ (a ℕ.⊔ b) a (ℕP.m≤m⊔n a b))
           (λ a b → ι-∸ (a ℕ.⊔ b) b (ℕP.m≤n⊔m a b))

------------------------------------------------------------------------
-- One frame against one frame

-- the continuous frame at a whole tick is the discrete frame sent through `ι`; a frame is there
-- on one side exactly when it is on the other
data RelC : Maybe (Dia ℚ) → Maybe (Dia ℕ) → Set where
  noFrame    : RelC nothing nothing
  bothFrames : ∀ {D F} → layoutQ D ≡ mapLayout ι (layoutN F) → RelC (just D) (just F)

RelC-mergeM : ∀ {a b a′ b′} → RelC a a′ → RelC b b′ → RelC (mergeM atop a b) (mergeM atop a′ b′)
RelC-mergeM noFrame        rb               = rb
RelC-mergeM (bothFrames r) noFrame          = bothFrames r
RelC-mergeM (bothFrames {F = x′} r) (bothFrames {F = y′} s) =
  bothFrames (trans (cong₂ PQ.atop r s) (sym (atop-ι (layoutN x′) (layoutN y′))))

RelC-just : ∀ {m F} → RelC m (just F) → ∃ λ D → m ≡ just D × layoutQ D ≡ mapLayout ι (layoutN F)
RelC-just (bothFrames {D} s) = D , refl , s

-- the readers (a segment binds its own parameter, so the zero one is irrelevant) are related when
-- their frames are
RelRd : Maybe (Rd ratClock) → Maybe (Rd natClock) → Set
RelRd a b = RelC (Maybe.map (λ g → g ℚ.0ℚ) a) (Maybe.map (λ g → g 0) b)

private
  RelRd-mergeM : ∀ {a b a′ b′} → RelRd a b → RelRd a′ b′ →
                 RelRd (mergeM (atopR ratClock) a a′) (mergeM (atopR natClock) b b′)
  RelRd-mergeM {a} {b} {a′} {b′} ra rb
    rewrite mergeM-map (λ g → g ℚ.0ℚ) (atopR ratClock) atop (λ _ _ → refl) a a′
          | mergeM-map (λ g → g 0) (atopR natClock) atop (λ _ _ → refl) b b′ = RelC-mergeM ra rb

------------------------------------------------------------------------
-- The hypotheses: exactness of the segments

-- a template segment is exact at its tick `m`: the hypotheses of `leaf-tick`
Exact : Tr.Track ℚ → Tmpl → ℕ → Set
Exact tr d m =
  let q = proj₂ (Tr.sample Tr.ℚLerp tr) m in
  q ≡ ι (units q) × AllLayout (FaithfulO (λ _ → units q)) (LayoutWith.layout termOps d)

-- an animation built from segments, each exact at every tick of its window (a `Hold` over
-- segments only narrows what is shown, so the hypothesis is the same)
data AllExact : Anim → Set where
  ex-seg   : ∀ n tr d → (∀ m → (m <ᵇ n) ≡ true → Exact tr d m) → AllExact (hold′ n (drive tr (pure d)))
  ex-hold  : ∀ {n a} → AllExact a → AllExact (hold′ n a)
  ex-seq   : ∀ {a b} → AllExact a → AllExact b → AllExact (a ⨾ b)
  ex-par   : ∀ {a b} → AllExact a → AllExact b → AllExact (a ∥ᵃ b)
  ex-delay : ∀ {n a} → AllExact a → AllExact (delay n a)

------------------------------------------------------------------------
-- The theorem, tick by tick

R₀ : ℕ → Maybe (Rd ratClock) → Maybe (Rd natClock) → Set
R₀ _ = RelRd

assembly : ∀ {a} → AllExact a → RelN R₀ (readA ratClock ratVal a) (readA natClock natVal a)
assembly {a = .(hold′ n (drive tr (pure d)))} (ex-seg n tr d ex) = refl , tick
  where
    leaf-rel : ∀ k → (k <ᵇ n) ≡ true →
               RelC (just (inst ratClock (ratVal tr (ι k)) d)) (just (inst natClock (natVal tr k) d))
    leaf-rel k hk rewrite sampleAt-ι Tr.ℚLerp tr k =
      bothFrames (inst-exact d (proj₂ (Tr.sample Tr.ℚLerp tr) k) (proj₁ (ex k hk)) (proj₂ (ex k hk)))

    tick : ∀ k → RelRd (if win ratClock n (ι k) then just (bndR ratClock (ratVal tr (ι k)) (λ p → inst ratClock p d)) else nothing)
                       (if win natClock n k then just (bndR natClock (natVal tr k) (λ p → inst natClock p d)) else nothing)
    tick k rewrite win-ι ratClock ratLaws n k with k <ᵇ n in eq
    ... | false = noFrame
    ... | true  = leaf-rel k eq
assembly (ex-hold {n} {a} h) =
  relN-hold {R = R₀} {x = readA ratClock ratVal a} {y = readA natClock natVal a} (λ _ → noFrame) (assembly h) n
assembly (ex-seq {a} {b} h₁ h₂) =
  relN-seq {R = R₀} {x₁ = readA ratClock ratVal a} {x₂ = readA ratClock ratVal b}
           {y₁ = readA natClock natVal a} {y₂ = readA natClock natVal b} (λ _ → noFrame) (assembly h₁) (assembly h₂)
assembly (ex-par {a} {b} h₁ h₂) =
  relN-par {R = R₀} {R₁ = R₀} {R₂ = R₀} {x₁ = readA ratClock ratVal a} {x₂ = readA ratClock ratVal b}
           {y₁ = readA natClock natVal a} {y₂ = readA natClock natVal b} (λ _ a b a′ b′ → RelRd-mergeM {a} {b} {a′} {b′}) (assembly h₁) (assembly h₂)
assembly (ex-delay {n} {a} h) =
  relN-delay {R = R₀} {x = readA ratClock ratVal a} {y = readA natClock natVal a} {n = n} (λ _ → noFrame) (assembly h)

------------------------------------------------------------------------
-- Statement (B)

-- The continuous frame at the whole tick `k` is the discrete frame sent through `ι`, provided
-- the segments are exact, and wherever the discrete frame is there.
frameAt-assembly : ∀ {a} → AllExact a → ∀ k F → proj₂ (framesN a) k ≡ just F →
                   frameAt a (ι k) ≡ just (mapLayout ι (layoutN F))
frameAt-assembly {a} ex k F eF with RelC-just (subst (RelC (proj₂ (framesQ a) (ι k))) eF (proj₂ (assembly ex) k))
... | D , e , s = trans (cong (Maybe.map layoutQ) e) (cong just s)
