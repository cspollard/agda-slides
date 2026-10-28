{-# OPTIONS --safe --without-K #-}

-- The meaning of an animation, parametric in the time clock (`Slides.Time`, `docs/Time.md` §7).
--
-- The carrier is a timed value `TM X = ℕ × (T → Maybe X)`: a duration in ticks and what is shown at
-- each time (`nothing`: absent).  `TimeC` is read as an algebra on it, in any clock `K`:
--
--     Seq      `seqW`     first then second, shown only on the window [0, |x| + |y|)
--     Par      `parAt`    the same time on both sides, overlaid; absence is the unit
--     Hold n   `holdT`    the window [0, n)
--     Delay n  `delayT`   nothing for `n` ticks, then the operand from its own time 0
--     Repeat n `loopT`    `n` copies end to end
--     Drive tr `driveT`   the parameter below is bound to the track's value at the local time
--
-- Leaves are eternal (`λ _ → just`), so the window is what makes a segment finite.  `seqW` is the
-- guarded `Seq`: a bare eternal left operand would otherwise show before time 0 and the right one
-- past its end (`docs/Stage2.md`, decision (b)).
--
-- What differs between clocks is only how a track is read at a time (`val`: the `Scale`/`Ease`
-- layers of `docs/Time.md` §4, which only ℚ has; the ℕ clock reads the track at its tick and takes
-- the whole units).  A frame is the diagram reader `T → Dia T` (a template evaluated at the bound
-- parameter in the clock's own scalar `OOps T`); `Drive` is its `bind`.

module Slides.Anim.Sample where

open import Data.Bool using (Bool; not; _∧_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ)
open import Data.Unit using (tt)
open import Data.Fin using (zero; suc)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Slides.Diagram.Syntax using (Dia; atop; mapDia)
open import Slides.Diagram.Ordered using (evalO; OOps)
open import Slides.Time
import Slides.Anim.Track as Tr
open import Slides.Anim.Syntax

module _ (K : Clock) where
  open Clock K
  open Sem K

  TM : Set → Set
  TM X = Timed (Maybe X)

  mapT : ∀ {X Y : Set} → (X → Y) → TM X → TM Y
  mapT f (n , g) = n , λ τ → Maybe.map f (g τ)

  -- the window [0, n)
  win : ℕ → T → Bool
  win n τ = not (τ <ᵇ 0#) ∧ (τ <ᵇ ι n)

  holdT : ∀ {X} → ℕ → TM X → TM X
  holdT n (_ , f) = n , λ τ → if win n τ then f τ else nothing

  -- sequencing, guarded to the window [0, |x| + |y|)
  seqW : ∀ {X} → TM X → TM X → TM X
  seqW x y = holdT (proj₁ x ℕ.+ proj₁ y) (seqAt x y)

  delayT : ∀ {X} → ℕ → TM X → TM X
  delayT n (m , f) = n ℕ.+ m , λ τ → if τ <ᵇ ι n then nothing else f (τ - ι n)

  loopT : ∀ {X} → ℕ → TM X → TM X
  loopT ℕ.zero    x = 0 , λ _ → nothing
  loopT (ℕ.suc n) x = seqW x (loopT n x)

  -- bind the parameter to the signal `w` of local time (`bnd` is the carrier's substitution)
  driveT : ∀ {X} → (T → X → X) → (T → T) → TM X → TM X
  driveT bnd w (n , f) = n , λ τ → Maybe.map (bnd (w τ)) (f τ)

  -- `⊙` overlays frames, `bnd q x` is `x` with the parameter bound to `q`, `val` reads a track
  timeAlg : ∀ {X} → (X → X → X) → (T → X → X) → (Tr.Track ℚ → T → T) → (s : TOp) → (tarity s → TM X) → TM X
  timeAlg ⊙ bnd val Seq        k = seqW (k zero) (k (suc zero))
  timeAlg ⊙ bnd val Par        k = parAt ⊙ (k zero) (k (suc zero))
  timeAlg ⊙ bnd val (Hold n)   k = holdT n (k tt)
  timeAlg ⊙ bnd val (Delay n)  k = delayT n (k tt)
  timeAlg ⊙ bnd val (Repeat n) k = loopT n (k tt)
  timeAlg ⊙ bnd val (Drive tr) k = driveT bnd (val tr) (k tt)

  -- a leaf is eternal
  sample : ∀ {A X} → (X → X → X) → (T → X → X) → (Tr.Track ℚ → T → T) → (A → X) → Scene A → TM X
  sample ⊙ bnd val ℓ = foldS (λ a → 0 , λ _ → just (ℓ a)) (timeAlg ⊙ bnd val)

  ----------------------------------------------------------------------
  -- Templates: the frames of an animation

  Rd : Set
  Rd = T → Dia T

  -- a template at the value `p` of its parameter, in the clock's own scalar
  inst : T → Tmpl → Dia T
  inst p d = mapDia (evalO O (λ _ → p)) d

  -- the animation read as readers: leaves are templates at the bound parameter, `Par` overlays
  -- pointwise, `Drive` binds
  atopR : Rd → Rd → Rd
  atopR g h p = atop (g p) (h p)

  bndR : T → Rd → Rd
  bndR q g _ = g q

  readA : (Tr.Track ℚ → T → T) → Anim → TM Rd
  readA val = sample atopR bndR val inst-d
    where inst-d : Tmpl → Rd
          inst-d d p = inst p d

  -- the frames at time τ: the readers at the zero parameter (every segment binds its own)
  frames : (Tr.Track ℚ → T → T) → Anim → TM (Dia T)
  frames val a = mapT (λ g → g 0#) (readA val a)
