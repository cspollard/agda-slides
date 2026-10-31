{-# OPTIONS --safe --without-K #-}

-- A deck as a program: a pause is a wait for `next`.
--
--   scene:    chunk i+1 delayed by `gap` ticks under `Par`    (`Slides.Deck.Syntax`, `Slides.Deck.Steps`)
--   program:  `elab` turns each `Delay d` into `d` waits for `next`; a Kleisli lowering
--             of the scene signature into the program signature
--
-- The behaviour of `elab` (`Slides.Program.Sem`) on `t` nexts shows at time 0 what the scene
-- shows at tick `t`:
--   `pause-agree`    that output is the accumulated chunks 0..k (every t; the behaviour saturates)
--   `pause-visible`  it is `visible` (`Slides.Deck.Read`)
--   `awaits-in`, `awaits-out`  `w` waits for `next` delay the rest by `w` of the `next`s given
--   `skip-elab`      taking every wait as satisfied gives the scene with its delays removed

module Slides.Deck.Program where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; length; replicate)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; s≤s)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

open import Level using (lift)
open import Container.Lowering using (Lowering; lower; _⋙_)
open import Container.Lowering.Properties using (_≈⋆_; _≈ˡ_; refl≈; sym≈; trans≈; lower-⋙; lower-cong)
open import Slides.Scalar.Model.Nat using (natMon; natSub)
open import Slides.Scene.Syntax
open import Slides.Program.Syntax
open import Slides.Program.Navigation using (Nav; next; _≟N_)
open import Slides.Deck.Content
open import Slides.Deck.Syntax
open import Slides.Deck.Read using (ℓ; accumL; go-visible; visible)
open import Slides.Deck.Steps using (gap)
open import Data.Bool.Base using (if_then_else_)
open import Data.Nat.Base using (_∸_)
import Data.Nat.Properties as ℕP
import Data.Nat.Base as ℕ
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Nullary.Decidable using (dec-true; dec-false)
open import Data.Bool.Base using (true; false; T)
open import Data.Unit using (tt)

open import Slides.Deck.Clock using (module S)
open import Slides.Diagram.Overlay using (listOverlay)

-- a waiting machine shows nothing
absent : S.Timed
absent = 0 , λ _ _ → nothing

import Slides.Scene.Equiv {ℕ} {⊥} {Flow} natMon natSub (λ ()) listOverlay as E

-- outputs are compared up to the scene setoid: equal durations, pointwise equal readings
import Slides.Program.Sem {ℕ} {⊥} {Nav} _≟N_ E.TimedS S.dirH E.dirCong≈ absent as P

-- Pause as a wait

Prog : Set → Set
Prog = Program ℕ ⊥ Nav

awaits : ℕ → Prog ⊤
awaits zero          = pure tt
awaits (suc n)   = await next >>= λ _ → awaits n

elabOp : Lowering (SceneC ℕ ⊥) (ProgC ℕ ⊥ Nav)
elabOp (Delay d) = awaits d
elabOp o         = impure (inj₁ o , pure)

elab : ∀ {A} → Scene ℕ ⊥ A → Prog A
elab = lower elabOp

-- The behaviour of a slide's program

leafB : Flow → P.Beh
leafB a = P.constB (S.leafT ℓ a)

slideP : Flow → List Flow → P.Beh
slideP c cs = P.sem leafB (elab (chunkFrom c cs))

-- what the output reads at time 0
now : S.Timed → Maybe Flow
now t = proj₂ t 0 nothing

-- `w` waits for `next` before the rest: with `t` nexts given, the rest starts once `w ≤ t`, on the
-- `t - w` left; before that nothing is shown
awaits-in : ∀ w (K : Prog Flow) t → w ≤ t →
            P.sem leafB (awaits w >>= λ _ → K) (replicate t next) ≡ P.sem leafB K (replicate (t ∸ w) next)
awaits-in zero    K t       le       = refl
awaits-in (suc w) K (suc t) (s≤s le) =
  trans (P.await-hit (P.sem leafB (awaits w >>= λ _ → K)) next (replicate t next)) (awaits-in w K t le)

awaits-out : ∀ w (K : Prog Flow) t → t < w →
             P.sem leafB (awaits w >>= λ _ → K) (replicate t next) ≡ absent
awaits-out (suc w) K zero    lt       = refl
awaits-out (suc w) K (suc t) (s≤s lt) =
  trans (P.await-hit (P.sem leafB (awaits w >>= λ _ → K)) next (replicate t next)) (awaits-out w K t lt)

-- after `t` nexts the program shows the chunks revealed by tick `t`
pause-agree : ∀ c cs t → now (slideP c cs (replicate t next)) ≡ just (accumL c cs t)
pause-agree c []        t = refl
pause-agree c (d ∷ ds)  t = go (gap c d ℕP.≤? t)
  where
    K = elab (chunkFrom d ds)
    go : (q : Dec (gap c d ≤ t)) →
         now (slideP c (d ∷ ds) (replicate t next)) ≡ just (if does q then c ++ accumL d ds (t ∸ gap c d) else c)
    go (yes p) = trans (cong (λ z → S.merge (just c) (now z)) (awaits-in (gap c d) K t p))
                       (cong (S.merge (just c)) (pause-agree d ds (t ∸ gap c d)))
    go (no ¬p) = cong (λ z → S.merge (just c) (now z)) (awaits-out (gap c d) K t (ℕP.≰⇒> ¬p))

-- inside the slide this is what the scene shows at that tick
pause-visible : ∀ c cs t → now (slideP c cs (replicate t next)) ≡ visible (chunkFrom c cs) t
pause-visible c cs t = trans (pause-agree c cs t) (sym (go-visible c cs t))

-- A program as a scene: forget the waits

-- the scene with its delays removed: everything shown at once
undelayOp : Lowering (SceneC ℕ ⊥) (SceneC ℕ ⊥)
undelayOp (Delay d) = pure tt
undelayOp o         = impure (o , pure)

private
  skip-awaits : ∀ n → skip (awaits n) ≈⋆ pure tt
  skip-awaits zero    = lift refl
  skip-awaits (suc n) = skip-awaits n

skip-elab : ∀ {A} (s : Scene ℕ ⊥ A) → skip (elab s) ≈⋆ lower undelayOp s
skip-elab s = trans≈ (sym≈ (lower-⋙ elabOp skipOp s)) (lower-cong pw (refl≈ s))
  where
    pw : (elabOp ⋙ skipOp) ≈ˡ undelayOp
    pw (Delay d) = skip-awaits d
    pw Seq        = refl , λ q → lift refl
    pw Par        = refl , λ q → lift refl
    pw (Hold _)   = refl , λ q → lift refl
    pw (Repeat _) = refl , λ q → lift refl
    pw (Drive ())
