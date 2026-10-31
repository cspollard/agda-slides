{-# OPTIONS --safe --without-K #-}

-- A deck as a program: a pause is a wait for `next`.
--
--   scene:    chunk i+1 delayed by one tick under `Par`    (`Slides.Deck.Syntax`)
--   program:  `elab` turns each `Delay d` into `d` waits for `next`; a Kleisli lowering
--             of the scene signature into the program signature
--
-- The behaviour of `elab` (`Slides.Program.Sem`) on `k` nexts shows at time 0 what the scene
-- shows at tick `k`:
--   `pause-agree`    that output is the accumulated chunks 0..k (every k; the behaviour saturates)
--   `pause-visible`  for k inside the slide it is `visible` (`Slides.Deck.Read`)
--   `skip-elab`      taking every wait as satisfied gives the scene with its delays removed

module Slides.Deck.Program where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; length; replicate)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

open import Level using (lift)
open import Container.Lowering using (Lowering; lower; _⋙_)
open import Container.Lowering.Properties using (_≈⋆_; _≈ˡ_; refl≈; sym≈; trans≈; lower-⋙; lower-cong)
open import Container.Pick using (pick2)
open import Slides.Scalar.Model.Nat using (natMon; natSub)
open import Slides.Scene.Syntax
open import Slides.Program.Syntax
open import Slides.Program.Navigation using (Nav; next; _≟N_)
open import Slides.Deck.Content
open import Slides.Deck.Syntax
open import Slides.Deck.Read using (ℓ; accumL; go-visible; visible)

open import Slides.Diagram.Overlay using (listOverlay)
import Slides.Scene.Sample {ℕ} {⊥} {Flow} natMon natSub (λ ()) listOverlay as S

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

kids : Flow → Flow → List Flow → Fin 2 → P.Beh
kids c d ds q = P.sem leafB (elab (pick2 (pure c) (delay 1 (chunkFrom d ds)) q))

-- a wait for `next` hands the rest of the commands to the slide behind it
pause-agree : ∀ c cs k → now (slideP c cs (replicate k next)) ≡ just (accumL c cs k)
pause-agree c []        k        = refl
pause-agree c (d ∷ ds)  zero     = refl
pause-agree c (d ∷ ds)  (suc k)  =
  trans (cong (λ z → S.merge (just c) (now z)) (P.await-hit (slideP d ds) next (replicate k next)))
        (cong (S.merge (just c)) (pause-agree d ds k))

-- inside the slide this is what the scene shows at that tick
pause-visible : ∀ c cs k → k < suc (length cs) →
                now (slideP c cs (replicate k next)) ≡ visible (chunkFrom c cs) k
pause-visible c cs k lt = trans (pause-agree c cs k) (sym (go-visible c cs k lt))

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
