{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE (spike): no executable imports it.
--
-- The lifting lemma for the Stage 2 container (`Spike.Timed.Properties.lift-natural` plus the new
-- operations).  Sampling commutes with a map `Φ : A → B` that is a homomorphism of
-- `DiagramC S`-algebras into an extensional algebra and commutes with the carrier's
-- substitution `bnd` (the operation `Drive` uses).  Taking the term algebra on the left gives
-- the plan's statement; the instance at layout is one line (`Layout`), at names two (`Names`).
--
-- New cases: `seqW` (a `hold` of a `seq`), `Repeat` (induction on the count), `Drive`.

module Slides.Spike.Stage2.Lift where

open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Slides.Diagram.Syntax
open import Slides.Anim.Continuous using (seqAt)
open import Slides.Spike.Timed using (TM; holdT; mapT; fin2)
open import Slides.Spike.Timed.Properties using (Rel; mk; seq-nat; hold-nat; delay-nat; par-nat; fin2-map; module Lift)
open Rel public
open import Slides.Spike.Stage2.Scene

seqW-nat : ∀ {A B : Set} (Φ : A → B) {xB xA yB yA} → Rel Φ xB xA → Rel Φ yB yA → Rel Φ (seqW xB yB) (seqW xA yA)
seqW-nat Φ {nB , fB} {nA , fA} {mB , gB} {mA , gA} (mk refl p) (mk refl q) =
  hold-nat Φ (nB ℕ.+ mB) {seqAt (nB , fB) (mB , gB)} {seqAt (nB , fA) (mB , gA)}
    (seq-nat Φ {nB , fB} {nB , fA} {mB , gB} {mB , gA} (mk refl p) (mk refl q))

loop-nat : ∀ {A B : Set} (Φ : A → B) n {xB xA} → Rel Φ xB xA → Rel Φ (loopT n xB) (loopT n xA)
loop-nat Φ ℕ.zero    r = mk refl (λ _ → refl)
loop-nat Φ (ℕ.suc n) r = seqW-nat Φ r (loop-nat Φ n r)

drive-nat : ∀ {A B : Set} (Φ : A → B) (bndA : ℚ → A → A) (bndB : ℚ → B → B) →
            (∀ q a → Φ (bndA q a) ≡ bndB q (Φ a)) → ∀ w {xB xA} →
            Rel Φ xB xA → Rel Φ (driveT bndB w xB) (driveT bndA w xA)
drive-nat Φ bndA bndB BND w {_ , fB} {_ , fA} (mk d p) =
  mk d λ τ → trans (cong (Maybe.map (bndB (w τ))) (p τ)) (mm (w τ) (fA τ))
  where
    mm : ∀ q x → Maybe.map (bndB q) (Maybe.map Φ x) ≡ Maybe.map Φ (Maybe.map (bndA q) x)
    mm q nothing  = refl
    mm q (just x) = cong just (sym (BND q x))

module Lift′ {S A B : Set} (αA : Algebra S A) (αB : Algebra S B) (Φ : A → B)
             (HOM : ∀ o x → Φ (αA o x) ≡ αB o (λ i → Φ (x i)))
             (EXT : ∀ o {x y} → (∀ i → x i ≡ y i) → αB o x ≡ αB o y)
             (bndA : ℚ → A → A) (bndB : ℚ → B → B) (BND : ∀ q a → Φ (bndA q a) ≡ bndB q (Φ a)) where

  open Lift αA αB Φ HOM EXT using (gather-nat)

  lift-natural′ : ∀ t → Rel Φ (sample αB bndB t) (sample αA bndA t)
  lift-natural′ (pure ())
  lift-natural′ (impure (inj₁ Seq , k))        = seqW-nat Φ (lift-natural′ (k zero)) (lift-natural′ (k (suc zero)))
  lift-natural′ (impure (inj₁ Par , k))        =
    par-nat Φ (λ a b → trans (HOM Atop (fin2 a b)) (EXT Atop (fin2-map Φ a b)))
      (lift-natural′ (k zero)) (lift-natural′ (k (suc zero)))
  lift-natural′ (impure (inj₁ (Hold n) , k))   = hold-nat Φ n (lift-natural′ (k tt))
  lift-natural′ (impure (inj₁ (Delay n) , k))  = delay-nat Φ n (lift-natural′ (k tt))
  lift-natural′ (impure (inj₁ (Repeat n) , k)) = loop-nat Φ n (lift-natural′ (k tt))
  lift-natural′ (impure (inj₁ (Drive tr) , k)) = drive-nat Φ bndA bndB BND _ (lift-natural′ (k tt))
  lift-natural′ (impure (inj₂ o , k))          = gather-nat o (λ i → lift-natural′ (k i))

-- the plan's statement: sampling in `α` is `fold α` of the restriction (`sample con`), where
-- the term carrier has a substitution `bndD` that `fold α` carries to `bnd` (for closed scenes,
-- `bnd = bndD = λ _ x → x`)
module _ {S B : Set} (α : Algebra S B) (bnd : ℚ → B → B) (bndD : ℚ → Dia S → Dia S)
         (BND : ∀ q d → fold α (bndD q d) ≡ bnd q (fold α d))
         (EXT : ∀ o {x y} → (∀ i → x i ≡ y i) → α o x ≡ α o y) where

  private
    con : Algebra S (Dia S)
    con o k = impure (o , k)

  lifting-lemma′ : ∀ t → Rel (fold α) (sample α bnd t) (sample con bndD t)
  lifting-lemma′ = Lift′.lift-natural′ con α (fold α) (λ _ _ → refl) EXT bndD bnd BND
