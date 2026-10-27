{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE (spike): no executable imports it.
--
-- THE LIFTING LEMMA.  Sampling commutes with folding a scene:
--
--     Rel Φ (sample αB t) (sample αA t)           (`lift-natural`)
--
-- for any map Φ : A → B that is a homomorphism of `DiagramC S`-algebras (HOM) into an
-- algebra that is extensional (EXT; without funext this is what stands in for the setoid
-- `Func.cong` of `Container.Sum`).  Taking αA = the term algebra `con` and Φ = `fold αB`
-- (a homomorphism by definition) gives the statement of plan/Unify.md:
--
--     Rel (fold αB) (sample αB t) (sample con t)        i.e.
--     sample αB t at τ  ≡  Maybe.map (fold αB) (restrict t τ)           (`lifting-lemma`)
--
-- `Rel Φ xB xA` is: equal durations and pointwise equal samples (no funext).  The temporal
-- operations (Seq, Hold, Delay) commute with any Φ; Par needs Φ to commute with Atop.

module Slides.Spike.Timed.Properties where

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.Syntax
open import Slides.Anim.Continuous using (Timed; seqAt; parAt; _<ᵗ_)
open import Slides.Anim.Timeline using (mergeM)
open import Slides.Spike.Timed

------------------------------------------------------------------------
-- Helpers

if-cong : ∀ {X : Set} (c : Bool) {x x′ y y′ : X} → x ≡ x′ → y ≡ y′ →
          (if c then x else y) ≡ (if c then x′ else y′)
if-cong true  p q = p
if-cong false p q = q

map-if : ∀ {A B : Set} (Φ : A → B) (c : Bool) (x y : Maybe A) →
         Maybe.map Φ (if c then x else y) ≡ (if c then Maybe.map Φ x else Maybe.map Φ y)
map-if Φ true  x y = refl
map-if Φ false x y = refl

fin2-map : ∀ {A B : Set} (Φ : A → B) (a b : A) (i : Fin 2) → Φ (fin2 a b i) ≡ fin2 (Φ a) (Φ b) i
fin2-map Φ a b zero          = refl
fin2-map Φ a b (suc zero)    = refl
fin2-map Φ a b (suc (suc ()))

------------------------------------------------------------------------
-- The operations commute with a map Φ

-- `Rel Φ xB xA`: xB is xA with Φ applied (equal durations, pointwise equal samples)
record Rel {A B : Set} (Φ : A → B) (xB : TM B) (xA : TM A) : Set where
  constructor mk
  field
    dur≡ : proj₁ xB ≡ proj₁ xA
    at≡  : ∀ τ → proj₂ xB τ ≡ Maybe.map Φ (proj₂ xA τ)

module _ {A B : Set} (Φ : A → B) where

  seq-nat : ∀ {xB xA yB yA} → Rel Φ xB xA → Rel Φ yB yA → Rel Φ (seqAt xB yB) (seqAt xA yA)
  seq-nat {nB , fB} {nA , fA} {mB , gB} {mA , gA} (mk refl p) (mk refl q) =
    mk refl (λ τ → trans (if-cong (τ <ᵗ ι nB) (p τ) (q (τ ℚ.- ι nB)))
                         (sym (map-if Φ (τ <ᵗ ι nB) (fA τ) (gA (τ ℚ.- ι nB)))))

  hold-nat : ∀ n {xB xA} → Rel Φ xB xA → Rel Φ (holdT n xB) (holdT n xA)
  hold-nat n {_ , fB} {_ , fA} (mk _ p) =
    mk refl (λ τ → trans (if-cong ((0ℚ ℚ.≤ᵇ τ) ∧ (τ <ᵗ ι n)) (p τ) refl)
                         (sym (map-if Φ ((0ℚ ℚ.≤ᵇ τ) ∧ (τ <ᵗ ι n)) (fA τ) nothing)))

  delay-nat : ∀ n {xB xA} → Rel Φ xB xA → Rel Φ (delayT n xB) (delayT n xA)
  delay-nat n {mB , fB} {mA , fA} (mk refl p) =
    mk refl (λ τ → trans (if-cong (τ <ᵗ ι n) refl (p (τ ℚ.- ι n)))
                         (sym (map-if Φ (τ <ᵗ ι n) nothing (fA (τ ℚ.- ι n)))))

  -- Par: needs Φ to commute with the overlay
  par-nat : ∀ {⊙A ⊙B} → (∀ a b → Φ (⊙A a b) ≡ ⊙B (Φ a) (Φ b)) →
    ∀ {xB xA yB yA} → Rel Φ xB xA → Rel Φ yB yA → Rel Φ (parAt ⊙B xB yB) (parAt ⊙A xA yA)
  par-nat {⊙A} {⊙B} h {_ , fB} {_ , fA} {_ , gB} {_ , gA} (mk d p) (mk e q) =
    mk (cong₂ ℕ._⊔_ d e) λ τ →
      trans (cong₂ (mergeM ⊙B) (p τ) (q τ)) (merge-map (fA τ) (gA τ))
    where
      merge-map : ∀ x y → mergeM ⊙B (Maybe.map Φ x) (Maybe.map Φ y) ≡ Maybe.map Φ (mergeM ⊙A x y)
      merge-map nothing  y        = refl
      merge-map (just x) nothing  = refl
      merge-map (just x) (just y) = cong just (sym (h x y))

  zip-nat : ∀ {C D : Set} (Ψ : C → D) {uA : A → A → C} {uB : B → B → D} →
    (∀ a b → Ψ (uA a b) ≡ uB (Φ a) (Φ b)) →
    ∀ {xB xA yB yA} → Rel Φ xB xA → Rel Φ yB yA → Rel Ψ (zipT uB xB yB) (zipT uA xA yA)
  zip-nat Ψ {uA} {uB} h {_ , fB} {_ , fA} {_ , gB} {_ , gA} (mk d p) (mk e q) =
    mk (cong₂ ℕ._⊔_ d e) λ τ → trans (cong₂ (zipM uB) (p τ) (q τ)) (zip-map (fA τ) (gA τ))
    where
      zip-map : ∀ x y → zipM uB (Maybe.map Φ x) (Maybe.map Φ y) ≡ Maybe.map Ψ (zipM uA x y)
      zip-map nothing  y        = refl
      zip-map (just x) nothing  = refl
      zip-map (just x) (just y) = cong just (sym (h x y))

  map-nat : ∀ {C D : Set} (Ψ : C → D) (uA : A → C) (uB : B → D) →
    (∀ a → Ψ (uA a) ≡ uB (Φ a)) →
    ∀ {xB xA} → Rel Φ xB xA → Rel Ψ (mapT uB xB) (mapT uA xA)
  map-nat Ψ uA uB h {_ , fB} {_ , fA} (mk d p) =
    mk d λ τ → trans (cong (Maybe.map uB) (p τ)) (mm (fA τ))
    where
      mm : ∀ x → Maybe.map uB (Maybe.map Φ x) ≡ Maybe.map Ψ (Maybe.map uA x)
      mm nothing  = refl
      mm (just x) = cong just (sym (h x))

------------------------------------------------------------------------
-- The lifting lemma

module Lift {S A B : Set} (αA : Algebra S A) (αB : Algebra S B) (Φ : A → B)
            (HOM : ∀ o x → Φ (αA o x) ≡ αB o (λ i → Φ (x i)))
            (EXT : ∀ o {x y} → (∀ i → x i ≡ y i) → αB o x ≡ αB o y) where

  gather-nat : ∀ o {kA kB} → (∀ i → Rel Φ (kB i) (kA i)) →
    Rel Φ (gather o kB (αB o)) (gather o kA (αA o))
  gather-nat (Rectangle w h s)  _ = mk refl (λ τ → cong just (sym (trans (HOM _ _) (EXT _ (λ ())))))
  gather-nat (Disc r s)         _ = mk refl (λ τ → cong just (sym (trans (HOM _ _) (EXT _ (λ ())))))
  gather-nat (Segment w h s)    _ = mk refl (λ τ → cong just (sym (trans (HOM _ _) (EXT _ (λ ())))))
  gather-nat (Text p z t s)     _ = mk refl (λ τ → cong just (sym (trans (HOM _ _) (EXT _ (λ ())))))
  gather-nat (Spacer w h)       _ = mk refl (λ τ → cong just (sym (trans (HOM _ _) (EXT _ (λ ())))))
  gather-nat (Beside al)  ih = zip-nat Φ Φ (λ a b → trans (HOM (Beside al) (fin2 a b)) (EXT (Beside al) (fin2-map Φ a b))) (ih zero) (ih (suc zero))
  gather-nat (Above al)   ih = zip-nat Φ Φ (λ a b → trans (HOM (Above al) (fin2 a b)) (EXT (Above al) (fin2-map Φ a b))) (ih zero) (ih (suc zero))
  gather-nat Atop         ih = zip-nat Φ Φ (λ a b → trans (HOM Atop (fin2 a b)) (EXT Atop (fin2-map Φ a b))) (ih zero) (ih (suc zero))
  gather-nat LabelAbove   ih = zip-nat Φ Φ (λ a b → trans (HOM LabelAbove (fin2 a b)) (EXT LabelAbove (fin2-map Φ a b))) (ih zero) (ih (suc zero))
  gather-nat LabelBelow   ih = zip-nat Φ Φ (λ a b → trans (HOM LabelBelow (fin2 a b)) (EXT LabelBelow (fin2-map Φ a b))) (ih zero) (ih (suc zero))
  gather-nat (Overlay w h) ih = zip-nat Φ Φ (λ a b → trans (HOM (Overlay w h) (fin2 a b)) (EXT (Overlay w h) (fin2-map Φ a b))) (ih zero) (ih (suc zero))
  gather-nat (Place w h x y) ih = map-nat Φ Φ _ _ (λ a → HOM (Place w h x y) (λ _ → a)) (ih tt)
  gather-nat (Named n)       ih = map-nat Φ Φ _ _ (λ a → HOM (Named n) (λ _ → a)) (ih tt)
  gather-nat (Connect a pa b pb s) ih = map-nat Φ Φ _ _ (λ x → HOM (Connect a pa b pb s) (λ _ → x)) (ih tt)

  lift-natural : ∀ t → Rel Φ (sample αB t) (sample αA t)
  lift-natural (pure ())
  lift-natural (impure (inj₁ Seq , k))       = seq-nat Φ (lift-natural (k zero)) (lift-natural (k (suc zero)))
  lift-natural (impure (inj₁ Par , k))       =
    par-nat Φ (λ a b → trans (HOM Atop (fin2 a b)) (EXT Atop (fin2-map Φ a b)))
      (lift-natural (k zero)) (lift-natural (k (suc zero)))
  lift-natural (impure (inj₁ (Hold n) , k))  = hold-nat Φ n (lift-natural (k tt))
  lift-natural (impure (inj₁ (Delay n) , k)) = delay-nat Φ n (lift-natural (k tt))
  lift-natural (impure (inj₂ o , k))         = gather-nat o (λ i → lift-natural (k i))

-- The plan's statement: sampling the lifted algebra is `fold α` of the restriction.
module _ {S B : Set} (α : Algebra S B)
         (EXT : ∀ o {x y} → (∀ i → x i ≡ y i) → α o x ≡ α o y) where

  lifting-lemma : ∀ t → Rel (fold α) (sample α t) (sample con t)
  lifting-lemma = Lift.lift-natural con α (fold α) (λ _ _ → refl) EXT

  lifting-lemma-at : ∀ t τ → proj₂ (sample α t) τ ≡ Maybe.map (fold α) (restrict t τ)
  lifting-lemma-at t τ = Rel.at≡ (lifting-lemma t) τ

  lifting-lemma-dur : ∀ t → proj₁ (sample α t) ≡ proj₁ (sample con t)
  lifting-lemma-dur t = Rel.dur≡ (lifting-lemma t)
