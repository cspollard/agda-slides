{-# OPTIONS --safe --without-K #-}

-- Clocks: reading a scene along an order embedding of time (`ι : ℕ → ℚ`).
--
-- `mapScene h g` maps durations by `h` and drivers by `g`.  If `h` is an order embedding
-- (`IsOrdMonHom`: preserves `⊔`, comparisons, exact differences), drivers are carried (`g-val`)
-- and overlay is (`IsOverlayHom`), then
--
--   tick-hom   reading the mapped scene at `h t` is reading the original at `t`:
--              durations map by `h`, frames by `F`, given that leaves do (`ℓ-ok`)
--
-- A logical relation over the signature, one lemma per operation.  Instantiated at `ι` in
-- `Slides.Scene.Digital`.

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Slides.Scalar.Core using (OrdMon; Sub; IsOrdMonHom)
open import Slides.Diagram.Overlay using (Overlays; IsOverlayHom)

module Slides.Scene.Tick
  {T₁ T₂ D₁ D₂ X₁ X₂ : Set}
  (M₁ : OrdMon T₁) (Sb₁ : Sub M₁) (M₂ : OrdMon T₂) (Sb₂ : Sub M₂)
  (h : T₁ → T₂) (H : IsOrdMonHom M₁ M₂ h)
  (val₁ : D₁ → T₁ → T₁) (val₂ : D₂ → T₂ → T₂) (g : D₁ → D₂)
  (g-val : ∀ c τ → val₂ (g c) (h τ) ≡ h (val₁ c τ))
  (O₁ : Overlays X₁) (O₂ : Overlays X₂) (F : X₁ → X₂) (HF : IsOverlayHom O₁ O₂ F) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ)
import Data.Nat as ℕ
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Container.Core using (_⇒_; position)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (refl; cong; cong₂; sym; trans; subst)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Container.Interpret.Plain using (pfold-rel-translate)
open import Container.Lowering using (translate)
open import Slides.Scene.Syntax
import Slides.Scene.Events {D = D₁} M₁ Sb₁ as E₁
import Slides.Scene.Events {D = D₂} M₂ Sb₂ as E₂
import Slides.Scene.Sample {D = D₁} {X₁} M₁ Sb₁ val₁ O₁ as S₁
import Slides.Scene.Sample {D = D₂} {X₂} M₂ Sb₂ val₂ O₂ as S₂
private
  module O₁ = OrdMon M₁
  module O₂ = OrdMon M₂
  module Sb₁′ = Sub Sb₁
  module Sb₂′ = Sub Sb₂
open IsOrdMonHom H
open IsOverlayHom HF

-- Windows, shifts and overlay commute with `h`

private
  mapM : Maybe X₁ → Maybe X₂
  mapM = Maybe.map F

  -- comparisons agree
  sel-≡ : ∀ {a a′ b} → h a ≡ a′ → (da : Dec (a O₁.≤ b)) (db : Dec (a′ O₂.≤ h b)) {A : Set} (x y : A) →
          O₂.select db x y ≡ O₁.select da x y
  sel-≡ refl da db x y = sym (h-select da db x y)

  map-select : ∀ {a b} (d : Dec (a O₁.≤ b)) x y → mapM (O₁.select d x y) ≡ O₁.select d (mapM x) (mapM y)
  map-select (yes _) x y = refl
  map-select (no _)  x y = refl

  pos-h : ∀ w → E₂.pos (h w) ≡ h (E₁.pos w)
  pos-h w = trans (cong (λ z → z O₂.⊔ h w) (sym h-0)) (sym (h-⊔ O₁.0# w))

  param-h : ∀ q t → S₂.param (Maybe.map g q) (h t) ≡ h (S₁.param q t)
  param-h nothing  t = sym h-0
  param-h (just c) t = g-val c t

  win-h : ∀ w t y → S₂.win (h w) (h t) (mapM y) ≡ mapM (S₁.win w t y)
  win-h w t y =
    trans (sel-≡ h-0 (O₁._≤?_ O₁.0# t) (O₂._≤?_ O₂.0# (h t)) _ _)
      (trans (cong (λ z → O₁.select (O₁._≤?_ O₁.0# t) z nothing)
                   (sel-≡ refl (O₁._≤?_ w t) (O₂._≤?_ (h w) (h t)) nothing (mapM y)))
             (sym (trans (map-select (O₁._≤?_ O₁.0# t) _ nothing)
                         (cong (λ z → O₁.select (O₁._≤?_ O₁.0# t) z nothing)
                               (map-select (O₁._≤?_ w t) nothing y)))))

  back-h : ∀ w t (r₁ : T₁ → Maybe X₁) (r₂ : T₂ → Maybe X₂) → (∀ u → r₂ (h u) ≡ mapM (r₁ u)) →
           S₂.back (h w) (h t) r₂ ≡ mapM (S₁.back w t r₁)
  back-h w t r₁ r₂ e with O₁._≤?_ w t
  ... | yes w≤t with O₂._≤?_ (h w) (h t)
  ...   | yes _ = trans (cong r₂ (sym (h-sub Sb₁ Sb₂ w≤t))) (e (t Sb₁′.- w))
  ...   | no ¬h = ⊥-elim (¬h (h-mono w≤t))
  back-h w t r₁ r₂ e | no w≰t with O₂._≤?_ (h w) (h t)
  ... | yes hh = ⊥-elim (w≰t (h-reflect hh))
  ... | no _ = refl

-- The relation: durations map by `h`, drivers by `g`, readings by `F` (`Slides.Scene.Relation`)

RT : T₁ → T₂ → Set
RT d e = e ≡ h d

RD : D₁ → D₂ → Set
RD c c′ = c′ ≡ g c

RP : S₁.Rd → S₂.Rd → Set
RP r r′ = ∀ t q → r′ (h t) (Maybe.map g q) ≡ Maybe.map F (r t q)

import Slides.Scene.Relation as Rln
module Lg = Rln M₁ M₂ S₁.rdP S₂.rdP RT RD RP

R : S₁.Timed → S₂.Timed → Set
R = Lg.R

private
  RP-clip : ∀ w {r r′} → RP r r′ → RP (λ t q → S₁.win (E₁.pos w) t (r t q)) (λ t q → S₂.win (E₂.pos (h w)) t (r′ t q))
  RP-clip w {r} {r′} a rewrite pos-h w = λ t q → trans (cong (S₂.win (h (E₁.pos w)) (h t)) (a t q)) (win-h (E₁.pos w) t (r t q))

  RP-shift : ∀ w {r r′} → RP r r′ → RP (λ t q → S₁.back (E₁.pos w) t (λ u → r u q)) (λ t q → S₂.back (E₂.pos (h w)) t (λ u → r′ u q))
  RP-shift w {r} {r′} a rewrite pos-h w =
    λ t q → back-h (E₁.pos w) t (λ u → r u q) (λ u → r′ u (Maybe.map g q)) (λ u → a u q)

logical : Lg.Logical
logical = record
  { RT-0 = sym h-0
  ; RT-+ = λ { {a} {_} {b} refl refl → sym (h-+ a b) }
  ; RT-⊔ = λ { {a} {_} {b} refl refl → sym (h-⊔ a b) }
  ; RT-pos = λ { {w} refl → pos-h w }
  ; RP-none = λ t q → refl
  ; RP-par = λ { {r₁} {r₁′} a b t q → trans (cong₂ S₂.merge (a t q) (b t q)) (sym (merge-map (r₁ t q) (r₁′ t q))) }
  ; RP-clip = λ { {w} {_} {r} {r′} refl a → RP-clip w {r} {r′} a }
  ; RP-shift = λ { {w} {_} {r} {r′} refl a → RP-shift w {r} {r′} a }
  ; RP-drive = λ { {c} refl a t q → a t (just c) }
  }

module _ {A : Set} (ℓ₁ : A → T₁ → X₁) (ℓ₂ : A → T₂ → X₂) (ℓ-ok : ∀ a p → ℓ₂ a (h p) ≡ F (ℓ₁ a p)) where

  rel-leaf : ∀ a → R (S₁.leafT ℓ₁ a) (S₂.leafT ℓ₂ a)
  rel-leaf a = sym h-0 , λ t q →
    trans (sel-≡ h-0 (O₁._≤?_ O₁.0# t) (O₂._≤?_ O₂.0# (h t)) _ _)
      (trans (cong (λ z → O₁.select (O₁._≤?_ O₁.0# t) z nothing) (cong just (trans (cong (ℓ₂ a) (param-h q t)) (ℓ-ok a _))))
             (sym (map-select (O₁._≤?_ O₁.0# t) _ nothing)))

  rel-hom : ∀ o {k : arity (proj₁ o) → S₁.Timed} {k′ : arity (proj₁ o) → S₂.Timed} → (∀ p → R (k p) (k′ p)) →
            R (S₁.dirH o k) (S₂.dirH (mapOp h g o) (λ q → k′ (position (mapSC h g) {o} q)))
  rel-hom Seq        {k} {k′} e = Lg.rel-seq logical {k zero} {k′ zero} {k (suc zero)} {k′ (suc zero)} (e zero) (e (suc zero))
  rel-hom Par        {k} {k′} e = Lg.rel-par logical {k zero} {k′ zero} {k (suc zero)} {k′ (suc zero)} (e zero) (e (suc zero))
  rel-hom (Hold d)   {k} {k′} e = Lg.rel-hold logical {x = k tt} {k′ tt} refl (e tt)
  rel-hom (Delay d)  {k} {k′} e = Lg.rel-delay logical {x = k tt} {k′ tt} refl (e tt)
  rel-hom (Repeat n) {k} {k′} e = Lg.rel-rep logical n {k tt} {k′ tt} (e tt)
  rel-hom (Drive c)  {k} {k′} e = Lg.rel-drive logical {x = k tt} {k′ tt} refl (e tt)

  -- Reading the mapped scene at `h t` is reading the scene at `t`.
  tick-hom : ∀ s → proj₁ (S₂.sample ℓ₂ (mapScene h g s)) ≡ h (proj₁ (S₁.sample ℓ₁ s)) ×
                   (∀ t q → proj₂ (S₂.sample ℓ₂ (mapScene h g s)) (h t) (Maybe.map g q)
                            ≡ Maybe.map F (proj₂ (S₁.sample ℓ₁ s) t q))
  tick-hom = pfold-rel-translate (mapSC h g) R (λ o k k′ e → rel-hom o {k} {k′} e) rel-leaf
