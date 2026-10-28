{-# OPTIONS --safe --without-K #-}

-- Clocks: reading a scene along an order embedding of time (`ι : ℕ → ℚ`).
--
-- A scene over the durations of one clock maps to a scene over another by `h` on its durations
-- (`mapScene`, a container morphism, so `translate`).  If `h` is an order embedding
-- (`IsOrdMonHom`, which preserves `⊔`, comparisons and exact differences), drivers are carried
-- (`g-val`) and overlay is (`IsOverlayHom`), then reading the mapped scene at `h t` is reading the
-- original at `t` (`tick-hom`): durations map by `h`, and the frames by `F`, given that leaves
-- do (`ℓ-ok`).  It is the logical relation `R` over the signature, one lemma per operation.
-- `Slides.Scene.Digital` instantiates it at `ι` with `digitise` for the leaves.

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

------------------------------------------------------------------------
-- The scene map

mapOp : Op T₁ D₁ → Op T₂ D₂
mapOp Seq        = Seq
mapOp Par        = Par
mapOp (Hold d)   = Hold (h d)
mapOp (Delay d)  = Delay (h d)
mapOp (Repeat n) = Repeat n
mapOp (Drive c)  = Drive (g c)

mapSC : SceneC T₁ D₁ ⇒ SceneC T₂ D₂
mapSC = record { shape = mapOp ; position = pos }
  where
    pos : ∀ {o} → arity (mapOp o) → arity o
    pos {Seq}      p = p
    pos {Par}      p = p
    pos {Hold _}   p = p
    pos {Delay _}  p = p
    pos {Repeat _} p = p
    pos {Drive _}  p = p

mapScene : ∀ {A : Set} → Scene T₁ D₁ A → Scene T₂ D₂ A
mapScene = translate mapSC

------------------------------------------------------------------------
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

------------------------------------------------------------------------
-- The relation: durations map by `h`, readings by `F`

R : S₁.Timed → S₂.Timed → Set
R x y = proj₁ y ≡ h (proj₁ x) × ∀ t q → proj₂ y (h t) (Maybe.map g q) ≡ Maybe.map F (proj₂ x t q)

rel-par : ∀ {x x′ y y′} → R x x′ → R y y′ → R (S₁.parT x y) (S₂.parT x′ y′)
rel-par {dx , rx} {_ , rx′} {dy , ry} {_ , ry′} (refl , a) (refl , b) =
  sym (h-⊔ dx dy) , λ t q → trans (cong₂ S₂.merge (a t q) (b t q)) (sym (merge-map (rx t q) (ry t q)))

rel-hold : ∀ w {x x′} → R x x′ → R (S₁.holdT w x) (S₂.holdT (h w) x′)
rel-hold w {_ , r} {_ , r′} (_ , a) rewrite pos-h w =
  refl , λ t q → trans (cong (S₂.win (h (E₁.pos w)) (h t)) (a t q)) (win-h (E₁.pos w) t (r t q))

rel-delay : ∀ w {x x′} → R x x′ → R (S₁.delayT w x) (S₂.delayT (h w) x′)
rel-delay w {d , r} {_ , r′} (refl , a) rewrite pos-h w =
  sym (h-+ (E₁.pos w) d) ,
  λ t q → back-h (E₁.pos w) t (λ u → r u q) (λ u → r′ u (Maybe.map g q)) (λ u → a u q)

rel-drive : ∀ c {x x′} → R x x′ → R (S₁.driveT c x) (S₂.driveT (g c) x′)
rel-drive c (e , a) = e , λ t q → a t (just c)

rel-seq : ∀ {x x′ y y′} → R x x′ → R y y′ → R (S₁.seqT x y) (S₂.seqT x′ y′)
rel-seq {dx , rx} {.(h dx) , rx′} {dy , ry} {.(h dy) , ry′} (refl , a) (refl , b) =
  sym (h-+ dx dy) ,
  proj₂ (rel-par {S₁.holdT dx (dx , rx)} {S₂.holdT (h dx) (h dx , rx′)}
                 {S₁.delayT dx (S₁.holdT dy (dy , ry))} {S₂.delayT (h dx) (S₂.holdT (h dy) (h dy , ry′))}
           (rel-hold dx {dx , rx} {h dx , rx′} (refl , a))
           (rel-delay dx {S₁.holdT dy (dy , ry)} {S₂.holdT (h dy) (h dy , ry′)}
              (rel-hold dy {dy , ry} {h dy , ry′} (refl , b))))

rel-rep : ∀ n {x x′} → R x x′ → R (S₁.repT n x) (S₂.repT n x′)
rel-rep ℕ.zero    rx = sym h-0 , λ t q → refl
rel-rep (ℕ.suc n) {x} {x′} rx = rel-seq {x} {x′} {S₁.repT n x} {S₂.repT n x′} rx (rel-rep n rx)

module _ {A : Set} (ℓ₁ : A → T₁ → X₁) (ℓ₂ : A → T₂ → X₂) (ℓ-ok : ∀ a p → ℓ₂ a (h p) ≡ F (ℓ₁ a p)) where

  rel-leaf : ∀ a → R (S₁.leafT ℓ₁ a) (S₂.leafT ℓ₂ a)
  rel-leaf a = sym h-0 , λ t q →
    trans (sel-≡ h-0 (O₁._≤?_ O₁.0# t) (O₂._≤?_ O₂.0# (h t)) _ _)
      (trans (cong (λ z → O₁.select (O₁._≤?_ O₁.0# t) z nothing) (cong just (trans (cong (ℓ₂ a) (param-h q t)) (ℓ-ok a _))))
             (sym (map-select (O₁._≤?_ O₁.0# t) _ nothing)))

  rel-hom : ∀ o {k : arity o → S₁.Timed} {k′ : arity o → S₂.Timed} → (∀ p → R (k p) (k′ p)) →
            R (S₁.dirH o k) (S₂.dirH (mapOp o) (λ q → k′ (position mapSC q)))
  rel-hom Seq        {k} {k′} e = rel-seq {k zero} {k′ zero} {k (suc zero)} {k′ (suc zero)} (e zero) (e (suc zero))
  rel-hom Par        {k} {k′} e = rel-par {k zero} {k′ zero} {k (suc zero)} {k′ (suc zero)} (e zero) (e (suc zero))
  rel-hom (Hold d)   {k} {k′} e = rel-hold d {k tt} {k′ tt} (e tt)
  rel-hom (Delay d)  {k} {k′} e = rel-delay d {k tt} {k′ tt} (e tt)
  rel-hom (Repeat n) {k} {k′} e = rel-rep n {k tt} {k′ tt} (e tt)
  rel-hom (Drive c)  {k} {k′} e = rel-drive c {k tt} {k′ tt} (e tt)

  -- Reading the mapped scene at `h t` is reading the scene at `t`.
  tick-hom : ∀ s → proj₁ (S₂.sample ℓ₂ (mapScene s)) ≡ h (proj₁ (S₁.sample ℓ₁ s)) ×
                   (∀ t q → proj₂ (S₂.sample ℓ₂ (mapScene s)) (h t) (Maybe.map g q)
                            ≡ Maybe.map F (proj₂ (S₁.sample ℓ₁ s) t q))
  tick-hom = pfold-rel-translate mapSC R (λ o k k′ e → rel-hom o {k} {k′} e) rel-leaf
