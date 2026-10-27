{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE: proofs and the vocabulary they need; no executable imports it (`tests/check_closure.py`).
--
-- Agreement of a list of frames with a list of symbolic frames: the induction both assembly
-- theorems carry.
--
-- The symbolic frames of an animation are elements of a type `Sym` (for continuous templates
-- `Dia (Expr ℕ)`, for discrete ones `Dia (DExpr ℕ)`), each *interpreted* at an assignment as the
-- layout in ℕ it stands for (`interp`: lay it out symbolically, evaluate at `ρ`), with `atop`
-- of symbolic frames (`atopS`) interpreted as `atop` of layouts (`interp-atop`: layout is
-- natural along evaluation, `Slides.Diagram.Layout.Properties.atop-natural`).  That is the whole
-- interface; the rest (agreement is preserved by `merge`, by `++` with the tick shifted, and
-- lists in agreement are equally long) is independent of which expression language the symbolic
-- frames are over, so it is proved once.

module Slides.Anim.Assembly where

open import Data.Bool using (true; false; if_then_else_; T)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ; suc; _+_; _∸_; _<ᵇ_; _≤_)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Slides.Diagram.Draw using (Layout)
open import Slides.Diagram.Syntax using (Dia; atop)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (natOps)
import Slides.Diagram.Place natOps as PN
open import Slides.Anim.Arith using (<ᵇ-ge)
open import Slides.Anim.Nth
open import Slides.Anim.Timeline using (merge; mergeM)

private
  layoutℕ : Dia ℕ → Layout ℕ
  layoutℕ = LayoutWith.layout natOps

module Over
  (Sym : Set)
  (interp : Sym → (ℕ → ℕ) → Layout ℕ)
  (atopS : Sym → Sym → Sym)
  (interp-atop : ∀ x y ρ → PN.atop (interp x ρ) (interp y ρ) ≡ interp (atopS x y) ρ)
  where

  ------------------------------------------------------------------------
  -- Agreement

  -- one frame against one symbolic frame, at the assignments satisfying `G`; a frame that is
  -- there on one side is there on the other
  data Rel (G : (ℕ → ℕ) → Set) : Maybe (Dia ℕ) → Maybe Sym → Set where
    noFrame : Rel G nothing nothing
    bothFrames : ∀ {x y} → (∀ ρ → G ρ → layoutℕ x ≡ interp y ρ) → Rel G (just x) (just y)

  Rel-⇒ : ∀ {G G′ : (ℕ → ℕ) → Set} → (∀ ρ → G ρ → G′ ρ) → ∀ {a b} → Rel G′ a b → Rel G a b
  Rel-⇒ f noFrame     = noFrame
  Rel-⇒ f (bothFrames r) = bothFrames (λ ρ g → r ρ (f ρ g))

  -- the frames of `xs` (from tick `t` on) are the symbolic frames `ys` evaluated at the
  -- assignments in `G k`; `G` says which assignments are meant at the absolute tick `k`
  record Agree (G : ℕ → (ℕ → ℕ) → Set) (t : ℕ) (xs : List (Dia ℕ)) (ys : List Sym) : Set where
    constructor agree
    field at : ∀ j → Rel (G (t + j)) (nth xs j) (nth ys j)
  open Agree public

  Agree-≡ : ∀ {G t t′ xs ys} → t ≡ t′ → Agree G t xs ys → Agree G t′ xs ys
  Agree-≡ refl a = a

  -- `atop` of the frames is `atop` of the symbolic frames (`interp-atop`)
  Rel-mergeM : ∀ {G₁ G₂ : (ℕ → ℕ) → Set} {a b a′ b′} → Rel G₁ a a′ → Rel G₂ b b′ →
               Rel (λ ρ → G₁ ρ × G₂ ρ) (mergeM atop a b) (mergeM atopS a′ b′)
  Rel-mergeM noFrame         rb         = Rel-⇒ (λ ρ → proj₂) rb
  Rel-mergeM (bothFrames ra)    noFrame       = Rel-⇒ (λ ρ → proj₁) (bothFrames ra)
  Rel-mergeM (bothFrames {x} {x′} ra) (bothFrames {y} {y′} rb) = bothFrames λ ρ (g₁ , g₂) →
    trans (cong₂ PN.atop (ra ρ g₁) (rb ρ g₂)) (interp-atop x′ y′ ρ)

  -- `merge` of lists is `atop` frame by frame
  Agree-merge : ∀ {G₁ G₂ t xs xs′ ys ys′} → Agree G₁ t xs xs′ → Agree G₂ t ys ys′ →
                Agree (λ k ρ → G₁ k ρ × G₂ k ρ) t (merge atop xs ys) (merge atopS xs′ ys′)
  Agree-merge {G₁} {G₂} {t} {xs} {xs′} {ys} {ys′} a₁ a₂ = agree go
    where
      go : ∀ j → Rel (λ ρ → G₁ (t + j) ρ × G₂ (t + j) ρ) (nth (merge atop xs ys) j) (nth (merge atopS xs′ ys′) j)
      go j rewrite nth-merge atop xs ys j | nth-merge atopS xs′ ys′ j = Rel-mergeM (at a₁ j) (at a₂ j)

  -- lists in agreement are as long as each other
  private
    len≤ : ∀ {A B : Set} (xs : List A) (ys : List B) →
           (∀ j → nth ys j ≡ nothing → nth xs j ≡ nothing) → length xs ≤ length ys
    len≤ []       ys       h = ℕ.z≤n
    len≤ (x ∷ xs) []       h with h 0 refl
    ... | ()
    len≤ (x ∷ xs) (y ∷ ys) h = ℕ.s≤s (len≤ xs ys (λ j → h (suc j)))

    Rel-nothingˡ : ∀ {G a b} → Rel G a b → a ≡ nothing → b ≡ nothing
    Rel-nothingˡ noFrame     refl = refl
    Rel-nothingˡ (bothFrames _) ()

    Rel-nothingʳ : ∀ {G a b} → Rel G a b → b ≡ nothing → a ≡ nothing
    Rel-nothingʳ noFrame     refl = refl
    Rel-nothingʳ (bothFrames _) ()

  Agree-length : ∀ {G t xs ys} → Agree G t xs ys → length xs ≡ length ys
  Agree-length {G} {t} {xs} {ys} ag =
    ℕP.≤-antisym (len≤ xs ys (λ j e → Rel-nothingʳ (at ag j) e))
                 (len≤ ys xs (λ j e → Rel-nothingˡ (at ag j) e))

  Agree-++ : ∀ {G₁ G₂ t xs xs′ ys ys′} → Agree G₁ t xs xs′ → Agree G₂ (t + length xs) ys ys′ →
             Agree (λ k ρ → G₁ k ρ × G₂ k ρ) t (xs ++ ys) (xs′ ++ ys′)
  Agree-++ {G₁} {G₂} {t} {xs} {xs′} {ys} {ys′} a₁ a₂ = agree λ j →
    go j (length xs) refl (sym (Agree-length a₁))
    where
      go : ∀ j n → length xs ≡ n → length xs′ ≡ n →
           Rel (λ ρ → G₁ (t + j) ρ × G₂ (t + j) ρ) (nth (xs ++ ys) j) (nth (xs′ ++ ys′) j)
      go j n e e′ rewrite nth-++′ xs ys j n e | nth-++′ xs′ ys′ j n e′ with j <ᵇ n in eq
      ... | true  = Rel-⇒ (λ ρ → proj₁) (at a₁ j)
      ... | false = Rel-⇒ (λ ρ → proj₂)
                      (subst (λ k → Rel (G₂ k) (nth ys (j ∸ n)) (nth ys′ (j ∸ n)))
                             (trans (ℕP.+-assoc t n (j ∸ n)) (cong (t +_) (ℕP.m+[n∸m]≡n {n} {j} (<ᵇ-ge eq))))
                             (subst (λ m → Rel (G₂ (t + m + (j ∸ n))) (nth ys (j ∸ n)) (nth ys′ (j ∸ n))) e (at a₂ (j ∸ n))))

  -- one frame against a symbolic one, as the statement of the assembly theorem
  Rel-just : ∀ {G F m} → Rel G (just F) m →
             ∃ λ S → m ≡ just S × (∀ ρ → G ρ → layoutℕ F ≡ interp S ρ)
  Rel-just (bothFrames {y = y} r) = y , refl , r
