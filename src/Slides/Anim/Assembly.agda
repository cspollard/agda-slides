{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE: proofs and the vocabulary they need; no executable imports it (`tests/check_closure.py`).
--
-- The assembly calculus: a logical relation over the temporal skeleton of two readings of a scene
-- (`Slides.Anim.Sample`), in two clocks `K₁`, `K₂` related by their tick embeddings `ι`.
--
--     RelN R x y   the durations are equal and, at every tick `k`, `R k` relates what `x` shows at
--                  `ι₁ k` to what `y` shows at `ι₂ k`
--
-- `R` is a family over the tick, because `Seq` and `Delay` shift the tick of what follows (`relN-seq`:
-- the right operand is related by `R` shifted by the left duration).  `RelN` is closed under the
-- connectives with only the clock laws (`ClockLaws`: the window and the order are matched by `ι`,
-- the exact case of subtraction), so the assembly of a whole animation is an induction that
-- delegates to the leaf: it needs the exactness hypotheses (`Faithful`) only there, and nothing for
-- the temporal skeleton.  Two instances: ℚ against ℕ (`Slides.Anim.Assembly.Continuous`, the
-- continuous frame at a whole tick is the discrete one) and ℕ against ℕ (`Slides.Anim.Param.Properties`,
-- the discrete frame is the evaluation of the symbolic one).
--
-- `Over` is the vocabulary for the second: frames compared as layouts, a symbolic frame interpreted
-- at an assignment.

module Slides.Anim.Assembly where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ; _+_; _∸_)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Slides.Diagram.Draw using (Layout)
open import Slides.Diagram.Syntax using (Dia; atop)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (natOps)
import Slides.Diagram.Place natOps as PN
open import Slides.Time
open import Slides.Anim.Arith using (<ᵇ-ge)
open import Slides.Anim.Sample
open import Slides.Anim.Sample.Properties using (win-ι)

module Calculus (K₁ K₂ : Clock) (L₁ : ClockLaws K₁) (L₂ : ClockLaws K₂) where
  private
    module C₁ = Clock K₁
    module C₂ = Clock K₂
    module P₁ = ClockLaws L₁
    module P₂ = ClockLaws L₂

  RelN : ∀ {X Y : Set} → (ℕ → Maybe X → Maybe Y → Set) → TM K₁ X → TM K₂ Y → Set
  RelN R (n , f) (m , g) = n ≡ m × ∀ k → R k (f (C₁.ι k)) (g (C₂.ι k))

  relN-mono : ∀ {X Y} {R R′ : ℕ → Maybe X → Maybe Y → Set} {x y} →
              (∀ k a b → R k a b → R′ k a b) → RelN R x y → RelN R′ x y
  relN-mono h (e , r) = e , λ k → h k _ _ (r k)

  -- the window
  relN-hold : ∀ {X Y} {R : ℕ → Maybe X → Maybe Y → Set} {x : TM K₁ X} {y : TM K₂ Y} →
              (∀ k → R k nothing nothing) → RelN R x y → ∀ n → RelN R (holdT K₁ n x) (holdT K₂ n y)
  relN-hold {R = R} {_ , f} {_ , g} nn (_ , r) n = refl , tick
    where
      tick : ∀ k → R k (if win K₁ n (C₁.ι k) then f (C₁.ι k) else nothing) (if win K₂ n (C₂.ι k) then g (C₂.ι k) else nothing)
      tick k rewrite win-ι K₁ L₁ n k | win-ι K₂ L₂ n k with k ℕ.<ᵇ n
      ... | true  = r k
      ... | false = nn k

  -- the right operand of `Seq` is related by `R` shifted by the left duration
  relN-seq : ∀ {X Y} {R : ℕ → Maybe X → Maybe Y → Set} {x₁ x₂ : TM K₁ X} {y₁ y₂ : TM K₂ Y} →
             (∀ k → R k nothing nothing) → RelN R x₁ y₁ → RelN (λ k → R (proj₁ x₁ + k)) x₂ y₂ →
             RelN R (seqW K₁ x₁ x₂) (seqW K₂ y₁ y₂)
  relN-seq {R = R} {n₁ , f₁} {n₂ , f₂} {_ , g₁} {_ , g₂} nn (refl , r₁) (refl , r₂) = refl , tick
    where
      tick : ∀ k → R k
        (if win K₁ (n₁ + n₂) (C₁.ι k) then (if C₁.ι k C₁.<ᵇ C₁.ι n₁ then f₁ (C₁.ι k) else f₂ (C₁.ι k C₁.- C₁.ι n₁)) else nothing)
        (if win K₂ (n₁ + n₂) (C₂.ι k) then (if C₂.ι k C₂.<ᵇ C₂.ι n₁ then g₁ (C₂.ι k) else g₂ (C₂.ι k C₂.- C₂.ι n₁)) else nothing)
      tick k rewrite win-ι K₁ L₁ (n₁ + n₂) k | win-ι K₂ L₂ (n₁ + n₂) k | P₁.ι-<ᵇ k n₁ | P₂.ι-<ᵇ k n₁
        with k ℕ.<ᵇ n₁ + n₂ | k ℕ.<ᵇ n₁ in eq
      ... | false | _     = nn k
      ... | true  | true  = r₁ k
      ... | true  | false
        rewrite sym (P₁.ι-∸ k n₁ (<ᵇ-ge {k} {n₁} eq)) | sym (P₂.ι-∸ k n₁ (<ᵇ-ge {k} {n₁} eq)) =
        subst (λ t → R t (f₂ (C₁.ι (k ∸ n₁))) (g₂ (C₂.ι (k ∸ n₁)))) (ℕP.m+[n∸m]≡n (<ᵇ-ge {k} {n₁} eq)) (r₂ (k ∸ n₁))

  relN-delay : ∀ {X Y} {R : ℕ → Maybe X → Maybe Y → Set} {x : TM K₁ X} {y : TM K₂ Y} {n} →
               (∀ k → R k nothing nothing) → RelN (λ k → R (n + k)) x y →
               RelN R (delayT K₁ n x) (delayT K₂ n y)
  relN-delay {R = R} {x = _ , f} {y = _ , g} {n = n} nn (refl , r) = refl , tick
    where
      tick : ∀ k → R k (if C₁.ι k C₁.<ᵇ C₁.ι n then nothing else f (C₁.ι k C₁.- C₁.ι n))
                       (if C₂.ι k C₂.<ᵇ C₂.ι n then nothing else g (C₂.ι k C₂.- C₂.ι n))
      tick k rewrite P₁.ι-<ᵇ k n | P₂.ι-<ᵇ k n with k ℕ.<ᵇ n in eq
      ... | true  = nn k
      ... | false rewrite sym (P₁.ι-∸ k n (<ᵇ-ge {k} {n} eq)) | sym (P₂.ι-∸ k n (<ᵇ-ge {k} {n} eq)) =
        subst (λ t → R t (f (C₁.ι (k ∸ n))) (g (C₂.ι (k ∸ n)))) (ℕP.m+[n∸m]≡n (<ᵇ-ge {k} {n} eq)) (r (k ∸ n))

  -- both sides run at the same time; the relation must be closed under overlay
  relN-par : ∀ {X Y} {R R₁ R₂ : ℕ → Maybe X → Maybe Y → Set} {x₁ x₂ : TM K₁ X} {y₁ y₂ : TM K₂ Y} {⊙₁ ⊙₂} →
             (∀ k a b a′ b′ → R₁ k a b → R₂ k a′ b′ → R k (mergeM ⊙₁ a a′) (mergeM ⊙₂ b b′)) →
             RelN R₁ x₁ y₁ → RelN R₂ x₂ y₂ → RelN R (Sem.parAt K₁ ⊙₁ x₁ x₂) (Sem.parAt K₂ ⊙₂ y₁ y₂)
  relN-par {R = R} {R₁} {R₂} {_ , _} {_ , _} {_ , _} {_ , _} cl (e₁ , r₁) (e₂ , r₂) =
    cong₂ ℕ._⊔_ e₁ e₂ , λ k → cl k _ _ _ _ (r₁ k) (r₂ k)

------------------------------------------------------------------------
-- Frames against symbolic frames

-- The symbolic frames of an animation are elements of a type `Sym` (for templates `Dia (OExpr ℕ)`),
-- each *interpreted* at an assignment as the layout in ℕ it stands for (`interp`: lay it out
-- symbolically, evaluate at `ρ`), with `atop` of symbolic frames (`atopS`) interpreted as `atop` of
-- layouts (`interp-atop`: layout is natural along evaluation,
-- `Slides.Diagram.Layout.Properties.atop-natural`).  That is the whole interface.
module Over
  (Sym : Set)
  (interp : Sym → (ℕ → ℕ) → Layout ℕ)
  (atopS : Sym → Sym → Sym)
  (interp-atop : ∀ x y ρ → PN.atop (interp x ρ) (interp y ρ) ≡ interp (atopS x y) ρ)
  where

  private
    layoutℕ : Dia ℕ → Layout ℕ
    layoutℕ = LayoutWith.layout natOps

  -- one frame against one symbolic frame, at the assignments satisfying `G`; a frame that is
  -- there on one side is there on the other
  data Rel (G : (ℕ → ℕ) → Set) : Maybe (Dia ℕ) → Maybe Sym → Set where
    noFrame : Rel G nothing nothing
    bothFrames : ∀ {x y} → (∀ ρ → G ρ → layoutℕ x ≡ interp y ρ) → Rel G (just x) (just y)

  Rel-⇒ : ∀ {G G′ : (ℕ → ℕ) → Set} → (∀ ρ → G ρ → G′ ρ) → ∀ {a b} → Rel G′ a b → Rel G a b
  Rel-⇒ f noFrame        = noFrame
  Rel-⇒ f (bothFrames r) = bothFrames (λ ρ g → r ρ (f ρ g))

  -- `atop` of the frames is `atop` of the symbolic frames (`interp-atop`)
  Rel-mergeM : ∀ {G₁ G₂ : (ℕ → ℕ) → Set} {a b a′ b′} → Rel G₁ a a′ → Rel G₂ b b′ →
               Rel (λ ρ → G₁ ρ × G₂ ρ) (mergeM atop a b) (mergeM atopS a′ b′)
  Rel-mergeM noFrame         rb         = Rel-⇒ (λ ρ → proj₂) rb
  Rel-mergeM (bothFrames ra) noFrame    = Rel-⇒ (λ ρ → proj₁) (bothFrames ra)
  Rel-mergeM (bothFrames {x} {x′} ra) (bothFrames {y} {y′} rb) = bothFrames λ ρ (g₁ , g₂) →
    trans (cong₂ PN.atop (ra ρ g₁) (rb ρ g₂)) (interp-atop x′ y′ ρ)

  -- one frame against a symbolic one, as the statement of the assembly theorem
  Rel-just : ∀ {G F m} → Rel G (just F) m →
             ∃ λ S → m ≡ just S × (∀ ρ → G ρ → layoutℕ F ≡ interp S ρ)
  Rel-just (bothFrames {y = y} r) = y , refl , r
