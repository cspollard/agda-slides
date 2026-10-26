{-# OPTIONS --safe --without-K #-}

-- The assembly of whole frames for discrete templates: the symbolic frames of
-- `Slides.Anim.DParam` are the frames of the animation (cf. `Slides.Anim.ParamCorrect`, for
-- continuous templates read in ℕ).
--
-- Statement.  Let `a` be an animation whose segments are `template` or `discrete` (so that
-- `dleaves 0 0 a ≡ just (i′ , l)`).  For every tick `k < dur a`,
--
--     layout_ℕ (frame k of  timeline atop (frames natOps) a)
--       ≡  mapLayout (evalD natD ρ) (layout_DExpr (symbolic frame k))
--
-- for every assignment `ρ` such that every leaf running at tick `k` has
-- `ρ (idx) ≡ units (sample of its track at that tick)` (`DGoodL l k ρ`).  The right-hand side
-- is what the page computes: the formulas of the tick, read in ℕ (`Slides.Anim.Formula.encD-semN`
-- says that the shipped, folded formula is `evalD natD ρ`), and the left is the frame the
-- flipbook shows.  The proof is the one of `Slides.Anim.ParamCorrect` -- the induction is
-- `Slides.Anim.Assembly`, shared -- with `Slides.Diagram.EuclidNatural` for one segment: the
-- Euclidean operations never reach the layout, they only live in the leaves' formulas.
--
-- Not repeated here: that `DGoodL` is satisfiable by `i ↦ (parameter of segment i at tick k)`
-- for the shipped segments (`canonical-good`, `paramOf-assembly-canonical` of `ParamCorrect`);
-- the numbering of the leaves is the same code as for continuous templates.

module Slides.Anim.DParamCorrect where

open import Data.Bool using (true; false; if_then_else_)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Data.Unit using (⊤)
open import Data.Fin using (zero; suc)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Slides.Diagram.Draw using (Layout; mapLayout)
open import Slides.Diagram.Syntax using (Dia; atop; mapDia)
open import Slides.Diagram.Expr using (Expr; eval)
open import Slides.Diagram.Euclid
open import Slides.Diagram.EuclidNatural using (layout-evalD; layout-weakenE)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (Ops; natOps)
open import Slides.Diagram.LayoutNatural using (atop-natural)
import Slides.Anim.Track as T
open import Slides.Anim.Syntax
open import Slides.Anim.Timeline using (timeline; frames; length-dur)
open import Slides.Anim.Nth
open import Slides.Anim.DParam
import Slides.Anim.Assembly as Asm

private
  layoutℕ : Dia ℕ → Layout ℕ
  layoutℕ = LayoutWith.layout natOps

  layoutD : Dia (DExpr ℕ) → Layout (DExpr ℕ)
  layoutD = LayoutWith.layout dexprOps

-- a symbolic frame is interpreted by evaluating its layout in ℕ; `atop` is `atop` because layout
-- is natural along `evalD`, an `Ops`-homomorphism
open Asm.Over (Dia (DExpr ℕ)) (λ y ρ → mapLayout (evalD natD ρ) (layoutD y)) atop
  (λ x y ρ → sym (atop-natural dexprOps natOps (evalD natD ρ) (evalD-hom-ℕ ρ) (layoutD x) (layoutD y)))

------------------------------------------------------------------------
-- One segment

-- `ρ` gives the leaf's variable the parameter its track has at the tick `m` that falls on `k`
DLeafGood : DLeaf → ℕ → (ℕ → ℕ) → Set
DLeafGood l k ρ = ∀ m → (m <ᵇ T.dur (DLeaf.track l)) ≡ true → DLeaf.start l + m ≡ k →
                  ρ (DLeaf.idx l) ≡ units (proj₂ (T.sample T.ℚLerp (DLeaf.track l)) m)

DGoodL : AnimC ⋆ DLeaf → ℕ → (ℕ → ℕ) → Set
DGoodL (pure l)              k ρ = DLeafGood l k ρ
DGoodL (impure (Seq , c))    k ρ = DGoodL (c zero) k ρ × DGoodL (c (suc zero)) k ρ
DGoodL (impure (Par , c))    k ρ = DGoodL (c zero) k ρ × DGoodL (c (suc zero)) k ρ

-- a segment whose body, at a whole parameter, lays out as the template evaluated there
dleaf-Agree : ∀ (c : SegBody ℕ) tr (T′ : Dia (DExpr ⊤)) i t₀ →
  (∀ r → layoutℕ (bodyAt natOps c r) ≡ layoutℕ (mapDia (evalD natD (λ _ → units r)) T′)) →
  Agree (DLeafGood (dleaf i t₀ tr T′)) t₀ (frames natOps (seg tr c))
        (replicate (T.dur tr) (dinstantiate (dleaf i t₀ tr T′)))
dleaf-Agree c tr T′ i t₀ body-ok = agree go
  where
  l = dleaf i t₀ tr T′
  go : ∀ j → Rel (DLeafGood l (t₀ + j)) (nth (frames natOps (seg tr c)) j)
                                         (nth (replicate (T.dur tr) (dinstantiate l)) j)
  go j rewrite nth-frames natOps (seg tr c) j
             | nth-replicate (T.dur tr) (dinstantiate l) j
             | T.sample-dur T.ℚLerp tr
    with j <ᵇ T.dur tr in eq
  ... | false = noFrame
  ... | true  = bothFrames λ ρ g →
    let q = proj₂ (T.sample T.ℚLerp tr) j
        idx≡ : units q ≡ ρ i
        idx≡ = sym (g j eq refl)
    in trans (body-ok q)
      (trans (cong (λ r → layoutℕ (mapDia (evalD natD (λ _ → r)) T′)) idx≡)
      (trans (sym (dleaf-agrees l ρ))
             (sym (layout-evalD natD ρ (dinstantiate l)))))

private
  bind-just : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {y} → (m Maybe.>>= f) ≡ just y →
              ∃ λ x → m ≡ just x × f x ≡ just y
  bind-just (just x) f eq = x , refl , eq
  bind-just nothing  f ()

------------------------------------------------------------------------
-- The whole animation

dleaves-agree : ∀ (a : Anim ℕ (Seg ℕ)) i t₀ i′ l → dleaves i t₀ a ≡ just (i′ , l) →
                Agree (DGoodL l) t₀ (timeline atop (frames natOps) a) (dsymbolicFrames l)
dleaves-agree (pure (seg tr (template d))) i t₀ _ _ refl =
  dleaf-Agree (template d) tr (mapDia weakenE d) i t₀
    (λ r → sym (layout-weakenE natD (λ _ → units r) d))
dleaves-agree (pure (seg tr (discrete d))) i t₀ _ _ refl =
  dleaf-Agree (discrete d) tr d i t₀ (λ r → refl)
dleaves-agree (pure (seg tr (blackBox f))) i t₀ _ _ ()
dleaves-agree (impure (Seq , k)) i t₀ i′ l eq with bind-just (dleaves i t₀ (k zero)) _ eq
... | (i₁ , a′) , e₁ , r₁ with bind-just (dleaves i₁ _ (k (suc zero))) _ r₁
... | (i₂ , b′) , e₂ , refl =
  Agree-++ (dleaves-agree (k zero) i t₀ i₁ a′ e₁)
           (Agree-≡ (cong (t₀ +_) (sym (length-dur natOps (k zero))))
                    (dleaves-agree (k (suc zero)) i₁ (t₀ + dur (k zero)) i₂ b′ e₂))
dleaves-agree (impure (Par , k)) i t₀ i′ l eq with bind-just (dleaves i t₀ (k zero)) _ eq
... | (i₁ , a′) , e₁ , r₁ with bind-just (dleaves i₁ _ (k (suc zero))) _ r₁
... | (i₂ , b′) , e₂ , refl =
  Agree-merge (dleaves-agree (k zero) i t₀ i₁ a′ e₁) (dleaves-agree (k (suc zero)) i₁ t₀ i₂ b′ e₂)

------------------------------------------------------------------------
-- Tick by tick

-- Statement.  For an animation of discrete (or continuous) templates, at every tick `k < dur a`
-- the frame of `timeline atop (frames natOps) a` is the layout of the symbolic frame evaluated
-- in ℕ at any assignment `ρ` that gives each leaf running at `k` the (floored) parameter of its
-- track at that tick.
discrete-assemblyD :
  ∀ (a : Anim ℕ (Seg ℕ)) i′ l → dleaves 0 0 a ≡ just (i′ , l) → ∀ k → (k <ᵇ dur a) ≡ true →
  ∀ ρ → DGoodL l k ρ →
  ∃₂ λ F S → nth (timeline atop (frames natOps) a) k ≡ just F
           × nth (dsymbolicFrames l) k ≡ just S
           × layoutℕ F ≡ mapLayout (evalD natD ρ) (layoutD S)
discrete-assemblyD a i′ l eq k hk ρ g with nth-in (timeline atop (frames natOps) a) k
                                             (subst (λ n → (k <ᵇ n) ≡ true) (sym (length-dur natOps a)) hk)
... | F , eF with Rel-just (subst (λ m → Rel (DGoodL l k) m (nth (dsymbolicFrames l) k)) eF
                                  (at (dleaves-agree a 0 0 i′ l eq) k))
... | S , eS , r = F , S , eF , eS , r ρ g
