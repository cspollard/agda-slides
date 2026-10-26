{-# OPTIONS --safe --without-K #-}

-- The assembly of whole frames, for any language of template numbers: the symbolic frames of an
-- animation are its frames.  Continuous templates (`Slides.Anim.Param.Properties`, `Expr`) and
-- discrete ones (`Slides.Anim.DParam.Properties`, `DExpr`) are instances; what they supply is
--
--   * how a symbolic frame is interpreted at an assignment (`interp`: lay it out symbolically,
--     evaluate at `ρ`), with `atop` interpreted as `atop` (`interp-atop`, layout is natural
--     along evaluation: `Slides.Diagram.Layout.Properties.atop-natural`);
--   * for one leaf, that the renamed template interpreted at `ρ` is the template laid out at the
--     leaf's own parameter `ρ idx` (`inst-agrees`), and that the segment's body at a whole
--     parameter is the template there (`body-ok`);
--   * how a segment is made a leaf (`leafOf`), numbered by its place (`leafOf-idx`).
--
-- Statement.  Let `a` be an animation whose segments all become leaves (`leavesWith leafOf 0 0 a
-- ≡ just (i′ , l)`): `l` is the same animation with each segment replaced by a `Leaf` (its
-- variable `idx`, its start tick, its track, its template).  For every tick `k < dur a`
--
--     layout_ℕ (frame k of  timeline atop (frames natOps) a)  ≡  interp (symbolic frame k) ρ
--
-- for every assignment `ρ` such that, for every leaf running at tick `k` (`start + m ≡ k`,
-- `m < dur track`), `ρ idx ≡ units (sample of its track at m)` (`GoodL l k ρ`).
--
--   * `assembly`: the statement, tick by tick.
--   * `leaves-agree`: the same for all ticks at once, as `Agree`, a relation between the list of
--     frames and the list of symbolic frames, which is what the induction carries.
--   * `assembly-canonical`: with the assignment named (`assignAt`: variable `j` is the floored
--     parameter of the leaf numbered `j`, 0 when it is not running).
--   * `segmentsOf-nth`: the shipped segments are the leaves, in order of their variable.
--
-- The hypothesis `GoodL l k ρ` is *only* about the leaves running at tick `k`: segments that are
-- not running at `k` do not occur in the frame.  It is satisfiable (the leaves are numbered apart:
-- `leaves-numbered`, `canonical-good`); it is a hypothesis on `ρ`, not on the animation.
--
-- The proof is the induction the module header of `Slides.Anim.Param` promised.  Lists of frames
-- are read as partial functions of the tick (`Slides.Anim.Nth`): `++` is "first, then the second
-- with the tick shifted" and `merge` the pointwise `mergeM`, the same algebra the continuous
-- semantics uses (`Slides.Anim.Continuous.parAt`); that part is `Slides.Anim.Assembly`.

module Slides.Anim.Assembly.Leaf where

open import Data.Bool using (true; false; if_then_else_; _∧_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; _++_; length; replicate; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_; _≤_)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
import Data.List.Properties as LP
open import Data.Unit using (⊤; tt)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary using (yes; no)
open import Data.Fin using (zero; suc)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)

open import Slides.Diagram.Draw using (Layout)
open import Slides.Diagram.Syntax using (Dia; atop)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (natOps)
import Slides.Diagram.Place natOps as PN
import Slides.Anim.Track as T
import Slides.Anim.Track.Properties as TP
open import Slides.Anim.Syntax
open import Slides.Anim.Timeline using (timeline; frames; length-dur)
open import Slides.Anim.Param using (Leaf; leaf; leavesWith; symbolicFramesWith; segmentsOf; pieces)
open import Slides.Anim.Nth
open import Slides.Anim.Arith
import Slides.Anim.Assembly as Asm

private
  layoutℕ : Dia ℕ → Layout ℕ
  layoutℕ = LayoutWith.layout natOps

module Over
  (E : Set → Set)
  (interp : Dia (E ℕ) → (ℕ → ℕ) → Layout ℕ)
  (interp-atop : ∀ x y ρ → PN.atop (interp x ρ) (interp y ρ) ≡ interp (atop x y) ρ)
  -- a template at a constant parameter
  (evalAt : ℕ → Dia (E ⊤) → Dia ℕ)
  -- a leaf's template with its variable renamed to its own
  (inst : Leaf E → Dia (E ℕ))
  (inst-agrees : ∀ l ρ → interp (inst l) ρ ≡ layoutℕ (evalAt (ρ (Leaf.idx l)) (Leaf.tmpl l)))
  where

  open Asm.Over (Dia (E ℕ)) interp atop interp-atop public

  ------------------------------------------------------------------------
  -- One segment

  -- `ρ` gives the leaf's variable the parameter its track has at the tick `m` that falls on `k`
  LeafGood : Leaf E → ℕ → (ℕ → ℕ) → Set
  LeafGood l k ρ = ∀ m → (m <ᵇ T.dur (Leaf.track l)) ≡ true → Leaf.start l + m ≡ k →
                   ρ (Leaf.idx l) ≡ units (proj₂ (T.sample T.ℚLerp (Leaf.track l)) m)

  -- the leaves of a tree, each with its own condition: the assignments for the tick `k` that
  -- agree with the parameter of every leaf running at `k` (and say nothing of the others)
  GoodL : AnimC ⋆ Leaf E → ℕ → (ℕ → ℕ) → Set
  GoodL (pure l)           k ρ = LeafGood l k ρ
  GoodL (impure (_ , c))   k ρ = GoodL (c zero) k ρ × GoodL (c (suc zero)) k ρ

  -- a segment whose body, at a whole parameter, lays out as the template evaluated there
  leaf-Agree : ∀ (c : SegBody ℕ) i t₀ tr (tmpl : Dia (E ⊤)) →
    (∀ q → layoutℕ (bodyAt natOps c q) ≡ layoutℕ (evalAt (units q) tmpl)) →
    Agree (LeafGood (leaf i t₀ tr tmpl)) t₀ (frames natOps (seg tr c))
          (replicate (T.dur tr) (inst (leaf i t₀ tr tmpl)))
  leaf-Agree c i t₀ tr tmpl body-ok = agree go
    where
    l = leaf i t₀ tr tmpl
    go : ∀ j → Rel (LeafGood l (t₀ + j)) (nth (frames natOps (seg tr c)) j)
                                           (nth (replicate (T.dur tr) (inst l)) j)
    go j rewrite nth-frames natOps (seg tr c) j
               | nth-replicate (T.dur tr) (inst l) j
               | TP.sample-dur T.ℚLerp tr
      with j <ᵇ T.dur tr in eq
    ... | false = noFrame
    ... | true  = bothFrames λ ρ g →
      let q = proj₂ (T.sample T.ℚLerp tr) j
          idx≡ : units q ≡ ρ i
          idx≡ = sym (g j eq refl)
      in trans (body-ok q)
        (trans (cong (λ r → layoutℕ (evalAt r tmpl)) idx≡)
               (sym (inst-agrees l ρ)))

  module Induction
    (leafOf : ℕ → ℕ → Seg ℕ → Maybe (Leaf E))
    (leafOf-idx : ∀ i t₀ s l → leafOf i t₀ s ≡ just l → Leaf.idx l ≡ i)
    (leaf-agree : ∀ i t₀ s l → leafOf i t₀ s ≡ just l →
                  Agree (LeafGood l) t₀ (frames natOps s) (replicate (T.dur (Leaf.track l)) (inst l)))
    where

    ------------------------------------------------------------------------
    -- The whole animation

    -- The whole animation: the frames agree with the symbolic frames at every tick.
    leaves-agree : ∀ (a : Anim ℕ (Seg ℕ)) i t₀ i′ l → leavesWith leafOf i t₀ a ≡ just (i′ , l) →
                   Agree (GoodL l) t₀ (timeline atop (frames natOps) a) (symbolicFramesWith inst l)
    leaves-agree (pure s) i t₀ i′ l eq with leafOf i t₀ s in e
    leaves-agree (pure s) i t₀ _ _ refl | just l′ = leaf-agree i t₀ s l′ e
    leaves-agree (pure s) i t₀ i′ l ()   | nothing
    leaves-agree (impure (Seq , k)) i t₀ i′ l eq with bind-just (leavesWith leafOf i t₀ (k zero)) _ eq
    ... | (i₁ , a′) , e₁ , r₁ with bind-just (leavesWith leafOf i₁ _ (k (suc zero))) _ r₁
    ... | (i₂ , b′) , e₂ , refl =
      Agree-++ (leaves-agree (k zero) i t₀ i₁ a′ e₁)
               (Agree-≡ (cong (t₀ +_) (sym (length-dur natOps (k zero))))
                        (leaves-agree (k (suc zero)) i₁ (t₀ + dur (k zero)) i₂ b′ e₂))
    leaves-agree (impure (Par , k)) i t₀ i′ l eq with bind-just (leavesWith leafOf i t₀ (k zero)) _ eq
    ... | (i₁ , a′) , e₁ , r₁ with bind-just (leavesWith leafOf i₁ _ (k (suc zero))) _ r₁
    ... | (i₂ , b′) , e₂ , refl =
      Agree-merge (leaves-agree (k zero) i t₀ i₁ a′ e₁) (leaves-agree (k (suc zero)) i₁ t₀ i₂ b′ e₂)

    -- Statement.  At every tick `k < dur a` the frame of `timeline atop (frames natOps) a` is the
    -- interpretation of the symbolic frame at any assignment `ρ` that gives each leaf running at `k`
    -- the (floored) parameter of its track at that tick (`GoodL l k ρ`).
    assembly :
      ∀ (a : Anim ℕ (Seg ℕ)) i′ l → leavesWith leafOf 0 0 a ≡ just (i′ , l) → ∀ k → (k <ᵇ dur a) ≡ true →
      ∀ ρ → GoodL l k ρ →
      ∃₂ λ F S → nth (timeline atop (frames natOps) a) k ≡ just F
               × nth (symbolicFramesWith inst l) k ≡ just S
               × layoutℕ F ≡ interp S ρ
    assembly a i′ l eq k hk ρ g with nth-in (timeline atop (frames natOps) a) k
                                           (subst (λ n → (k <ᵇ n) ≡ true) (sym (length-dur natOps a)) hk)
    ... | F , eF with Rel-just (subst (λ m → Rel (GoodL l k) m (nth (symbolicFramesWith inst l) k)) eF
                                      (at (leaves-agree a 0 0 i′ l eq) k))
    ... | S , eS , r = F , S , eF , eS , r ρ g

    ------------------------------------------------------------------------
    -- The assignment `i ↦ (parameter of segment i at tick k)`
    --
    -- `GoodL` says what an assignment must do; this is one that does it.  The leaves of `leaves`
    -- are numbered apart (`numbered`: the variables of a tree lie in `[i, i′)`, a `Seq` or `Par`
    -- splitting the range at `i₁`), and `assignAt` gives variable `j` the floored parameter of the
    -- leaf numbered `j` at tick `k` if that leaf is running, and 0 otherwise.

    numbered : ℕ → ℕ → AnimC ⋆ Leaf E → Set
    numbered i i′ (pure l)           = Leaf.idx l ≡ i × i′ ≡ suc i
    numbered i i′ (impure (_ , c)) = ∃ λ i₁ → numbered i i₁ (c zero) × numbered i₁ i′ (c (suc zero))

    leaves-numbered : ∀ (a : Anim ℕ (Seg ℕ)) i t₀ i′ l → leavesWith leafOf i t₀ a ≡ just (i′ , l) → numbered i i′ l
    leaves-numbered (pure s) i t₀ i′ l eq with leafOf i t₀ s in e
    leaves-numbered (pure s) i t₀ _ _ refl | just l′ = leafOf-idx i t₀ s l′ e , refl
    leaves-numbered (pure s) i t₀ i′ l ()   | nothing
    leaves-numbered (impure (Seq , k)) i t₀ i′ l eq with bind-just (leavesWith leafOf i t₀ (k zero)) _ eq
    ... | (i₁ , a′) , e₁ , r₁ with bind-just (leavesWith leafOf i₁ _ (k (suc zero))) _ r₁
    ... | (i₂ , b′) , e₂ , refl = i₁ , leaves-numbered (k zero) i t₀ i₁ a′ e₁ , leaves-numbered (k (suc zero)) i₁ _ i₂ b′ e₂
    leaves-numbered (impure (Par , k)) i t₀ i′ l eq with bind-just (leavesWith leafOf i t₀ (k zero)) _ eq
    ... | (i₁ , a′) , e₁ , r₁ with bind-just (leavesWith leafOf i₁ _ (k (suc zero))) _ r₁
    ... | (i₂ , b′) , e₂ , refl = i₁ , leaves-numbered (k zero) i t₀ i₁ a′ e₁ , leaves-numbered (k (suc zero)) i₁ t₀ i₂ b′ e₂

    numbered-≤ : ∀ t i i′ → numbered i i′ t → i ≤ i′
    numbered-≤ (pure l)           i i′ (refl , refl) = ℕP.n≤1+n i
    numbered-≤ (impure (Seq , c)) i i′ (i₁ , n₁ , n₂) = ℕP.≤-trans (numbered-≤ (c zero) i i₁ n₁) (numbered-≤ (c (suc zero)) i₁ i′ n₂)
    numbered-≤ (impure (Par , c)) i i′ (i₁ , n₁ , n₂) = ℕP.≤-trans (numbered-≤ (c zero) i i₁ n₁) (numbered-≤ (c (suc zero)) i₁ i′ n₂)

    -- the parameter of a leaf at tick `k` if it is running there
    activeVal : Leaf E → ℕ → ℕ
    activeVal l k =
      if (Leaf.start l ℕ.≤ᵇ k) ∧ (k <ᵇ Leaf.start l + T.dur (Leaf.track l))
      then units (proj₂ (T.sample T.ℚLerp (Leaf.track l)) (k ∸ Leaf.start l)) else 0

    assignAt : AnimC ⋆ Leaf E → ℕ → ℕ → ℕ
    assignAt (pure l)           k j = if ⌊ j ℕP.≟ Leaf.idx l ⌋ then activeVal l k else 0
    assignAt (impure (_ , c)) k j = assignAt (c zero) k j + assignAt (c (suc zero)) k j

    private
      true≢false : true ≡ false → ⊥
      true≢false ()

      <ᵇ-irrefl : ∀ i → (i <ᵇ i) ≡ false
      <ᵇ-irrefl zero    = refl
      <ᵇ-irrefl (suc i) = <ᵇ-irrefl i

      ⌊≟⌋-diag : ∀ i → ⌊ i ℕP.≟ i ⌋ ≡ true
      ⌊≟⌋-diag i rewrite ℕP.≟-diag {i} {i} refl = refl

    activeVal-on : ∀ l m → (m <ᵇ T.dur (Leaf.track l)) ≡ true →
                   activeVal l (Leaf.start l + m) ≡ units (proj₂ (T.sample T.ℚLerp (Leaf.track l)) m)
    activeVal-on l m h =
      trans (cong (λ b → if b then units (proj₂ (T.sample T.ℚLerp (Leaf.track l)) (Leaf.start l + m ∸ Leaf.start l)) else 0)
                  (cong₂ _∧_ (≤ᵇ-true (ℕP.m≤m+n (Leaf.start l) m))
                             (<ᵇ-true (ℕP.+-monoʳ-< (Leaf.start l) (<ᵇ-lt h)))))
            (cong (λ x → units (proj₂ (T.sample T.ℚLerp (Leaf.track l)) x)) (ℕP.m+n∸m≡n (Leaf.start l) m))

    assignAt-out : ∀ t i i′ → numbered i i′ t → ∀ k j → ((j <ᵇ i) ≡ true) ⊎ (i′ ≤ j) → assignAt t k j ≡ 0
    assignAt-out (pure l) i i′ (refl , refl) k j out with j ℕP.≟ Leaf.idx l
    ... | no  _    = refl
    ... | yes refl with out
    ...   | inj₁ h = ⊥-elim (true≢false (trans (sym h) (<ᵇ-irrefl (Leaf.idx l))))
    ...   | inj₂ h = ⊥-elim (ℕP.1+n≰n h)
    assignAt-out (impure (Seq , c)) i i′ (i₁ , n₁ , n₂) k j out =
      cong₂ _+_ (assignAt-out (c zero) i i₁ n₁ k j (outˡ n₂ out))
                (assignAt-out (c (suc zero)) i₁ i′ n₂ k j (outʳ n₁ out))
      where
        outˡ : numbered i₁ i′ (c (suc zero)) → _ → _
        outˡ n₂ (inj₁ h) = inj₁ h
        outˡ n₂ (inj₂ h) = inj₂ (ℕP.≤-trans (numbered-≤ _ i₁ i′ n₂) h)
        outʳ : numbered i i₁ (c zero) → _ → _
        outʳ n₁ (inj₁ h) = inj₁ (<ᵇ-true (ℕP.<-≤-trans (<ᵇ-lt h) (numbered-≤ _ i i₁ n₁)))
        outʳ n₁ (inj₂ h) = inj₂ h
    assignAt-out (impure (Par , c)) i i′ (i₁ , n₁ , n₂) k j out =
      cong₂ _+_ (assignAt-out (c zero) i i₁ n₁ k j (outˡ n₂ out))
                (assignAt-out (c (suc zero)) i₁ i′ n₂ k j (outʳ n₁ out))
      where
        outˡ : numbered i₁ i′ (c (suc zero)) → _ → _
        outˡ n₂ (inj₁ h) = inj₁ h
        outˡ n₂ (inj₂ h) = inj₂ (ℕP.≤-trans (numbered-≤ _ i₁ i′ n₂) h)
        outʳ : numbered i i₁ (c zero) → _ → _
        outʳ n₁ (inj₁ h) = inj₁ (<ᵇ-true (ℕP.<-≤-trans (<ᵇ-lt h) (numbered-≤ _ i i₁ n₁)))
        outʳ n₁ (inj₂ h) = inj₂ h

    -- `assignAt` is good, and so is anything that agrees with it on the variables of the tree
    canonical-good : ∀ t i i′ → numbered i i′ t → ∀ k ρ →
                     (∀ j → i ≤ j → j ℕ.< i′ → ρ j ≡ assignAt t k j) → GoodL t k ρ
    canonical-good (pure l) i i′ (refl , refl) k ρ h m hm refl =
      trans (h (Leaf.idx l) ℕP.≤-refl (ℕP.n<1+n (Leaf.idx l)))
            (trans (cong (λ b → if b then activeVal l (Leaf.start l + m) else 0) (⌊≟⌋-diag (Leaf.idx l)))
                   (activeVal-on l m hm))
    canonical-good (impure (_ , c)) i i′ (i₁ , n₁ , n₂) k ρ h =
      canonical-good (c zero) i i₁ n₁ k ρ
        (λ j lo hi → trans (h j lo (ℕP.<-≤-trans hi (numbered-≤ _ i₁ i′ n₂)))
                           (trans (cong (assignAt (c zero) k j +_) (assignAt-out _ i₁ i′ n₂ k j (inj₁ (<ᵇ-true hi))))
                                  (ℕP.+-identityʳ _)))
      , canonical-good (c (suc zero)) i₁ i′ n₂ k ρ
        (λ j lo hi → trans (h j (ℕP.≤-trans (numbered-≤ _ i i₁ n₁) lo) hi)
                           (cong (_+ assignAt (c (suc zero)) k j) (assignAt-out _ i i₁ n₁ k j (inj₂ lo))))

    -- Statement, with the assignment named: variable `j` is the floored parameter, at tick `k`, of
    -- the segment numbered `j` (0 when it is not running).  No hypothesis beyond `a` being made of
    -- leaves.
    assembly-canonical :
      ∀ (a : Anim ℕ (Seg ℕ)) i′ l → leavesWith leafOf 0 0 a ≡ just (i′ , l) → ∀ k → (k <ᵇ dur a) ≡ true →
      ∃₂ λ F S → nth (timeline atop (frames natOps) a) k ≡ just F
               × nth (symbolicFramesWith inst l) k ≡ just S
               × layoutℕ F ≡ interp S (assignAt l k)
    assembly-canonical a i′ l eq k hk =
      assembly a i′ l eq k hk (assignAt l k)
        (canonical-good l 0 i′ (leaves-numbered a 0 0 i′ l eq) k (assignAt l k) (λ j _ _ → refl))

    ------------------------------------------------------------------------
    -- The shipped segments are the leaves, in order of their variable

    -- `lf` is a leaf of the tree
    InTree : Leaf E → AnimC ⋆ Leaf E → Set
    InTree lf (pure l)           = lf ≡ l
    InTree lf (impure (_ , c)) = InTree lf (c zero) ⊎ InTree lf (c (suc zero))

    InTree-range : ∀ t i i′ lf → numbered i i′ t → InTree lf t → i ≤ Leaf.idx lf × Leaf.idx lf ℕ.< i′
    InTree-range (pure l) i i′ lf (refl , refl) refl = ℕP.≤-refl , ℕP.n<1+n _
    InTree-range (impure (Seq , c)) i i′ lf (i₁ , n₁ , n₂) (inj₁ h) with InTree-range (c zero) i i₁ lf n₁ h
    ... | lo , hi = lo , ℕP.<-≤-trans hi (numbered-≤ _ i₁ i′ n₂)
    InTree-range (impure (Seq , c)) i i′ lf (i₁ , n₁ , n₂) (inj₂ h) with InTree-range (c (suc zero)) i₁ i′ lf n₂ h
    ... | lo , hi = ℕP.≤-trans (numbered-≤ _ i i₁ n₁) lo , hi
    InTree-range (impure (Par , c)) i i′ lf (i₁ , n₁ , n₂) (inj₁ h) with InTree-range (c zero) i i₁ lf n₁ h
    ... | lo , hi = lo , ℕP.<-≤-trans hi (numbered-≤ _ i₁ i′ n₂)
    InTree-range (impure (Par , c)) i i′ lf (i₁ , n₁ , n₂) (inj₂ h) with InTree-range (c (suc zero)) i₁ i′ lf n₂ h
    ... | lo , hi = ℕP.≤-trans (numbered-≤ _ i i₁ n₁) lo , hi

    length-segmentsOf : ∀ t i i′ → numbered i i′ t → i + length (segmentsOf t) ≡ i′
    length-segmentsOf (pure l) i i′ (refl , refl) = ℕP.+-comm i 1
    length-segmentsOf (impure (Seq , c)) i i′ (i₁ , n₁ , n₂) =
      trans (cong (i +_) (LP.length-++ (segmentsOf (c zero))))
      (trans (sym (ℕP.+-assoc i (length (segmentsOf (c zero))) (length (segmentsOf (c (suc zero))))))
      (trans (cong (_+ length (segmentsOf (c (suc zero)))) (length-segmentsOf (c zero) i i₁ n₁))
             (length-segmentsOf (c (suc zero)) i₁ i′ n₂)))
    length-segmentsOf (impure (Par , c)) i i′ (i₁ , n₁ , n₂) =
      trans (cong (i +_) (LP.length-++ (segmentsOf (c zero))))
      (trans (sym (ℕP.+-assoc i (length (segmentsOf (c zero))) (length (segmentsOf (c (suc zero))))))
      (trans (cong (_+ length (segmentsOf (c (suc zero)))) (length-segmentsOf (c zero) i i₁ n₁))
             (length-segmentsOf (c (suc zero)) i₁ i′ n₂)))

    private
      lt-or-ge : ∀ x y → x ℕ.< y ⊎ y ≤ x
      lt-or-ge x y with ℕP.<-cmp x y
      ... | tri< a _ _ = inj₁ a
      ... | tri≈ _ b _ = inj₂ (ℕP.≤-reflexive (sym b))
      ... | tri> _ _ c = inj₂ (ℕP.<⇒≤ c)

      -- reading the `d`-th element of `xs ++ ys` when `xs` and `ys` cover consecutive ranges of
      -- positions `[i, i₁)`, `[i₁, …)`
      nth-join : ∀ {A : Set} (xs ys : List A) i i₁ x (r : A) d → i + length xs ≡ i₁ → i + d ≡ x →
                 (x ℕ.< i₁ → nth xs d ≡ just r) →
                 (i₁ ≤ x → ∀ d′ → i₁ + d′ ≡ x → nth ys d′ ≡ just r) →
                 nth (xs ++ ys) d ≡ just r
      nth-join xs ys i i₁ x r d len e h₁ h₂ with lt-or-ge x i₁
      ... | inj₁ lt = trans (trans (nth-++ xs ys d) (cong (λ b → if b then nth xs d else nth ys (d ∸ length xs)) d<))
                            (h₁ lt)
        where d< = <ᵇ-true (ℕP.+-cancelˡ-< i d (length xs) (subst₂ ℕ._<_ (sym e) (sym len) lt))
      ... | inj₂ ge = trans (trans (nth-++ xs ys d) (cong (λ b → if b then nth xs d else nth ys (d ∸ length xs)) d≮))
                            (h₂ ge (d ∸ length xs) off)
        where d≥ : length xs ≤ d
              d≥ = ℕP.+-cancelˡ-≤ i _ d (subst₂ ℕ._≤_ (sym len) (sym e) ge)
              d≮ = <ᵇ-false d≥
              off = trans (cong (_+ (d ∸ length xs)) (sym len))
                     (trans (ℕP.+-assoc i (length xs) (d ∸ length xs))
                     (trans (cong (i +_) (ℕP.m+[n∸m]≡n d≥)) e))

    -- the `d`-th shipped segment, counting from the first variable `i`, is the leaf numbered `i + d`
    segmentsOf-nth : ∀ t i i′ lf → numbered i i′ t → InTree lf t → ∀ d → i + d ≡ Leaf.idx lf →
                     nth (segmentsOf t) d ≡ just (Leaf.start lf , pieces (Leaf.track lf))
    segmentsOf-nth (pure l) i i′ lf (refl , refl) refl d h
      with ℕP.+-cancelˡ-≡ (Leaf.idx l) d 0 (trans h (sym (ℕP.+-identityʳ _)))
    ... | refl = refl
    segmentsOf-nth (impure (Seq , c)) i i′ lf (i₁ , n₁ , n₂) (inj₁ h) d e =
      nth-join (segmentsOf (c zero)) (segmentsOf (c (suc zero))) i i₁ (Leaf.idx lf) _ d
        (length-segmentsOf (c zero) i i₁ n₁) e
        (λ _ → segmentsOf-nth (c zero) i i₁ lf n₁ h d e)
        (λ ge → ⊥-elim (ℕP.<⇒≱ (proj₂ (InTree-range (c zero) i i₁ lf n₁ h)) ge))
    segmentsOf-nth (impure (Seq , c)) i i′ lf (i₁ , n₁ , n₂) (inj₂ h) d e =
      nth-join (segmentsOf (c zero)) (segmentsOf (c (suc zero))) i i₁ (Leaf.idx lf) _ d
        (length-segmentsOf (c zero) i i₁ n₁) e
        (λ lt → ⊥-elim (ℕP.<⇒≱ lt (proj₁ (InTree-range (c (suc zero)) i₁ i′ lf n₂ h))))
        (λ _ d′ e′ → segmentsOf-nth (c (suc zero)) i₁ i′ lf n₂ h d′ e′)
    segmentsOf-nth (impure (Par , c)) i i′ lf (i₁ , n₁ , n₂) (inj₁ h) d e =
      nth-join (segmentsOf (c zero)) (segmentsOf (c (suc zero))) i i₁ (Leaf.idx lf) _ d
        (length-segmentsOf (c zero) i i₁ n₁) e
        (λ _ → segmentsOf-nth (c zero) i i₁ lf n₁ h d e)
        (λ ge → ⊥-elim (ℕP.<⇒≱ (proj₂ (InTree-range (c zero) i i₁ lf n₁ h)) ge))
    segmentsOf-nth (impure (Par , c)) i i′ lf (i₁ , n₁ , n₂) (inj₂ h) d e =
      nth-join (segmentsOf (c zero)) (segmentsOf (c (suc zero))) i i₁ (Leaf.idx lf) _ d
        (length-segmentsOf (c zero) i i₁ n₁) e
        (λ lt → ⊥-elim (ℕP.<⇒≱ lt (proj₁ (InTree-range (c (suc zero)) i₁ i′ lf n₂ h))))
        (λ _ d′ e′ → segmentsOf-nth (c (suc zero)) i₁ i′ lf n₂ h d′ e′)
