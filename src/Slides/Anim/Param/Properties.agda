{-# OPTIONS --safe --without-K #-}

-- The assembly of whole frames: the symbolic frames of `Slides.Anim.Param` are the frames of the
-- animation (the discrete frames, `layout_ℕ`, of `timeline a`).  The proof is the assembly calculus
-- (`Slides.Anim.Assembly.Calculus`) at the clocks ℕ and ℕ: the animation and its symbolic scene
-- (`place`) are the same temporal skeleton read two ways, so the induction has one case per
-- connective, and what is specific to this instance is one segment (`leaf-agrees`).
--
--     layout_ℕ (frame k of  timeline a)  ≡  mapLayout (evalO natO ρ) (layout (symbolic frame k))
--
-- for every tick `k < dur a` of an animation `a` that has a parametric encoding (`place 0 0 a`) and
-- every assignment `ρ` such that every leaf running at tick `k` has `ρ (idx) ≡ units (sample of its
-- track at that tick)` (`GoodL ls k ρ`).  The right-hand side is exactly what the page computes
-- (evaluate the symbolic layout at the parameters), and the left is the existing discrete frame.
--
--   * `discrete-assembly` (`assembly`): the statement, tick by tick; `assembly-canonical` with the
--     assignment named (`assignAt`: variable `j` is the floored parameter of the leaf numbered `j`).
--   * `paramOf-assembly`: for the animation `render` ships (`paramOf acts`), against the frames
--     `render` shows (`concat (map timeline acts)`).
--
-- `GoodL` is *only* about the leaves running at tick `k`: segments that are not running at `k` do not
-- occur in the frame.  It is satisfiable (the leaves are numbered apart: `place-numbered`,
-- `canonical-good`); it is a hypothesis on `ρ`, not on the animation.

module Slides.Anim.Param.Properties where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; map; concat)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as AllP
import Data.List.Relation.Unary.All as AllH
import Data.List.Properties as LP
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ; _+_; _∸_; _<ᵇ_; _≤_)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Fin using (zero; suc)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Slides.Diagram.Draw using (Layout; mapLayout)
open import Slides.Diagram.Syntax using (Dia; atop; mapDia; spacer)
open import Slides.Diagram.Ordered using (OExpr; evalO; natO; substO; termOps; zero′)
open import Slides.Diagram.Ordered.Properties.Laws using (evalO-hom; layout-evalO; layout-substO)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (natOps)
open import Slides.Diagram.Layout.Properties using (atop-natural)
import Slides.Anim.Track as Tr
open import Slides.Time using (mergeM)
open import Slides.Time.Nat using (natClock)
open import Slides.Time.Properties using (natLaws)
open import Slides.Anim.Syntax
open import Slides.Anim.Sample
open import Slides.Anim.Sample.Properties using (sample-dur; frames-dur)
open import Slides.Anim.Timeline using (timeline; framesN; natVal; tabulate)
open import Slides.Anim.Timeline.Properties using (length-dur; timeline-⨾)
open import Slides.Anim.Param
import Slides.Diagram.Param as DP
open import Slides.Anim.Nth public
open import Slides.Anim.Arith using (<ᵇ-true; <ᵇ-lt; <ᵇ-false; ≤ᵇ-true)
open import Slides.Anim.Assembly

private
  layoutℕ : Dia ℕ → Layout ℕ
  layoutℕ = LayoutWith.layout natOps

  layoutE : Dia (OExpr ℕ) → Layout (OExpr ℕ)
  layoutE = LayoutWith.layout termOps

------------------------------------------------------------------------
-- One segment

-- Laying a segment's renamed template out symbolically and evaluating it at an assignment
-- is laying out the template at the segment's own parameter there.
leaf-agrees : ∀ (l : Leaf) (ρ : ℕ → ℕ) →
  LayoutWith.layout natOps (mapDia (evalO natO ρ) (instantiate l))
  ≡ LayoutWith.layout natOps (mapDia (evalO natO (λ _ → ρ (Leaf.idx l))) (Leaf.tmpl l))
leaf-agrees l ρ = layout-substO natO (λ _ → pure (Leaf.idx l)) ρ (Leaf.tmpl l)

-- the symbolic frames are over `OExpr`: a frame is interpreted by evaluating its layout, and
-- `atop` is interpreted as `atop` because layout is natural along evaluation
interp : Dia (OExpr ℕ) → (ℕ → ℕ) → Layout ℕ
interp y ρ = mapLayout (evalO natO ρ) (layoutE y)

open Over (Dia (OExpr ℕ)) interp atop
  (λ x y ρ → sym (atop-natural termOps natOps (evalO natO ρ) (evalO-hom natO ρ) (layoutE x) (layoutE y)))
open Calculus natClock natClock natLaws natLaws

-- `ρ` gives the leaf's variable the parameter its track has at the tick `m` that falls on `k`
LeafGood : Leaf → ℕ → (ℕ → ℕ) → Set
LeafGood l k ρ = ∀ m → (m <ᵇ Tr.dur (Leaf.track l)) ≡ true → Leaf.start l + m ≡ k →
                 ρ (Leaf.idx l) ≡ units (proj₂ (Tr.sample Tr.ℚLerp (Leaf.track l)) m)

-- every leaf has its own condition: the assignments for the tick `k` that agree with the parameter
-- of every leaf running at `k` (and say nothing of the others)
GoodL : List Leaf → ℕ → (ℕ → ℕ) → Set
GoodL ls k ρ = All (λ l → LeafGood l k ρ) ls

-- the relation of the calculus: the readers of the animation against the symbolic frames, the
-- tick `j` of a subanimation that starts at `t₀` being the tick `t₀ + j` of the whole
RS : List Leaf → ℕ → ℕ → Maybe (Rd natClock) → Maybe (Dia (OExpr ℕ)) → Set
RS ls t₀ j = Rel (GoodL ls (t₀ + j))

private
  seg-case : ∀ i t₀ tr d → RelN (RS (leaf i t₀ tr d ∷ []) t₀) (readA natClock natVal (seg tr d))
                                (symTM (symLeaf (leaf i t₀ tr d)))
  seg-case i t₀ tr d = refl , tick
    where
      l = leaf i t₀ tr d
      tick : ∀ k → RS (l ∷ []) t₀ k
               (if k <ᵇ Tr.dur tr then just (bndR natClock (natVal tr k) (λ p → inst natClock p d)) else nothing)
               (if k <ᵇ Tr.dur tr then just (instantiate l) else nothing)
      tick k with k <ᵇ Tr.dur tr in eq
      ... | false = noFrame
      ... | true  = bothFrames λ ρ gs →
        let g = AllH.head gs
            idx≡ : units (proj₂ (Tr.sample Tr.ℚLerp tr) k) ≡ ρ i
            idx≡ = sym (g k eq refl)
        in trans (cong (λ r → layoutℕ (mapDia (evalO natO (λ _ → r)) d)) idx≡)
           (trans (sym (leaf-agrees l ρ)) (sym (layout-evalO natO ρ (instantiate l))))

------------------------------------------------------------------------
-- Segments are recognised

private
  segDrive-inv : ∀ n tr₀ x {tr d} → segDrive n tr₀ x ≡ just (tr , d) → hold′ n (drive tr₀ x) ≡ seg tr d
  segDrive-inv n tr₀ (pure d₀) eq with n ℕP.≟ Tr.dur tr₀
  segDrive-inv n tr₀ (pure d₀) refl | yes refl = refl
  segDrive-inv n tr₀ (pure d₀) ()   | no _
  segDrive-inv n tr₀ (impure _) ()

  segHold-inv : ∀ n x {tr d} → segHold n x ≡ just (tr , d) → hold′ n x ≡ seg tr d
  segHold-inv n (pure _) ()
  segHold-inv n (impure (Seq , _)) ()
  segHold-inv n (impure (Par , _)) ()
  segHold-inv n (impure (Hold _ , _)) ()
  segHold-inv n (impure (Delay _ , _)) ()
  segHold-inv n (impure (Repeat _ , _)) ()
  segHold-inv n (impure (Drive tr₀ , j)) eq = segDrive-inv n tr₀ (j tt) eq

  segOf-inv : ∀ a {tr d} → segOf a ≡ just (tr , d) → a ≡ seg tr d
  segOf-inv (pure _) ()
  segOf-inv (impure (Seq , _)) ()
  segOf-inv (impure (Par , _)) ()
  segOf-inv (impure (Hold n , k)) eq = segHold-inv n (k tt) eq
  segOf-inv (impure (Delay _ , _)) ()
  segOf-inv (impure (Repeat _ , _)) ()
  segOf-inv (impure (Drive _ , _)) ()

  -- what `place` says of a segment
  place-seg : ∀ i t₀ a {tr d} → segOf a ≡ just (tr , d) →
              place i t₀ a ≡ just (ℕ.suc i , symLeaf (leaf i t₀ tr d) , leaf i t₀ tr d ∷ [])
  place-seg i t₀ a eq with segOf a
  place-seg i t₀ a refl | just _ = refl

  -- and of an animation that is not one
  place-seq : ∀ i t₀ k → place i t₀ (impure (Seq , k)) ≡
    (place i t₀ (k zero) Maybe.>>= λ { (i₁ , a₁ , l₁) →
     place i₁ (t₀ + dur (k zero)) (k (suc zero)) Maybe.>>= λ { (i₂ , a₂ , l₂) →
     just (i₂ , a₁ ⨾ a₂ , l₁ ++ l₂) } })
  place-seq i t₀ k = refl

  place-hold : ∀ i t₀ n k {r} → place i t₀ (impure (Hold n , k)) ≡ just r →
               ∃₂ λ tr d → segOf (impure (Hold n , k)) ≡ just (tr , d)
  place-hold i t₀ n k eq with segOf (impure (Hold n , k)) in eqs
  place-hold i t₀ n k eq | just (tr , d) = tr , d , refl
  place-hold i t₀ n k () | nothing

------------------------------------------------------------------------
-- The whole animation

private
  -- the first part of a `Seq` of the leaves, and the second shifted
  Good-++ˡ : ∀ {l₁ l₂ k ρ} → GoodL (l₁ ++ l₂) k ρ → GoodL l₁ k ρ
  Good-++ˡ {l₁} g = proj₁ (AllP.++⁻ l₁ g)

  Good-++ʳ : ∀ {l₁ l₂ k ρ} → GoodL (l₁ ++ l₂) k ρ → GoodL l₂ k ρ
  Good-++ʳ {l₁} g = proj₂ (AllP.++⁻ l₁ g)

  Good-≡ : ∀ {ls t t′ ρ} → t ≡ t′ → GoodL ls t ρ → GoodL ls t′ ρ
  Good-≡ refl g = g

induct : ∀ a i t₀ i′ s ls → place i t₀ a ≡ just (i′ , s , ls) →
         RelN (RS ls t₀) (readA natClock natVal a) (symTM s)
induct (pure _) i t₀ i′ s ls ()
induct (impure (Seq , k)) i t₀ i′ s ls eq with bind-just (place i t₀ (k zero)) _ eq
... | (i₁ , a₁ , l₁) , e₁ , r₁ with bind-just (place i₁ (t₀ + dur (k zero)) (k (suc zero))) _ r₁
... | (i₂ , a₂ , l₂) , e₂ , refl =
  relN-seq {R = RS (l₁ ++ l₂) t₀} (λ _ → noFrame)
    (relN-mono {R = RS l₁ t₀} {R′ = RS (l₁ ++ l₂) t₀} (λ j _ _ → Rel-⇒ (λ ρ g → Good-++ˡ {l₁} g)) (induct (k zero) i t₀ i₁ a₁ l₁ e₁))
    (relN-mono {R = RS l₂ (t₀ + dur (k zero))} {R′ = λ j → RS (l₁ ++ l₂) t₀ (proj₁ (readA natClock natVal (k zero)) + j)} (λ j _ _ → Rel-⇒ (λ ρ g → Good-++ʳ {l₁} (Good-≡ (shift j) g)))
               (induct (k (suc zero)) i₁ (t₀ + dur (k zero)) i₂ a₂ l₂ e₂))
  where
    shift : ∀ j → t₀ + (proj₁ (readA natClock natVal (k zero)) + j) ≡ (t₀ + dur (k zero)) + j
    shift j = trans (cong (λ n → t₀ + (n + j)) (sample-dur natClock _ _ natVal _ (k zero)))
                    (sym (ℕP.+-assoc t₀ (dur (k zero)) j))
induct (impure (Par , k)) i t₀ i′ s ls eq with bind-just (place i t₀ (k zero)) _ eq
... | (i₁ , a₁ , l₁) , e₁ , r₁ with bind-just (place i₁ t₀ (k (suc zero))) _ r₁
... | (i₂ , a₂ , l₂) , e₂ , refl =
  relN-par {R = RS (l₁ ++ l₂) t₀} {R₁ = RS l₁ t₀} {R₂ = RS l₂ t₀}
    (λ j _ _ _ _ r₁ r₂ → Rel-⇒ (λ ρ g → Good-++ˡ {l₁} g , Good-++ʳ {l₁} g) (Rel-mergeM r₁ r₂))
    (induct (k zero) i t₀ i₁ a₁ l₁ e₁) (induct (k (suc zero)) i₁ t₀ i₂ a₂ l₂ e₂)
induct (impure (Delay n , k)) i t₀ i′ s ls eq with place i (t₀ + n) (k tt) in e₁
induct (impure (Delay n , k)) i t₀ i′ s ls () | nothing
induct (impure (Delay n , k)) i t₀ i′ _ _ refl | just (i₁ , a₁ , l₁) =
  relN-delay {R = RS l₁ t₀} {x = readA natClock natVal (k tt)} {y = symTM a₁} {n = n} (λ _ → noFrame)
    (relN-mono {R = RS l₁ (t₀ + n)} {R′ = λ j → RS l₁ t₀ (n + j)} (λ j _ _ → Rel-⇒ (λ ρ g → Good-≡ (sym (ℕP.+-assoc t₀ n j)) g)) (induct (k tt) i (t₀ + n) i₁ a₁ l₁ e₁))
induct (impure (Repeat _ , _)) i t₀ i′ s ls ()
induct (impure (Drive _ , _)) i t₀ i′ s ls ()
induct (impure (Hold n , k)) i t₀ i′ s ls eq with place-hold i t₀ n k eq
... | tr , d , eqs with trans (sym (place-seg i t₀ (impure (Hold n , k)) eqs)) eq
... | refl = subst (λ x → RelN (RS (leaf i t₀ tr d ∷ []) t₀) (readA natClock natVal x) (symTM (symLeaf (leaf i t₀ tr d))))
                    (sym (segOf-inv (impure (Hold n , k)) eqs)) (seg-case i t₀ tr d)

------------------------------------------------------------------------
-- Statement (A): tick by tick

private
  ε : Dia ℕ
  ε = spacer 0 0

  εS : Dia (OExpr ℕ)
  εS = spacer zero′ zero′

  -- a tick at which nothing is shown on either side: the empty frame, which evaluates to itself
  tick-frames : ∀ {G} x y → Rel G x y → ∀ ρ → G ρ →
                layoutℕ (fromMaybe ε (Maybe.map (λ g → g 0) x)) ≡ interp (fromMaybe εS y) ρ
  tick-frames nothing  nothing  noFrame        ρ g = sym (layout-evalO natO ρ (spacer zero′ zero′))
  tick-frames (just _) (just _) (bothFrames r) ρ g = r ρ g

-- At every tick `k < dur a` the frame of `timeline a` is the interpretation of the symbolic frame at
-- any assignment `ρ` that gives each leaf running at `k` the (floored) parameter of its track at that
-- tick (`GoodL ls k ρ`).
assembly :
  ∀ a i′ s ls → place 0 0 a ≡ just (i′ , s , ls) → ∀ k → (k <ᵇ dur a) ≡ true →
  ∀ ρ → GoodL ls k ρ →
  ∃₂ λ F S → nth (timeline a) k ≡ just F
           × nth (symbolicFrames s) k ≡ just S
           × layoutℕ F ≡ interp S ρ
assembly a i′ s ls eq k hk ρ g with induct a 0 0 i′ s ls eq
... | e , r = f k , h k , nthT , nthS , tick-frames _ _ (r k) ρ g
  where
    f : ℕ → Dia ℕ
    f j = fromMaybe ε (proj₂ (framesN a) j)
    h : ℕ → Dia (OExpr ℕ)
    h j = fromMaybe εS (proj₂ (symTM s) j)
    hk′ : (k <ᵇ proj₁ (framesN a)) ≡ true
    hk′ = subst (λ n → (k <ᵇ n) ≡ true) (sym (sample-dur natClock _ _ natVal _ a)) hk
    nthT : nth (timeline a) k ≡ just (f k)
    nthT = trans (nth-applyUpTo f (proj₁ (framesN a)) k) (cong (λ c → if c then just (f k) else nothing) hk′)
    nthS : nth (symbolicFrames s) k ≡ just (h k)
    nthS = trans (nth-applyUpTo h (proj₁ (symTM s)) k)
                 (cong (λ c → if c then just (h k) else nothing) (subst (λ n → (k <ᵇ n) ≡ true) e hk′))

discrete-assembly = assembly

------------------------------------------------------------------------
-- The leaves are numbered apart

Numbered : ℕ → List Leaf → Set
Numbered i []       = ⊤
Numbered i (l ∷ ls) = Leaf.idx l ≡ i × Numbered (ℕ.suc i) ls

private
  Numbered-++ : ∀ l₁ l₂ i → Numbered i l₁ → Numbered (i + length l₁) l₂ → Numbered i (l₁ ++ l₂)
  Numbered-++ []       l₂ i _ n₂ = subst (λ j → Numbered j l₂) (ℕP.+-identityʳ i) n₂
  Numbered-++ (l ∷ l₁) l₂ i (e , n₁) n₂ =
    e , Numbered-++ l₁ l₂ (ℕ.suc i) n₁ (subst (λ j → Numbered j l₂) (ℕP.+-suc i (length l₁)) n₂)

  +-len : ∀ i l₁ l₂ → i + length l₁ + length l₂ ≡ i + length (l₁ ++ l₂)
  +-len i l₁ l₂ = trans (ℕP.+-assoc i (length l₁) (length l₂)) (cong (i +_) (sym (LP.length-++ {A = Leaf} l₁ {l₂})))

place-numbered : ∀ a i t₀ i′ s ls → place i t₀ a ≡ just (i′ , s , ls) → Numbered i ls × i′ ≡ i + length ls
place-numbered (pure _) i t₀ i′ s ls ()
place-numbered (impure (Seq , k)) i t₀ i′ s ls eq with bind-just (place i t₀ (k zero)) _ eq
... | (i₁ , a₁ , l₁) , e₁ , r₁ with bind-just (place i₁ (t₀ + dur (k zero)) (k (suc zero))) _ r₁
... | (i₂ , a₂ , l₂) , e₂ , refl with place-numbered (k zero) i t₀ i₁ a₁ l₁ e₁ | place-numbered (k (suc zero)) i₁ _ i₂ a₂ l₂ e₂
... | n₁ , refl | n₂ , refl = Numbered-++ l₁ l₂ i n₁ n₂ , +-len i l₁ l₂
place-numbered (impure (Par , k)) i t₀ i′ s ls eq with bind-just (place i t₀ (k zero)) _ eq
... | (i₁ , a₁ , l₁) , e₁ , r₁ with bind-just (place i₁ t₀ (k (suc zero))) _ r₁
... | (i₂ , a₂ , l₂) , e₂ , refl with place-numbered (k zero) i t₀ i₁ a₁ l₁ e₁ | place-numbered (k (suc zero)) i₁ _ i₂ a₂ l₂ e₂
... | n₁ , refl | n₂ , refl = Numbered-++ l₁ l₂ i n₁ n₂ , +-len i l₁ l₂
place-numbered (impure (Delay n , k)) i t₀ i′ s ls eq with place i (t₀ + n) (k tt) in e₁
place-numbered (impure (Delay n , k)) i t₀ i′ s ls () | nothing
place-numbered (impure (Delay n , k)) i t₀ i′ _ _ refl | just (i₁ , a₁ , l₁) = place-numbered (k tt) i (t₀ + n) i₁ a₁ l₁ e₁
place-numbered (impure (Repeat _ , _)) i t₀ i′ s ls ()
place-numbered (impure (Drive _ , _)) i t₀ i′ s ls ()
place-numbered (impure (Hold n , k)) i t₀ i′ s ls eq with place-hold i t₀ n k eq
... | tr , d , eqs with trans (sym (place-seg i t₀ (impure (Hold n , k)) eqs)) eq
... | refl = (refl , _) , ℕP.+-comm 1 i

------------------------------------------------------------------------
-- The assignment `i ↦ (parameter of segment i at tick k)`
--
-- `GoodL` says what an assignment must do; this is one that does it: `assignAt` gives variable `j`
-- the floored parameter of the leaf numbered `j` at tick `k` if that leaf is running, and 0 otherwise.

-- the parameter of a leaf at tick `k` if it is running there
activeVal : Leaf → ℕ → ℕ
activeVal l k =
  if (ℕ._≤ᵇ_ (Leaf.start l) k) ∧ (k <ᵇ Leaf.start l + Tr.dur (Leaf.track l))
  then units (proj₂ (Tr.sample Tr.ℚLerp (Leaf.track l)) (k ∸ Leaf.start l)) else 0

assignAt : List Leaf → ℕ → ℕ → ℕ
assignAt []       k j = 0
assignAt (l ∷ ls) k j = (if ⌊ j ℕP.≟ Leaf.idx l ⌋ then activeVal l k else 0) + assignAt ls k j

private
  true≢false : true ≡ false → ⊥
  true≢false ()

  ⌊≟⌋-diag : ∀ i → ⌊ i ℕP.≟ i ⌋ ≡ true
  ⌊≟⌋-diag i rewrite ℕP.≟-diag {i} {i} refl = refl

  ⌊≟⌋-neq : ∀ i j → (i ≡ j → ⊥) → ⌊ i ℕP.≟ j ⌋ ≡ false
  ⌊≟⌋-neq i j ne with i ℕP.≟ j
  ... | yes e = ⊥-elim (ne e)
  ... | no _  = refl

activeVal-on : ∀ l m → (m <ᵇ Tr.dur (Leaf.track l)) ≡ true →
               activeVal l (Leaf.start l + m) ≡ units (proj₂ (Tr.sample Tr.ℚLerp (Leaf.track l)) m)
activeVal-on l m h =
  trans (cong (λ b → if b then units (proj₂ (Tr.sample Tr.ℚLerp (Leaf.track l)) (Leaf.start l + m ∸ Leaf.start l)) else 0)
              (cong₂ _∧_ (≤ᵇ-true (ℕP.m≤m+n (Leaf.start l) m))
                         (<ᵇ-true (ℕP.+-monoʳ-< (Leaf.start l) (<ᵇ-lt h)))))
        (cong (λ x → units (proj₂ (Tr.sample Tr.ℚLerp (Leaf.track l)) x)) (ℕP.m+n∸m≡n (Leaf.start l) m))

-- the variables outside the range of the leaves are 0
assignAt-out : ∀ ls i → Numbered i ls → ∀ k j → ((j ℕ.< i) ⊎ (i + length ls ≤ j)) → assignAt ls k j ≡ 0
assignAt-out []       i _ k j out = refl
assignAt-out (l ∷ ls) i (refl , n) k j out =
  trans (cong₂ _+_ (cong (λ b → if b then activeVal l k else 0) (⌊≟⌋-neq j (Leaf.idx l) ne))
                   (assignAt-out ls (ℕ.suc (Leaf.idx l)) n k j out′))
        refl
  where
    ne : j ≡ Leaf.idx l → ⊥
    ne e = ne′ out e
      where ne′ : (j ℕ.< Leaf.idx l) ⊎ (Leaf.idx l + length (l ∷ ls) ≤ j) → j ≡ Leaf.idx l → ⊥
            ne′ (inj₁ h) refl = ℕP.<-irrefl refl h
            ne′ (inj₂ h) refl = ℕP.<⇒≱ (ℕP.m<m+n (Leaf.idx l) (ℕP.0<1+n {length ls})) h
    out′ : (j ℕ.< ℕ.suc (Leaf.idx l)) ⊎ (ℕ.suc (Leaf.idx l) + length ls ≤ j)
    out′ = go out
      where go : (j ℕ.< Leaf.idx l) ⊎ (Leaf.idx l + length (l ∷ ls) ≤ j) → _
            go (inj₁ h) = inj₁ (ℕP.<-trans h (ℕP.n<1+n _))
            go (inj₂ h) = inj₂ (subst (_≤ j) (ℕP.+-suc (Leaf.idx l) (length ls)) h)

-- `assignAt` is good, and so is anything that agrees with it on the variables of the leaves
canonical-good : ∀ ls i → Numbered i ls → ∀ k ρ →
                 (∀ j → i ≤ j → j ℕ.< i + length ls → ρ j ≡ assignAt ls k j) → GoodL ls k ρ
canonical-good []       i _ k ρ h = []
canonical-good (l ∷ ls) i (refl , n) k ρ h =
  (λ m hm e →
     trans (h (Leaf.idx l) ℕP.≤-refl (ℕP.m<m+n (Leaf.idx l) (ℕP.0<1+n {length ls})))
     (trans (cong₂ _+_ (cong (λ b → if b then activeVal l k else 0) (⌊≟⌋-diag (Leaf.idx l)))
                       (assignAt-out ls (ℕ.suc (Leaf.idx l)) n k (Leaf.idx l) (inj₁ (ℕP.n<1+n _))))
            (trans (ℕP.+-identityʳ _) (trans (cong (activeVal l) (sym e)) (activeVal-on l m hm)))))
  ∷ canonical-good ls (ℕ.suc (Leaf.idx l)) n k ρ
      (λ j lo hi → trans (h j (ℕP.≤-trans (ℕP.n≤1+n _) lo) (subst (j ℕ.<_) (sym (ℕP.+-suc (Leaf.idx l) (length ls))) hi))
                         (cong (_+ assignAt ls k j)
                               (cong (λ b → if b then activeVal l k else 0)
                                     (⌊≟⌋-neq j (Leaf.idx l) (λ e → ℕP.<-irrefl (sym e) lo)))))

-- Statement, with the assignment named: variable `j` is the floored parameter, at tick `k`, of
-- the segment numbered `j` (0 when it is not running).  No hypothesis beyond `a` having a parametric
-- encoding.
assembly-canonical :
  ∀ a i′ s ls → place 0 0 a ≡ just (i′ , s , ls) → ∀ k → (k <ᵇ dur a) ≡ true →
  ∃₂ λ F S → nth (timeline a) k ≡ just F
           × nth (symbolicFrames s) k ≡ just S
           × layoutℕ F ≡ interp S (assignAt ls k)
assembly-canonical a i′ s ls eq k hk =
  assembly a i′ s ls eq k hk (assignAt ls k)
    (canonical-good ls 0 (proj₁ (place-numbered a 0 0 i′ s ls eq)) k (assignAt ls k) (λ j _ _ → refl))

------------------------------------------------------------------------
-- The shipped segments are the leaves, in order of their variable

-- the leaf at position `d` of a list numbered from `i` has variable `i + d` and is the `d`-th shipped segment
segmentsOf-nth : ∀ ls i → Numbered i ls → ∀ d lf → nth ls d ≡ just lf →
                 Leaf.idx lf ≡ i + d × nth (segmentsOf ls) d ≡ just (Leaf.start lf , pieces (Leaf.track lf))
segmentsOf-nth []       i _ d lf ()
segmentsOf-nth (l ∷ ls) i (refl , n) ℕ.zero    lf refl = sym (ℕP.+-identityʳ _) , refl
segmentsOf-nth (l ∷ ls) i (refl , n) (ℕ.suc d) lf e with segmentsOf-nth ls (ℕ.suc (Leaf.idx l)) n d lf e
... | e₁ , e₂ = trans e₁ (sym (ℕP.+-suc (Leaf.idx l) d)) , e₂

------------------------------------------------------------------------
-- What `render` ships

private
  map-just : ∀ {A B : Set} (f : A → B) (m : Maybe A) {y} → Maybe.map f m ≡ just y →
             ∃ λ x → m ≡ just x × f x ≡ y
  map-just f (just x) refl = x , refl , refl
  map-just f nothing  ()

-- the acts, one after the other, play their frames one after the other
seqAll-timeline : ∀ acts {a} → seqAll acts ≡ just a → timeline a ≡ concat (map timeline acts)
seqAll-timeline []             ()
seqAll-timeline (a ∷ [])       refl = sym (LP.++-identityʳ (timeline a))
seqAll-timeline (a ∷ b ∷ as)   eq =
  let r = map-just (a ⨾_) (seqAll (b ∷ as)) eq in
  trans (cong timeline (sym (proj₂ (proj₂ r))))
  (trans (timeline-⨾ a (proj₁ r))
         (cong (timeline a ++_) (seqAll-timeline (b ∷ as) (proj₁ (proj₂ r)))))

private
  guard : ∀ b {q p} → (if b then nonEmptyParam q else nothing) ≡ just p → q ≡ p
  guard false ()
  guard true {q} eq with DP.Param.ticks q
  guard true {q} refl | _ ∷ _ = refl

-- what `paramOf` is made of
paramOf-inv : ∀ acts {p} → paramOf acts ≡ just p →
              ∃₂ λ a s → ∃₂ λ ls i′ → seqAll acts ≡ just a × place 0 0 a ≡ just (i′ , s , ls) × mkParam s ls ≡ p
paramOf-inv acts eq with bind-just (seqAll acts) _ eq
... | a , e₁ , r₁ with bind-just (place 0 0 a) _ r₁
... | (i′ , s , ls) , e₂ , r₂ = a , s , ls , i′ , e₁ , e₂ , guard (moving ls) r₂

private
  shipped : ∀ acts a s ls i′ → seqAll acts ≡ just a → place 0 0 a ≡ just (i′ , s , ls) →
            ∀ k → (k <ᵇ length (concat (map timeline acts))) ≡ true →
            ∀ ρ → GoodL ls k ρ →
            ∃₂ λ F L → nth (concat (map timeline acts)) k ≡ just F
                     × nth (DP.Param.ticks (mkParam s ls)) k ≡ just L
                     × layoutℕ F ≡ mapLayout (evalO natO ρ) L
  shipped acts a s ls i′ ea ep k hk ρ g with
    assembly a i′ s ls ep k
      (subst (λ n → (k <ᵇ n) ≡ true) (length-dur a)
        (subst (λ xs → (k <ᵇ length xs) ≡ true) (sym (seqAll-timeline acts ea)) hk)) ρ g
  ... | F , S , eF , eS , r =
    F , layoutE S , subst (λ xs → nth xs k ≡ just F) (seqAll-timeline acts ea) eF
      , trans (nth-map layoutE (symbolicFrames s) k) (cong (Maybe.map layoutE) eS) , r

-- Statement (A) for what `render` ships.  If `paramOf acts ≡ just p`, there are leaves `ls` (the
-- numbered segments, with their tracks) whose `segmentsOf` are the shipped `segments`, and for every
-- tick `k` of the frames `render` shows (`concat (map timeline acts)`) and every assignment `ρ` that is
-- right for the leaves running at `k`, the shipped layout of tick `k`, evaluated at `ρ`, is the
-- layout of the shown frame.
paramOf-assembly :
  ∀ acts {p} → paramOf acts ≡ just p →
  ∃ λ ls → DP.Param.segments p ≡ segmentsOf ls
         × ∀ k → (k <ᵇ length (concat (map timeline acts))) ≡ true →
           ∀ ρ → GoodL ls k ρ →
           ∃₂ λ F L → nth (concat (map timeline acts)) k ≡ just F
                    × nth (DP.Param.ticks p) k ≡ just L
                    × layoutℕ F ≡ mapLayout (evalO natO ρ) L
paramOf-assembly acts eq with paramOf-inv acts eq
... | a , s , ls , i′ , ea , ep , refl = ls , refl , shipped acts a s ls i′ ea ep

-- The same with the assignment named, and the shipped segments identified: variable `j` is the
-- `j`-th entry of `segments` (the leaf `lf` at position `j` has `idx lf ≡ j` and is
-- `(start lf , pieces (track lf))`), and its value at tick `k` is the floored parameter of that
-- segment's track there.
paramOf-assembly-canonical :
  ∀ acts {p} → paramOf acts ≡ just p →
  ∃ λ ls → DP.Param.segments p ≡ segmentsOf ls
         × (∀ d lf → nth ls d ≡ just lf →
              Leaf.idx lf ≡ d × nth (DP.Param.segments p) d ≡ just (Leaf.start lf , pieces (Leaf.track lf)))
         × ∀ k → (k <ᵇ length (concat (map timeline acts))) ≡ true →
           ∃₂ λ F L → nth (concat (map timeline acts)) k ≡ just F
                    × nth (DP.Param.ticks p) k ≡ just L
                    × layoutℕ F ≡ mapLayout (evalO natO (assignAt ls k)) L
paramOf-assembly-canonical acts eq with paramOf-inv acts eq
... | a , s , ls , i′ , ea , ep , refl =
  ls , refl
  , (λ d lf e → segmentsOf-nth ls 0 (proj₁ (place-numbered a 0 0 i′ s ls ep)) d lf e)
  , λ k hk → shipped acts a s ls i′ ea ep k hk (assignAt ls k)
      (canonical-good ls 0 (proj₁ (place-numbered a 0 0 i′ s ls ep)) k (assignAt ls k) (λ j _ _ → refl))
