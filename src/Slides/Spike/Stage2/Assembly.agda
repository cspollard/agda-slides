{-# OPTIONS --safe --without-K #-}

-- THEORY MODULE (spike): no executable imports it (`tests/check_closure.py`).
--
-- `frameAt-assembly` re-derived on the Stage 2 container.
--
-- What the old proof (`Slides.Anim.Assembly.Continuous`, 230 lines) does, and what is different:
--   * it folds an animation into a `Maybe (Timed _)` and has `lift2-just` and `animAt-dur`
--     (in `Continuous.Properties`) to take the `Maybe` apart: here the embedding is total
--     (`Scene.embed`, template segments only) and the duration is `embed-dur`;
--   * its hypothesis `Good a k` recurses through the animation with the arithmetic of `Seq`
--     (`<ᵇ-+ˡ`, `<ᵇ-shift`, `<ᵇ-⊔ˡ`, `<ᵇ-⊔ʳ`) and a `Good ⇐ AllExact` bridge: here the
--     relation `RelN` is carried through `Seq`/`Par` once (`relN-seq`, `relN-par`), and the
--     hypothesis is the global `AllExact` (see "what is weaker");
--   * `Seq` and `Par` are bridged from the ℚ clock to the ℕ clock by two lemmas about the
--     temporal algebra (`seqW-tick`, `tickQ` on `parAt`) and from lists by `nth-++g`; nothing
--     about the animation language is used.
--
-- What is weaker than the old statement: `Good a k` asks exactness only of the leaves running at
-- the tick `k`; `AllExactT` asks it of every leaf at each of its own ticks (the old
-- `frameAt-assembly-all`).  The local form can be recovered by relativising `AllExactT` to the
-- tick, at the cost of the old arithmetic; it is not used by any other module.

module Slides.Spike.Stage2.Assembly where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; _++_; length)
import Data.List.Properties as LP
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ; _+_; _∸_; _<ᵇ_; _≤_)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Slides.Diagram.Draw using (Layout; mapLayout)
open import Slides.Diagram.Syntax using (Dia; atop; mapDia; Atop)
open import Slides.Diagram.Expr using (exprOps)
open import Slides.Diagram.Expr.Properties.Faithful using (AllLayout; Faithful; faithful-layout)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (natOps; ratOps)
open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.NatQ.Properties using (ι-+; ι-⊔; ι-∸)
import Slides.Diagram.Place natOps as PN
import Slides.Diagram.Place ratOps as PQ
import Slides.Diagram.Place.Properties.Atop as AN
import Slides.Anim.Track as Tr
import Slides.Anim.Syntax as A
open import Slides.Anim.Syntax using (units)
open import Slides.Anim.Timeline using (timeline; frames; mergeM; merge)
open import Slides.Anim.Timeline.Properties using (length-merge)
import Slides.Anim.Timeline.Properties as TLP
open import Slides.Anim.Continuous using (seqAt; parAt; sampleAt; instQ)
open import Slides.Anim.Continuous.Properties using (ι-<ᵗ; zero≤ι; sampleAt-ι; sampleAt-dur)
import Slides.Anim.Track.Properties as TrP
open import Slides.Anim.Arith using (<ᵇ-true; <ᵇ-lt; <ᵇ-ge; <ᵇ-false)
open import Slides.Anim.Nth using (nth; nth-++; nth-merge; nth-frames; nth-in)
open import Slides.Spike.Timed using (TM; holdT; fin2)
open import Slides.Spike.Stage2.Scene
open import Slides.Spike.Stage2.Scene.Properties

private
  layoutN : Dia ℕ → Layout ℕ
  layoutN = LayoutWith.layout natOps

  layoutQ : Dia ℚ → Layout ℚ
  layoutQ = LayoutWith.layout ratOps

------------------------------------------------------------------------
-- `atop` commutes with `ι`, for any layouts

atop-ι : ∀ a b → mapLayout ι (PN.atop a b) ≡ PQ.atop (mapLayout ι a) (mapLayout ι b)
atop-ι = AN.atop-natural′ natOps ratOps ι ι-+ ι-⊔
           (λ a b → ι-∸ (a ℕ.⊔ b) a (ℕP.m≤m⊔n a b))
           (λ a b → ι-∸ (a ℕ.⊔ b) b (ℕP.m≤n⊔m a b))

------------------------------------------------------------------------
-- The ℕ clock.  A timed value read at whole ticks, and a list read by `nth`, are both a duration
-- and a partial function of the tick; `RelN R` relates two of them tick by tick.

TN : Set → Set
TN A = ℕ × (ℕ → Maybe A)

tickQ : ∀ {A} → TM A → TN A
tickQ (n , f) = n , λ k → f (ι k)

nthN : ∀ {A} → List A → TN A
nthN xs = length xs , nth xs

record RelN {A B : Set} (R : Maybe A → Maybe B → Set) (X : TN A) (Y : TN B) : Set where
  constructor relN
  field
    durR : proj₁ X ≡ proj₁ Y
    atR  : ∀ k → R (proj₂ X k) (proj₂ Y k)
open RelN public

-- lists: `++` is the same, read through `nth`
nth-out : ∀ {A : Set} (xs : List A) k → (k <ᵇ length xs) ≡ false → nth xs k ≡ nothing
nth-out []       k         h = refl
nth-out (x ∷ xs) ℕ.zero    ()
nth-out (x ∷ xs) (ℕ.suc k) h = nth-out xs k h

private
  <ᵇ-+ˡ : ∀ {k n} m → (k <ᵇ n) ≡ true → (k <ᵇ n + m) ≡ true
  <ᵇ-+ˡ {k} {n} m h = <ᵇ-true {k} {n + m} (ℕP.<-≤-trans {k} {n} {n + m} (<ᵇ-lt {k} {n} h) (ℕP.m≤m+n n m))

  contra : ∀ {X : Set} → true ≡ false → X
  contra ()

nth-++g : ∀ {A : Set} (xs ys : List A) k →
  nth (xs ++ ys) k ≡
  (if k <ᵇ length xs + length ys then (if k <ᵇ length xs then nth xs k else nth ys (k ∸ length xs)) else nothing)
nth-++g xs ys k rewrite nth-++ xs ys k with k <ᵇ length xs + length ys in e₁ | k <ᵇ length xs in e₂
... | true  | _     = refl
... | false | true  = contra (trans (sym (<ᵇ-+ˡ {k} {length xs} (length ys) e₂)) e₁)
... | false | false = nth-out ys (k ∸ length xs) (<ᵇ-shift-false (length xs) (length ys) e₁)

module _ {A B : Set} {R : Maybe A → Maybe B → Set} where

  relN-seq : R nothing nothing → ∀ {X Y : TM A} {xs ys} →
             RelN R (tickQ X) (nthN xs) → RelN R (tickQ Y) (nthN ys) →
             RelN R (tickQ (seqW X Y)) (nthN (xs ++ ys))
  relN-seq R∅ {n , f} {m , g} {xs} {ys} (relN refl p) (relN refl q) = relN (sym (LP.length-++ xs)) pt
    where
      pt : ∀ k → R (proj₂ (seqW (length xs , f) (length ys , g)) (ι k)) (nth (xs ++ ys) k)
      pt k rewrite seqW-tick (length xs , f) (length ys , g) k | nth-++g xs ys k with k <ᵇ length xs + length ys
      ... | false = R∅
      ... | true  with k <ᵇ length xs
      ...   | true  = p k
      ...   | false = q (k ∸ length xs)

  relN-par : ∀ {⊙ : A → A → A} {⊙′ : B → B → B} →
             (∀ {x x′ y y′} → R x x′ → R y y′ → R (mergeM ⊙ x y) (mergeM ⊙′ x′ y′)) →
             ∀ {X Y : TM A} {xs ys} →
             RelN R (tickQ X) (nthN xs) → RelN R (tickQ Y) (nthN ys) →
             RelN R (tickQ (parAt ⊙ X Y)) (nthN (merge ⊙′ xs ys))
  relN-par {⊙′ = ⊙′} Rm {n , f} {m , g} {xs} {ys} (relN refl p) (relN refl q) =
    relN (sym (length-merge ⊙′ xs ys)) λ k → subst (R _) (sym (nth-merge ⊙′ xs ys k)) (Rm (p k) (q k))

------------------------------------------------------------------------
-- One frame against one frame (the continuous frame at a whole tick is the discrete frame
-- through `ι`), `Par` is `atop` on both sides

data RelR : Maybe RD → Maybe (Dia ℕ) → Set where
  noFrame    : RelR nothing nothing
  bothFrames : ∀ {g F} → layoutQ (g 0ℚ) ≡ mapLayout ι (layoutN F) → RelR (just g) (just F)

RelR-mergeM : ∀ {x x′ y y′} → RelR x x′ → RelR y y′ →
              RelR (mergeM (λ a b → algD Atop (fin2 a b)) x y) (mergeM atop x′ y′)
RelR-mergeM noFrame        rb               = rb
RelR-mergeM (bothFrames r) noFrame          = bothFrames r
RelR-mergeM (bothFrames {F = x′} r) (bothFrames {F = y′} s) =
  bothFrames (trans (cong₂ PQ.atop r s) (sym (atop-ι (layoutN x′) (layoutN y′))))

-- exactness of a template segment at its tick `m` (the hypotheses of `leaf-tick`)
ExactT : TSeg → ℕ → Set
ExactT (tr , d) m =
  let q = proj₂ (Tr.sample Tr.ℚLerp tr) m in
  q ≡ ι (units q) × AllLayout (Faithful (λ _ → units q)) (LayoutWith.layout exprOps d)

-- every segment is exact at each of its ticks
AllExactT : TAnim → Set
AllExactT (pure (tr , d))   = ∀ m → (m <ᵇ Tr.dur tr) ≡ true → ExactT (tr , d) m
AllExactT (impure (_ , c))  = AllExactT (c zero) × AllExactT (c (suc zero))

------------------------------------------------------------------------
-- A segment

leaf : ∀ tr d → (∀ m → (m <ᵇ Tr.dur tr) ≡ true → ExactT (tr , d) m) →
       RelN RelR (tickQ (sample algD bindD (segS (tr , d)))) (nthN (frames natOps (A.seg tr (A.template d))))
leaf tr d ex = relN (sym (TLP.frames-length natOps (A.seg tr (A.template d)))) pt
  where
    pt : ∀ k → RelR (proj₂ (sample algD bindD (segS (tr , d))) (ι k)) (nth (frames natOps (A.seg tr (A.template d))) k)
    pt k rewrite segS-at tr d (ι k) | zero≤ι k | ι-<ᵗ k (Tr.dur tr)
               | nth-frames natOps (A.seg tr (A.template d)) k | TrP.sample-dur Tr.ℚLerp tr
      with k <ᵇ Tr.dur tr in eq
    ... | false = noFrame
    ... | true  =
      let q  = proj₂ (Tr.sample Tr.ℚLerp tr) k
          e  = ex k eq
      in bothFrames (trans (cong layoutQ (fold-algD d _))
           (trans (cong (λ r → layoutQ (instQ d r)) (trans (sampleAt-ι Tr.ℚLerp tr k) (proj₁ e)))
                  (sym (faithful-layout (λ _ → units q) d (proj₂ e)))))

------------------------------------------------------------------------
-- The theorem, tick by tick

QS : TAnim → TM RD
QS t = sample algD bindD (embed t)

LS : TAnim → List (Dia ℕ)
LS t = timeline atop (frames natOps) (toAnim t)

assembly : ∀ t → AllExactT t → RelN RelR (tickQ (QS t)) (nthN (LS t))
assembly (pure (tr , d))        ex        = leaf tr d ex
assembly (impure (A.Seq , k))   (e₁ , e₂) =
  relN-seq noFrame {QS (k zero)} {QS (k (suc zero))} {LS (k zero)} {LS (k (suc zero))}
    (assembly (k zero) e₁) (assembly (k (suc zero)) e₂)
assembly (impure (A.Par , k))   (e₁ , e₂) =
  relN-par RelR-mergeM {X = QS (k zero)} {Y = QS (k (suc zero))} {xs = LS (k zero)} {ys = LS (k (suc zero))}
    (assembly (k zero) e₁) (assembly (k (suc zero)) e₂)

-- the frame the scene shows at τ, as a layout
frameQ : TAnim → ℚ → Maybe (Layout ℚ)
frameQ t τ = Maybe.map layoutQ (proj₂ (framesD (embed t)) τ)

-- STATEMENT: the continuous frame of the scene at a whole tick `k` is the discrete frame sent
-- through `ι` (compare `Slides.Anim.Assembly.Continuous.frameAt-assembly-all`)
RelR-just : ∀ {m F} → RelR m (just F) → ∃ λ g → m ≡ just g × layoutQ (g 0ℚ) ≡ mapLayout ι (layoutN F)
RelR-just (bothFrames {g} s) = g , refl , s

frameAt-assembly′ :
  ∀ t → AllExactT t → ∀ k → (k <ᵇ A.dur (toAnim t)) ≡ true →
  ∃ λ F → nth (LS t) k ≡ just F × frameQ t (ι k) ≡ just (mapLayout ι (layoutN F))
frameAt-assembly′ t ex k hk with nth-in (LS t) k (subst (λ n → (k <ᵇ n) ≡ true) (sym (TLP.length-dur natOps (toAnim t))) hk)
... | F , eF = F , eF , go (subst (RelR (proj₂ (QS t) (ι k))) eF (atR (assembly t ex) k))
  where
    go : RelR (proj₂ (QS t) (ι k)) (just F) → frameQ t (ι k) ≡ just (mapLayout ι (layoutN F))
    go r with RelR-just r
    ... | g , e , s = trans (cong (λ m → Maybe.map layoutQ (Maybe.map (λ h → h 0ℚ) m)) e) (cong just s)
