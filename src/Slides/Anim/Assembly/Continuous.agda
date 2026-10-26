{-# OPTIONS --safe --without-K #-}

-- The assembly of whole frames, continuous reading, at whole ticks: `leaf-tick` lifted from one
-- segment to the whole timeline (`Slides.Anim.Continuous`).
--
-- Statement (B).  Let `a` be an animation of templates (`animAt a ≡ just T`).  At every whole
-- tick `k < dur a`, if every segment running at `k` is *exact* at its tick (`Good a k`: the
-- hypotheses of `leaf-tick` for that segment: the sample of its track is a whole number `q ≡
-- ι (units q)` and the layout of its template is `Faithful` at `units q`), then
--
--     frameAt a (ι k)  ≡  just (mapLayout ι (layout_ℕ (frame k of timeline atop (frames natOps) a)))
--
-- (`frameAt-assembly`): the continuous frame at the whole tick is the discrete frame sent
-- through `ι`.  `Good a k` is only about the segments running at `k` (a `Seq` asks it of the
-- first part while `k` is in it and of the second, at `k ∸ dur`, after; a `Par` of each part that
-- is running).  The global form (`AllExact`: every segment is exact at each of its ticks) is
-- `frameAt-assembly-all`.
--
-- What `atop` needs of `ι`.  `ι` is not an `Ops`-homomorphism (on `∸` it preserves the
-- difference only when the minuend is the larger; on `percentOf` only when exact), so layout
-- is not natural along it in general; that is why the hypotheses `Faithful` are needed for a
-- segment's layout.  But `atop` computes only sums, maxima and the differences `(a ⊔ b) - a`,
-- `(a ⊔ b) - b`, whose minuend is the larger by construction.  So `atop` commutes with
-- `mapLayout ι` on every pair of layouts, *with no hypothesis* (`atop-ι`, by
-- `Slides.Diagram.Place.Properties.Atop`), and the assembly of the timeline needs `Faithful` only for the
-- layouts of the leaf templates.  (The report's expectation that `atop` would need a
-- `Faithful`-style hypothesis on the layouts was not borne out.)
--
-- Not covered: the frames between whole ticks (`k < τ < k+1`), where `frameAt` is evaluated at
-- the fractional parameters; that is checked in the browser.  `layout`-level `Faithful`
-- hypotheses are on the *template's* layout in the one variable, exactly as in `leaf-tick`.

module Slides.Anim.Assembly.Continuous where

open import Data.Bool using (true; false; if_then_else_; T)
open import Data.List using (_∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_; _≤_)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (zero; suc)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Data.Rational as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Slides.Diagram.Draw using (Layout; mapLayout)
open import Slides.Diagram.Syntax using (Dia; atop; mapDia)
open import Slides.Diagram.Expr using (exprOps; eval)
open import Slides.Diagram.ExprQ using (AllLayout; Faithful; faithful-layout)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (natOps; ratOps)
open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.NatQ.Properties using (ι-+; ι-⊔; ι-∸)
import Slides.Diagram.Place natOps as PN
import Slides.Diagram.Place ratOps as PQ
import Slides.Diagram.Place.Properties.Atop as AN
import Slides.Anim.Track as Tr
import Slides.Anim.Track.Properties as TrP
open import Slides.Anim.Syntax
open import Slides.Anim.Timeline using (timeline; frames; length-dur; mergeM)
open import Slides.Anim.Continuous
open import Slides.Anim.Continuous.Properties
open import Slides.Anim.Arith using (<ᵇ-true; <ᵇ-lt; <ᵇ-ge)
open import Slides.Anim.Nth using (nth; nth-++′; nth-merge; nth-frames; nth-in)

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
-- One frame against one frame

-- the continuous frame at a whole tick is the discrete frame sent through `ι`; a frame is there
-- on one side exactly when it is on the other
data RelC : Maybe (Dia ℚ) → Maybe (Dia ℕ) → Set where
  noFrame    : RelC nothing nothing
  bothFrames : ∀ {D F} → layoutQ D ≡ mapLayout ι (layoutN F) → RelC (just D) (just F)

RelC-mergeM : ∀ {a b a′ b′} → RelC a a′ → RelC b b′ → RelC (mergeM atop a b) (mergeM atop a′ b′)
RelC-mergeM noFrame        rb               = rb
RelC-mergeM (bothFrames r) noFrame          = bothFrames r
RelC-mergeM (bothFrames {F = x′} r) (bothFrames {F = y′} s) =
  bothFrames (trans (cong₂ PQ.atop r s) (sym (atop-ι (layoutN x′) (layoutN y′))))

RelC-just : ∀ {m F} → RelC m (just F) → ∃ λ D → m ≡ just D × layoutQ D ≡ mapLayout ι (layoutN F)
RelC-just (bothFrames {D} s) = D , refl , s

------------------------------------------------------------------------
-- The hypotheses: exactness of the segments that are running

-- a template segment is exact at its tick `m`: the hypotheses of `leaf-tick`
Exact : Seg ℕ → ℕ → Set
Exact (seg tr (template d)) m =
  let q = proj₂ (Tr.sample Tr.ℚLerp tr) m in
  q ≡ ι (units q) × AllLayout (Faithful (λ _ → units q)) (LayoutWith.layout exprOps d)
Exact (seg tr (blackBox _)) m = ⊤
Exact (seg tr (discrete _)) m = ⊤

-- Exactness of the segments running at the tick `k` of an animation (`k` relative to its start).
Good : Anim ℕ (Seg ℕ) → ℕ → Set
Good (pure s)           k = (k <ᵇ ticks s) ≡ true → Exact s k
Good (impure (Seq , c)) k = ((k <ᵇ dur (c zero)) ≡ true → Good (c zero) k)
                          × ((k <ᵇ dur (c zero)) ≡ false → Good (c (suc zero)) (k ∸ dur (c zero)))
Good (impure (Par , c)) k = ((k <ᵇ dur (c zero)) ≡ true → Good (c zero) k)
                          × ((k <ᵇ dur (c (suc zero))) ≡ true → Good (c (suc zero)) k)

-- every segment is exact at each of its ticks
AllExact : Anim ℕ (Seg ℕ) → Set
AllExact (pure s)           = ∀ m → (m <ᵇ ticks s) ≡ true → Exact s m
AllExact (impure (Seq , c)) = AllExact (c zero) × AllExact (c (suc zero))
AllExact (impure (Par , c)) = AllExact (c zero) × AllExact (c (suc zero))

AllExact⇒Good : ∀ a → AllExact a → ∀ k → Good a k
AllExact⇒Good (pure s)           ex k = ex k
AllExact⇒Good (impure (Seq , c)) (e₁ , e₂) k =
  (λ _ → AllExact⇒Good (c zero) e₁ k) , (λ _ → AllExact⇒Good (c (suc zero)) e₂ _)
AllExact⇒Good (impure (Par , c)) (e₁ , e₂) k =
  (λ _ → AllExact⇒Good (c zero) e₁ k) , (λ _ → AllExact⇒Good (c (suc zero)) e₂ k)

------------------------------------------------------------------------
-- A segment

-- outside `[0, ticks)` nothing is shown at a whole tick
leafAt-out : ∀ tr d k → (k <ᵇ Tr.dur tr) ≡ false → proj₂ (leafAt tr d) (ι k) ≡ nothing
leafAt-out tr d k hk
  rewrite sampleAt-dur Tr.ℚLerp tr | TrP.sample-dur Tr.ℚLerp tr | ι-<ᵗ k (Tr.dur tr) | hk | zero≤ι k = refl

------------------------------------------------------------------------
-- Arithmetic of ticks

private
  -- inside the first part of a `Seq`, inside the sum
  <ᵇ-+ˡ : ∀ {k n} m → (k <ᵇ n) ≡ true → (k <ᵇ n + m) ≡ true
  <ᵇ-+ˡ {k} {n} m h = <ᵇ-true {k} {n + m} (ℕP.<-≤-trans {k} {n} {n + m} (<ᵇ-lt {k} {n} h) (ℕP.m≤m+n n m))

  -- inside the second part: `k ∸ n < m` once `n ≤ k`
  <ᵇ-shift : ∀ {k n m} → (k <ᵇ n) ≡ false → (k ∸ n <ᵇ m) ≡ true → (k <ᵇ n + m) ≡ true
  <ᵇ-shift {k} {n} {m} hk hm =
    <ᵇ-true {k} {n + m} (subst (ℕ._< n + m) (ℕP.m+[n∸m]≡n {n} {k} (<ᵇ-ge {k} {n} hk))
                                 (ℕP.+-monoʳ-< n {k ∸ n} {m} (<ᵇ-lt {k ∸ n} {m} hm)))

  <ᵇ-⊔ˡ : ∀ {k n} m → (k <ᵇ n) ≡ true → (k <ᵇ n ℕ.⊔ m) ≡ true
  <ᵇ-⊔ˡ {k} {n} m h = <ᵇ-true {k} {n ℕ.⊔ m} (ℕP.<-≤-trans {k} {n} {n ℕ.⊔ m} (<ᵇ-lt {k} {n} h) (ℕP.m≤m⊔n n m))

  <ᵇ-⊔ʳ : ∀ {k m} n → (k <ᵇ m) ≡ true → (k <ᵇ n ℕ.⊔ m) ≡ true
  <ᵇ-⊔ʳ {k} {m} n h = <ᵇ-true {k} {n ℕ.⊔ m} (ℕP.<-≤-trans {k} {m} {n ℕ.⊔ m} (<ᵇ-lt {k} {m} h) (ℕP.m≤n⊔m n m))

------------------------------------------------------------------------
-- The theorem, tick by tick

assembly : ∀ a T → animAt a ≡ just T → ∀ k → ((k <ᵇ dur a) ≡ true → Good a k) →
           RelC (proj₂ T (ι k)) (nth (timeline atop (frames natOps) a) k)
assembly (pure (seg tr (template d))) T refl k H
  rewrite nth-frames natOps (seg tr (template d)) k | TrP.sample-dur Tr.ℚLerp tr
  with k <ᵇ Tr.dur tr in eq
... | false = subst (λ m → RelC m nothing) (sym (leafAt-out tr d k eq)) noFrame
... | true  =
  let q  = proj₂ (Tr.sample Tr.ℚLerp tr) k
      ex = H refl refl
  in subst (λ m → RelC m (just (mapDia (eval (λ _ → units q)) d))) (sym (leafAt-ι tr d k eq))
       (bothFrames (trans (cong (λ r → layoutQ (instQ d r)) (proj₁ ex))
                          (sym (faithful-layout (λ _ → units q) d (proj₂ ex)))))
assembly (pure (seg tr (blackBox f))) T () k H
assembly (pure (seg tr (discrete d))) T () k H
assembly (impure (Seq , c)) T eq k H with lift2-just seqAt (animAt (c zero)) (animAt (c (suc zero))) eq
... | A , B , e₁ , e₂ , refl = go (nth-++′ (timeline atop (frames natOps) (c zero)) (timeline atop (frames natOps) (c (suc zero)))
                                              k (dur (c zero)) (length-dur natOps (c zero)))
  where
    n = dur (c zero)
    m = dur (c (suc zero))
    A-dur = animAt-dur (c zero) A e₁
    step : proj₂ (seqAt A B) (ι k)
           ≡ (if ι k <ᵗ ι n then proj₂ A (ι k) else proj₂ B (ι k ℚ.- ι n))
    step = cong (λ x → if ι k <ᵗ ι x then proj₂ A (ι k) else proj₂ B (ι k ℚ.- ι x)) A-dur
    go : nth (timeline atop (frames natOps) (c zero) ++ timeline atop (frames natOps) (c (suc zero))) k
         ≡ (if k <ᵇ n then nth (timeline atop (frames natOps) (c zero)) k
            else nth (timeline atop (frames natOps) (c (suc zero))) (k ∸ n)) →
         RelC (proj₂ (seqAt A B) (ι k))
              (nth (timeline atop (frames natOps) (c zero) ++ timeline atop (frames natOps) (c (suc zero))) k)
    go e rewrite step | e | ι-<ᵗ k n with k <ᵇ n in ek
    ... | true  = assembly (c zero) A e₁ k (λ _ → proj₁ (H (<ᵇ-+ˡ {k} {n} m ek)) refl)
    ... | false rewrite sym (ι-∸ k n (<ᵇ-ge ek)) =
      assembly (c (suc zero)) B e₂ (k ∸ n) (λ t → proj₂ (H (<ᵇ-shift {k} {n} {m} ek t)) refl)
assembly (impure (Par , c)) T eq k H with lift2-just (parAt atop) (animAt (c zero)) (animAt (c (suc zero))) eq
... | A , B , e₁ , e₂ , refl
  rewrite nth-merge atop (timeline atop (frames natOps) (c zero)) (timeline atop (frames natOps) (c (suc zero))) k =
  RelC-mergeM (assembly (c zero) A e₁ k (λ t → proj₁ (H (<ᵇ-⊔ˡ {k} {dur (c zero)} (dur (c (suc zero))) t)) t))
              (assembly (c (suc zero)) B e₂ k (λ t → proj₂ (H (<ᵇ-⊔ʳ {k} {dur (c (suc zero))} (dur (c zero)) t)) t))

------------------------------------------------------------------------
-- Statement (B)

frameAt-just : ∀ a T → animAt a ≡ just T → ∀ τ → frameAt a τ ≡ Maybe.map (LayoutWith.layout ratOps) (proj₂ T τ)
frameAt-just a T eq τ rewrite eq = refl

-- The continuous frame at the whole tick `k` is the discrete frame sent through `ι`, provided
-- the segments running at `k` are exact there.
frameAt-assembly :
  ∀ a T → animAt a ≡ just T → ∀ k → (k <ᵇ dur a) ≡ true → Good a k →
  ∃ λ F → nth (timeline atop (frames natOps) a) k ≡ just F
        × frameAt a (ι k) ≡ just (mapLayout ι (layoutN F))
frameAt-assembly a T eq k hk g with nth-in (timeline atop (frames natOps) a) k
                                      (subst (λ n → (k <ᵇ n) ≡ true) (sym (length-dur natOps a)) hk)
... | F , eF = F , eF , trans (frameAt-just a T eq (ι k)) (go (subst (RelC (proj₂ T (ι k))) eF (assembly a T eq k (λ _ → g))))
  where
    go : RelC (proj₂ T (ι k)) (just F) → Maybe.map layoutQ (proj₂ T (ι k)) ≡ just (mapLayout ι (layoutN F))
    go r with RelC-just r
    ... | D , e , s = trans (cong (Maybe.map layoutQ) e) (cong just s)

-- ... for a whole animation of exact segments, at every tick
frameAt-assembly-all :
  ∀ a T → animAt a ≡ just T → AllExact a → ∀ k → (k <ᵇ dur a) ≡ true →
  ∃ λ F → nth (timeline atop (frames natOps) a) k ≡ just F
        × frameAt a (ι k) ≡ just (mapLayout ι (layoutN F))
frameAt-assembly-all a T eq ex k hk = frameAt-assembly a T eq k hk (AllExact⇒Good a ex k)
