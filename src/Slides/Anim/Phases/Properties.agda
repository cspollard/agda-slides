{-# OPTIONS --safe --without-K #-}

-- What the shipped phases mean (`Slides.Anim.Phases` ships them).
--
-- The page, at the parameters `ρ` of the segments, shows for a phase element `pageElem e ρ`: the
-- base command with each number replaced by the value of its formula (when it has one).  What
-- the page does with the shipped data does not depend on which expression language the symbolic
-- frames are over, nor on how a shipped formula is read (ℚ for continuous templates, ℕ for
-- discrete ones, `Slides.Anim.Formula`); only on two facts about each slot of a command: the
-- formula's value is the number the slot stands for (`slot-val`, positions halved), and a slot that
-- folded to a constant has the right base number (`slot-num`).  So the theorems are proved once,
-- in `Over`, given those two facts; `Slides.Anim.Phases.Properties` instantiates it at ℚ
-- (continuous templates) and `Slides.Anim.DPhases.Properties` at ℕ (discrete ones).  We prove
--
--   * `encode-sem`: for a drawing command `dr` of a symbolic layout, `pageElem (encodeWith slot
--     bval dr) ρ` is `dr` evaluated at `ρ` with positions halved (positions are in half units,
--     sizes in units): `halve (mapDraw (tval ρ) dr)`.  This includes that the folded closed
--     subformulas are exact and that the base numbers, taken at the all-zero assignment, are the
--     right ones where the formula is a folded constant.
--   * `phases-active`: grouping ticks into phases (`runs`) does not change the frame at any tick:
--     the phase in force at tick `k` has the same elements as tick `k` itself.
--   * `pageFrame-sem`: so at tick `k` the page's frame, at `ρ`, is the symbolic layout of tick `k`
--     evaluated at `ρ` and halved: the frame `Slides.Anim.Continuous.frameAt` (resp. the discrete
--     frame), drawn.
--
-- Not proved: the printing of this data as JSON and its parsing by the player (`parse`, the
-- attribute table `NUMS` in `assets/animation.js`, which must follow `nums`), and the floating
-- point of `ev`.  Those are tested (`tests/browser`).

module Slides.Anim.Phases.Properties where

open import Data.Bool using (true; false; if_then_else_; T)
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Unary.All as All
open All using (All; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _/_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Integer using (+_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using ()
import Data.Nat.Properties as ℕP
import Data.List.Properties as LP

open import Slides.Diagram.Draw using (Draw; rect; circle; line; arrow; label; mapDraw; Layout)
open import Slides.Diagram.NatQ.Properties using (ι)
open import Slides.Anim.Formula
open import Slides.Anim.Arith using (≤ᵇ-true)
open import Slides.Anim.Nth using (nth; nth-map)
open import Slides.Anim.Phases

------------------------------------------------------------------------
-- The numbers a page sets

-- the base number as the page reads it from the SVG: positions are halved (rounding down)
baseNum : Kind × ℕ → ℚ
baseNum (pos  , n) = ι (n / 2)
baseNum (size , n) = ι n

-- half the positions
halfIf : Kind → ℚ → ℚ
halfIf pos  v = (+ 1 ℚ./ 2) ℚ.* v
halfIf size v = v

halve : Draw ℚ → Draw ℚ
halve d = withNums d (map (λ ks → halfIf (proj₁ ks) (proj₂ ks)) (nums d)) 0ℚ

-- the command does not depend on the numbers it is refilled over
withNums-mapDraw : ∀ {S S′ T : Set} (f : S → S′) (d : Draw S) (ts : List T) (dflt : T) →
                   withNums (mapDraw f d) ts dflt ≡ withNums d ts dflt
withNums-mapDraw f (rect _ _ _ _ _)  ts d = refl
withNums-mapDraw f (circle _ _ _ _)  ts d = refl
withNums-mapDraw f (line _ _ _ _ _)  ts d = refl
withNums-mapDraw f (arrow _ _ _ _ _) ts d = refl
withNums-mapDraw f (label _ _ _ _ _) ts d = refl

-- the numbers of a mapped command
nums-mapDraw : ∀ {S S′ : Set} (f : S → S′) (d : Draw S) →
               nums (mapDraw f d) ≡ map (λ ks → proj₁ ks , f (proj₂ ks)) (nums d)
nums-mapDraw f (rect _ _ _ _ _)  = refl
nums-mapDraw f (circle _ _ _ _)  = refl
nums-mapDraw f (line _ _ _ _ _)  = refl
nums-mapDraw f (arrow _ _ _ _ _) = refl
nums-mapDraw f (label _ _ _ _ _) = refl

-- the numbers the page sets: the formula's value (`v`, how a formula is read) where there is one,
-- else the base number
pageNumsG : (Formula → ℚ) → List (Kind × ℕ) → List (Maybe Formula) → List ℚ
pageNumsG v []       _              = []
pageNumsG v (b ∷ bs) []             = baseNum b ∷ pageNumsG v bs []
pageNumsG v (b ∷ bs) (nothing ∷ es) = baseNum b ∷ pageNumsG v bs es
pageNumsG v (b ∷ bs) (just f  ∷ es) = v f ∷ pageNumsG v bs es

pageElemG : (Formula → ℚ) → Elem → Draw ℚ
pageElemG v e = withNums (Elem.base e) (pageNumsG v (nums (Elem.base e)) (entries (Elem.coords e))) 0ℚ

------------------------------------------------------------------------
-- What the page picks

-- What the page picks at tick `t`: the last phase whose start is at most `t` (it starts from
-- the first phase, whatever its start)
pick : ∀ {A : Set} → A → List (ℕ × A) → ℕ → A
pick cur []             t = cur
pick cur ((s , a) ∷ ps) t = if s ℕ.≤ᵇ t then pick a ps t else cur

active : ∀ {A : Set} → List (ℕ × A) → ℕ → Maybe A
active []             t = nothing
active ((s , a) ∷ ps) t = just (pick a ps t)

-- the phases start at or after the first tick
runs-start : ∀ {A : Set} (_≟_ : DecidableEquality A) prev k (xs : List A) →
             All (λ p → k ℕ.≤ proj₁ p) (runs _≟_ prev k xs)
runs-start _≟_ prev k []       = []
runs-start _≟_ prev k (x ∷ xs) with prev
... | nothing = ℕP.≤-refl ∷ All.map (ℕP.≤-trans (ℕP.n≤1+n k)) (runs-start _≟_ (just x) (suc k) xs)
... | just p  with x ≟ p
...   | yes _ = All.map (ℕP.≤-trans (ℕP.n≤1+n k)) (runs-start _≟_ (just p) (suc k) xs)
...   | no _  = ℕP.≤-refl ∷ All.map (ℕP.≤-trans (ℕP.n≤1+n k)) (runs-start _≟_ (just x) (suc k) xs)

private
  pick-none : ∀ {A : Set} (cur : A) ps t → All (λ p → suc t ℕ.≤ proj₁ p) ps → pick cur ps t ≡ cur
  pick-none cur []             t []        = refl
  pick-none cur ((s , a) ∷ ps) t (h ∷ _) with s ℕ.≤ᵇ t in e
  ... | true  = ⊥-elim (ℕP.<-irrefl refl (ℕP.<-≤-trans h (ℕP.≤ᵇ⇒≤ s t (subst T (sym e) tt))))
  ... | false = refl

  -- after `cur`, the entries of the ticks `k, k+1, …` are those that `pick` finds
  runs-pick : ∀ {A : Set} (_≟_ : DecidableEquality A) (cur : A) k (xs : List A) j {x} →
              nth xs j ≡ just x → pick cur (runs _≟_ (just cur) k xs) (k + j) ≡ x
  runs-pick _≟_ cur k []       j       ()
  runs-pick _≟_ cur k (y ∷ ys) j       h with y ≟ cur
  runs-pick _≟_ cur k (y ∷ ys) zero    refl | yes e =
    trans (pick-none cur _ (k + 0) (All.map (λ {p} q → ℕP.<-≤-trans (subst (ℕ._< suc k) (sym (ℕP.+-identityʳ k)) (ℕP.n<1+n k)) q)
                                       (runs-start _≟_ (just cur) (suc k) ys)))
          (sym e)
  runs-pick _≟_ cur k (y ∷ ys) (suc j) {x} h | yes e =
    subst (λ t → pick cur (runs _≟_ (just cur) (suc k) ys) t ≡ x) (sym (ℕP.+-suc k j)) (runs-pick _≟_ cur (suc k) ys j h)
  runs-pick _≟_ cur k (y ∷ ys) zero    refl | no _ rewrite ℕP.+-identityʳ k | ≤ᵇ-true (ℕP.≤-refl {k}) =
    pick-none y _ k (runs-start _≟_ (just y) (suc k) ys)
  runs-pick _≟_ cur k (y ∷ ys) (suc j) {x} h | no _ rewrite ≤ᵇ-true (ℕP.m≤m+n k (suc j)) =
    subst (λ t → pick y (runs _≟_ (just y) (suc k) ys) t ≡ x) (sym (ℕP.+-suc k j)) (runs-pick _≟_ y (suc k) ys j h)

-- Grouping into phases does not change what is in force at any tick.
phases-active : ∀ {A : Set} (_≟_ : DecidableEquality A) (xs : List A) j {x} →
                nth xs j ≡ just x → active (runs _≟_ nothing 0 xs) j ≡ just x
phases-active _≟_ []       j ()
phases-active _≟_ (y ∷ ys) zero    refl = cong just (pick-none y _ 0 (runs-start _≟_ (just y) 1 ys))
phases-active _≟_ (y ∷ ys) (suc j) h    = cong just (runs-pick _≟_ y 1 ys j h)


-- picking the phase in force commutes with changing what a phase holds
pick-map : ∀ {A B : Set} (f : A → B) cur ps t →
           pick (f cur) (map (λ p → proj₁ p , f (proj₂ p)) ps) t ≡ f (pick cur ps t)
pick-map f cur []             t = refl
pick-map f cur ((s , a) ∷ ps) t with s ℕ.≤ᵇ t
... | true  = pick-map f a ps t
... | false = refl

active-map : ∀ {A B : Set} (f : A → B) ps t →
             active (map (λ p → proj₁ p , f (proj₂ p)) ps) t ≡ Maybe.map f (active ps t)
active-map f []             t = refl
active-map f ((s , a) ∷ ps) t = cong just (pick-map f a ps t)

------------------------------------------------------------------------
-- A drawing command means what it ships

-- a formula is a constant (which `entry` drops) or not (which `entry` keeps)
entry-view : ∀ f → (∃ λ c → f ≡ num c) ⊎ (entry f ≡ just f × isNum f ≡ false)
entry-view (num c)       = inj₁ (c , refl)
entry-view (var _)       = inj₂ (refl , refl)
entry-view (add _ _)     = inj₂ (refl , refl)
entry-view (sub _ _)     = inj₂ (refl , refl)
entry-view (max _ _)     = inj₂ (refl , refl)
entry-view (pct _ _)     = inj₂ (refl , refl)
entry-view (hlf _)       = inj₂ (refl , refl)
entry-view (fdiv _ _)    = inj₂ (refl , refl)
entry-view (fmod _ _)    = inj₂ (refl , refl)
entry-view (fmul _ _)    = inj₂ (refl , refl)
entry-view (flt _ _ _ _) = inj₂ (refl , refl)

private
  false≢true : false ≡ true → ⊥
  false≢true ()

-- The slots of a command (`E` its numbers, `P` the assignments), shipped by `slot` (the formula of
-- a number) and `bval` (the base number, at the all-zero assignment), read by `rd`, meant as `tval`.
module Over {E P : Set} (slot : Kind × E → Formula) (bval : E → ℕ) (rd : Formula → P → ℚ) (tval : P → E → ℚ)
  -- a slot's formula has the value the slot stands for (positions halved)
  (slot-val : ∀ x ρ → rd (slot x) ρ ≡ halfIf (proj₁ x) (tval ρ (proj₂ x)))
  -- a slot that folded to a constant has the right base number
  (slot-num : ∀ x c ρ → slot x ≡ num c →
              baseNum (proj₁ x , bval (proj₂ x)) ≡ halfIf (proj₁ x) (tval ρ (proj₂ x)))
  where

  -- what the page draws for an element, and at a tick
  pageElem : Elem → P → Draw ℚ
  pageElem e ρ = pageElemG (λ f → rd f ρ) e

  pageFrame : List (ℕ × List Elem) → ℕ → P → Maybe (List (Draw ℚ))
  pageFrame ps k ρ = Maybe.map (map (λ e → pageElem e ρ)) (active ps k)

  private
    -- the value a number should have at `ρ`
    target : P → Kind × E → ℚ
    target ρ x = halfIf (proj₁ x) (tval ρ (proj₂ x))

    base0 : Kind × E → Kind × ℕ
    base0 x = proj₁ x , bval (proj₂ x)

    pageNums-A : ∀ ns ρ → pageNumsG (λ f → rd f ρ) (map base0 ns) (map (λ x → entry (slot x)) ns) ≡ map (target ρ) ns
    pageNums-A []       ρ = refl
    pageNums-A (x ∷ ns) ρ with entry-view (slot x)
    ... | inj₁ (c , e)  rewrite e = cong₂ _∷_ (slot-num x c ρ e) (pageNums-A ns ρ)
    ... | inj₂ (e , _)  rewrite e = cong₂ _∷_ (slot-val x ρ) (pageNums-A ns ρ)

    pageNums-B : ∀ ns ρ → allNum (map slot ns) ≡ true → pageNumsG (λ f → rd f ρ) (map base0 ns) [] ≡ map (target ρ) ns
    pageNums-B []       ρ h = refl
    pageNums-B (x ∷ ns) ρ h with entry-view (slot x)
    ... | inj₁ (c , e) =
      cong₂ _∷_ (slot-num x c ρ e)
                (pageNums-B ns ρ (subst (λ f → allNum (f ∷ map slot ns) ≡ true) e h))
    ... | inj₂ (_ , nn) =
      ⊥-elim (false≢true (subst (λ b → (if b then allNum (map slot ns) else false) ≡ true) nn h))

  -- The drawn element of what is shipped for a command of a symbolic layout is the command, at
  -- `ρ`, with positions halved.
  encode-sem : ∀ (dr : Draw E) ρ →
               pageElem (encodeWith slot bval dr) ρ ≡ halve (mapDraw (tval ρ) dr)
  encode-sem dr ρ =
    trans (withNums-mapDraw bval dr L₁ 0ℚ)
   (trans (cong (λ ts → withNums dr ts 0ℚ) (trans L₁≡T (sym L₂≡T)))
          (sym (withNums-mapDraw (tval ρ) dr L₂ 0ℚ)))
    where
      ns = nums dr
      cs = coordsOf (map slot ns)
      L₁ = pageNumsG (λ f → rd f ρ) (nums (mapDraw bval dr)) (entries cs)
      L₂ = map (λ ks → halfIf (proj₁ ks) (proj₂ ks)) (nums (mapDraw (tval ρ) dr))
      L₂≡T : L₂ ≡ map (target ρ) ns
      L₂≡T = trans (cong (map (λ ks → halfIf (proj₁ ks) (proj₂ ks))) (nums-mapDraw (tval ρ) dr))
                   (sym (LP.map-∘ ns))
      go : ∀ b → allNum (map slot ns) ≡ b →
           pageNumsG (λ f → rd f ρ) (map base0 ns) (entries (if b then nothing else just (map entry (map slot ns)))) ≡ map (target ρ) ns
      go true  h = pageNums-B ns ρ h
      go false h = trans (cong (pageNumsG (λ f → rd f ρ) (map base0 ns)) (sym (LP.map-∘ ns))) (pageNums-A ns ρ)
      L₁≡T : L₁ ≡ map (target ρ) ns
      L₁≡T = trans (cong (λ bs → pageNumsG (λ f → rd f ρ) bs (entries cs)) (nums-mapDraw bval dr))
                   (go (allNum (map slot ns)) refl)

  -- At tick `k < length ls`, the page draws the symbolic layout of tick `k` evaluated at `ρ`,
  -- positions halved: the grouping into phases, the encoding of the formulas (folded when exact)
  -- and the base elements lose nothing.
  pageFrame-sem : ∀ (ls : List (Layout E)) k L → nth ls k ≡ just L → ∀ ρ →
                  pageFrame (phasesWith slot bval ls) k ρ
                  ≡ just (map (λ dr → halve (mapDraw (tval ρ) dr)) (Layout.draws L))
  pageFrame-sem ls k L h ρ
    rewrite phases-active elemsEq? (map (tickElemsWith slot bval) ls) k
              (trans (nth-map (tickElemsWith slot bval) ls k) (cong (Maybe.map (tickElemsWith slot bval)) h)) =
    cong just (trans (sym (LP.map-∘ (Layout.draws L)))
                     (LP.map-cong (λ dr → encode-sem dr ρ) (Layout.draws L)))
