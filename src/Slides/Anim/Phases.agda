{-# OPTIONS --safe --without-K #-}

-- What the backend ships for a parametric animation, as data, and that it means the symbolic
-- frames (`Slides.Anim.Param`).  `Slides.Backend.Diagram` only prints this data as JSON.
--
-- The shipped structure (`data-param`, see `Slides.Backend.Diagram`) is a list of *phases*.  A
-- phase starts at a tick and has, for each drawing command of the layout, an `Elem`: the
-- command with its numbers taken at the all-zero assignment (`base`, shipped as an SVG
-- string: the page takes the numbers it does not override from it) and, for each of its
-- numbers in the page's attribute order, a formula or `null` (`coords`; `null` for all of them
-- when every number is a constant).  Ticks whose layouts ship the same elements share a phase.
--
-- Meaning.  The page, at the parameters `ρ` of the segments, shows for a phase element
-- `pageElem e ρ`: the base command with each number replaced by the value of its formula (when it
-- has one).  We prove
--
--   * `encodeDraw-sem`: for a drawing command `dr` of a symbolic layout, `pageElem (encodeDraw dr)
--     ρ` is `dr` evaluated in ℚ at `ρ` with positions halved (positions are in half units,
--     sizes in units): `halve (mapDraw (evalWith ratOps ρ) dr)`.  This includes that the folded
--     closed subformulas are exact (`Slides.Anim.Formula`) and that the base numbers, taken at the
--     all-zero assignment, are the right ones where the formula is a folded constant.
--   * `phases-sem`: grouping ticks into phases (`runs`) does not change the frame at any tick: the
--     phase in force at tick `k` has the same elements as tick `k` itself, hence the same
--     `pageFrame`.
--   * `pageFrame-sem`: so at tick `k` the page's frame, at `ρ`, is the symbolic layout of tick `k`
--     evaluated at `ρ` and halved: the continuous frame `Slides.Anim.Continuous.frameAt`, drawn.
--
-- Not proved: the printing of this data as JSON and its parsing by the player (`parse`, the
-- attribute table `NUMS` in `assets/animation.js`, which must follow `nums` below), and
-- the floating point of `ev`.  Those are tested (`tests/browser`).

module Slides.Anim.Phases where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; map; length)
import Data.List.Relation.Unary.All as All
open All using (All; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (T)
open import Data.Unit using (tt)
import Slides.Anim.ParamCorrect as PC
open PC using (nth)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _/_; _%_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Integer using (+_)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map′; ⌊_⌋)
import Data.Nat.Properties as ℕP
import Data.Maybe.Properties as MP
import Data.List.Properties as LP
open import Slides.Diagram.DrawEq using (drawEq?)

open import Slides.Diagram.Draw using (Draw; rect; circle; line; arrow; label; mapDraw; Layout)
open import Slides.Diagram.Expr using (Expr; eval; evalWith)
open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.Scalar using (ratOps)
open import Slides.Anim.Formula

------------------------------------------------------------------------
-- The numbers of a drawing command

data Kind : Set where
  pos size : Kind        -- a position (half units) or a size (units)

-- in the player's attribute order (`NUMS`)
nums : ∀ {S} → Draw S → List (Kind × S)
nums (rect x y w h _)  = (pos , x) ∷ (pos , y) ∷ (size , w) ∷ (size , h) ∷ []
nums (circle x y r _)  = (pos , x) ∷ (pos , y) ∷ (size , r) ∷ []
nums (line a b c d _)  = (pos , a) ∷ (pos , b) ∷ (pos , c) ∷ (pos , d) ∷ []
nums (arrow a b c d _) = (pos , a) ∷ (pos , b) ∷ (pos , c) ∷ (pos , d) ∷ []
nums (label x y _ _ _) = (pos , x) ∷ (pos , y) ∷ []

private
  headOr : ∀ {T : Set} → T → List T → T
  headOr d []      = d
  headOr d (x ∷ _) = x

  tailL : ∀ {T : Set} → List T → List T
  tailL []       = []
  tailL (_ ∷ xs) = xs

-- the same command with its numbers (in order) from a list; `dflt` when it runs out
withNums : ∀ {S T : Set} → Draw S → List T → T → Draw T
withNums (rect _ _ _ _ s) ts d =
  rect (headOr d ts) (headOr d (tailL ts)) (headOr d (tailL (tailL ts))) (headOr d (tailL (tailL (tailL ts)))) s
withNums (circle _ _ _ s) ts d =
  circle (headOr d ts) (headOr d (tailL ts)) (headOr d (tailL (tailL ts))) s
withNums (line _ _ _ _ s) ts d =
  line (headOr d ts) (headOr d (tailL ts)) (headOr d (tailL (tailL ts))) (headOr d (tailL (tailL (tailL ts)))) s
withNums (arrow _ _ _ _ s) ts d =
  arrow (headOr d ts) (headOr d (tailL ts)) (headOr d (tailL (tailL ts))) (headOr d (tailL (tailL (tailL ts)))) s
withNums (label _ _ n t s) ts d = label (headOr d ts) (headOr d (tailL ts)) n t s

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

-- half the positions
halfIf : Kind → ℚ → ℚ
halfIf pos  v = (+ 1 ℚ./ 2) ℚ.* v
halfIf size v = v

halve : Draw ℚ → Draw ℚ
halve d = withNums d (map (λ ks → halfIf (proj₁ ks) (proj₂ ks)) (nums d)) 0ℚ

------------------------------------------------------------------------
-- One drawing command, as shipped

-- the base command (its numbers at the all-zero assignment) and the formulas of its numbers;
-- `coords = nothing` when every number is constant, else an entry for each number, `nothing`
-- for a constant
record Elem : Set where
  constructor elem
  field
    base   : Draw ℕ
    coords : Maybe (List (Maybe Formula))
open Elem

-- the formula of a number: positions are halved
slotF : Kind × Expr ℕ → Formula
slotF (pos  , e) = half (enc e)
slotF (size , e) = enc e

entry : Formula → Maybe Formula
entry (num _) = nothing
entry f       = just f

allNum : List Formula → Bool
allNum []       = true
allNum (f ∷ fs) = if isNum f then allNum fs else false

coordsOf : List Formula → Maybe (List (Maybe Formula))
coordsOf fs = if allNum fs then nothing else just (map entry fs)

encodeDraw : Draw (Expr ℕ) → Elem
encodeDraw dr = elem (mapDraw (eval (λ _ → 0)) dr) (coordsOf (map slotF (nums dr)))

-- the base number as the page reads it from the SVG: positions are halved (rounding down)
baseNum : Kind × ℕ → ℚ
baseNum (pos  , n) = ι (n / 2)
baseNum (size , n) = ι n

entries : Maybe (List (Maybe Formula)) → List (Maybe Formula)
entries nothing   = []
entries (just cs) = cs

-- the numbers the page sets: the formula's value where there is one, else the base number
pageNums : List (Kind × ℕ) → List (Maybe Formula) → (ℕ → ℚ) → List ℚ
pageNums []       _              ρ = []
pageNums (b ∷ bs) []             ρ = baseNum b ∷ pageNums bs [] ρ
pageNums (b ∷ bs) (nothing ∷ es) ρ = baseNum b ∷ pageNums bs es ρ
pageNums (b ∷ bs) (just f  ∷ es) ρ = ⟦ f ⟧ ρ ∷ pageNums bs es ρ

pageElem : Elem → (ℕ → ℚ) → Draw ℚ
pageElem e ρ = withNums (base e) (pageNums (nums (base e)) (entries (coords e)) ρ) 0ℚ

------------------------------------------------------------------------
-- A drawing command means what it ships

private
  -- the value a number should have at `ρ`
  target : (ℕ → ℚ) → Kind × Expr ℕ → ℚ
  target ρ (k , e) = halfIf k (evalWith ratOps ρ e)

  base0 : Kind × Expr ℕ → Kind × ℕ
  base0 (k , e) = k , eval (λ _ → 0) e

  slot-val : ∀ x ρ → ⟦ slotF x ⟧ ρ ≡ target ρ x
  slot-val (pos  , e) ρ = trans (half-sem (enc e) ρ) (cong ((+ 1 ℚ./ 2) ℚ.*_) (enc-sem e ρ))
  slot-val (size , e) ρ = enc-sem e ρ

  -- a number that folded to a constant is the base number
  slot-num : ∀ x c ρ → slotF x ≡ num c → baseNum (base0 x) ≡ target ρ x
  slot-num (pos , e) c ρ h with half-num-inv (enc e) c h
  ... | a , e₁ , _ , refl =
    trans (cong (λ v → ι (v / 2)) (enc-num e a e₁ (λ _ → 0)))
          (trans (cong (λ f → ⟦ f ⟧ ρ) (sym h)) (slot-val (pos , e) ρ))
  slot-num (size , e) c ρ h =
    trans (cong ι (enc-num e c h (λ _ → 0)))
          (trans (cong (λ f → ⟦ f ⟧ ρ) (sym h)) (slot-val (size , e) ρ))

  pageNums-A : ∀ ns ρ → pageNums (map base0 ns) (map (λ x → entry (slotF x)) ns) ρ ≡ map (target ρ) ns
  pageNums-A []       ρ = refl
  pageNums-A (x ∷ ns) ρ with slotF x in eq
  ... | num c   = cong₂ _∷_ (slot-num x c ρ eq) (pageNums-A ns ρ)
  ... | var i   = cong₂ _∷_ (trans (cong (λ f → ⟦ f ⟧ ρ) (sym eq)) (slot-val x ρ)) (pageNums-A ns ρ)
  ... | add a b = cong₂ _∷_ (trans (cong (λ f → ⟦ f ⟧ ρ) (sym eq)) (slot-val x ρ)) (pageNums-A ns ρ)
  ... | sub a b = cong₂ _∷_ (trans (cong (λ f → ⟦ f ⟧ ρ) (sym eq)) (slot-val x ρ)) (pageNums-A ns ρ)
  ... | max a b = cong₂ _∷_ (trans (cong (λ f → ⟦ f ⟧ ρ) (sym eq)) (slot-val x ρ)) (pageNums-A ns ρ)
  ... | pct p a = cong₂ _∷_ (trans (cong (λ f → ⟦ f ⟧ ρ) (sym eq)) (slot-val x ρ)) (pageNums-A ns ρ)
  ... | hlf a   = cong₂ _∷_ (trans (cong (λ f → ⟦ f ⟧ ρ) (sym eq)) (slot-val x ρ)) (pageNums-A ns ρ)
  ... | fdiv d a  = cong₂ _∷_ (trans (cong (λ f → ⟦ f ⟧ ρ) (sym eq)) (slot-val x ρ)) (pageNums-A ns ρ)
  ... | fmod d a  = cong₂ _∷_ (trans (cong (λ f → ⟦ f ⟧ ρ) (sym eq)) (slot-val x ρ)) (pageNums-A ns ρ)
  ... | fmul n a  = cong₂ _∷_ (trans (cong (λ f → ⟦ f ⟧ ρ) (sym eq)) (slot-val x ρ)) (pageNums-A ns ρ)
  ... | flt a b c e  = cong₂ _∷_ (trans (cong (λ f → ⟦ f ⟧ ρ) (sym eq)) (slot-val x ρ)) (pageNums-A ns ρ)

  pageNums-B : ∀ ns ρ → allNum (map slotF ns) ≡ true → pageNums (map base0 ns) [] ρ ≡ map (target ρ) ns
  pageNums-B []       ρ h = refl
  pageNums-B (x ∷ ns) ρ h with slotF x in eq
  ... | num c   = cong₂ _∷_ (slot-num x c ρ eq) (pageNums-B ns ρ h)
  pageNums-B (x ∷ ns) ρ () | var i
  pageNums-B (x ∷ ns) ρ () | add a b
  pageNums-B (x ∷ ns) ρ () | sub a b
  pageNums-B (x ∷ ns) ρ () | max a b
  pageNums-B (x ∷ ns) ρ () | pct p a
  pageNums-B (x ∷ ns) ρ () | hlf a
  pageNums-B (x ∷ ns) ρ () | fdiv d a
  pageNums-B (x ∷ ns) ρ () | fmod d a
  pageNums-B (x ∷ ns) ρ () | fmul n a
  pageNums-B (x ∷ ns) ρ () | flt a b c e

  map-map : ∀ {A B C : Set} (f : B → C) (g : A → B) xs → map f (map g xs) ≡ map (λ x → f (g x)) xs
  map-map f g []       = refl
  map-map f g (x ∷ xs) = cong₂ _∷_ refl (map-map f g xs)

-- The drawn element of what is shipped for a command of a symbolic layout is the command, at
-- `ρ`, in ℚ, with positions halved.
encodeDraw-sem : ∀ (dr : Draw (Expr ℕ)) ρ →
                 pageElem (encodeDraw dr) ρ ≡ halve (mapDraw (evalWith ratOps ρ) dr)
encodeDraw-sem dr ρ =
  trans (withNums-mapDraw (eval (λ _ → 0)) dr L₁ 0ℚ)
 (trans (cong (λ ts → withNums dr ts 0ℚ) (trans L₁≡T (sym L₂≡T)))
        (sym (withNums-mapDraw (evalWith ratOps ρ) dr L₂ 0ℚ)))
  where
    ns = nums dr
    cs = coordsOf (map slotF ns)
    L₁ = pageNums (nums (mapDraw (eval (λ _ → 0)) dr)) (entries cs) ρ
    L₂ = map (λ ks → halfIf (proj₁ ks) (proj₂ ks)) (nums (mapDraw (evalWith ratOps ρ) dr))
    L₂≡T : L₂ ≡ map (target ρ) ns
    L₂≡T = trans (cong (map (λ ks → halfIf (proj₁ ks) (proj₂ ks))) (nums-mapDraw (evalWith ratOps ρ) dr))
                 (map-map (λ ks → halfIf (proj₁ ks) (proj₂ ks)) (λ ks → proj₁ ks , evalWith ratOps ρ (proj₂ ks)) ns)
    go : ∀ b → allNum (map slotF ns) ≡ b →
         pageNums (map base0 ns) (entries (if b then nothing else just (map entry (map slotF ns)))) ρ ≡ map (target ρ) ns
    go true  h = pageNums-B ns ρ h
    go false h = trans (cong (λ es → pageNums (map base0 ns) es ρ) (map-map entry slotF ns)) (pageNums-A ns ρ)
    L₁≡T : L₁ ≡ map (target ρ) ns
    L₁≡T = trans (cong (λ bs → pageNums bs (entries cs) ρ) (nums-mapDraw (eval (λ _ → 0)) dr))
                 (go (allNum (map slotF ns)) refl)

------------------------------------------------------------------------
-- Equality of what is shipped

formulaEq? : DecidableEquality Formula
formulaEq? (num x0) (num y0) with ℕP._≟_ x0 y0
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
formulaEq? (num _) (var _) = no λ ()
formulaEq? (num _) (add _ _) = no λ ()
formulaEq? (num _) (sub _ _) = no λ ()
formulaEq? (num _) (max _ _) = no λ ()
formulaEq? (num _) (pct _ _) = no λ ()
formulaEq? (num _) (hlf _) = no λ ()
formulaEq? (num _) (fdiv _ _) = no λ ()
formulaEq? (num _) (fmod _ _) = no λ ()
formulaEq? (num _) (fmul _ _) = no λ ()
formulaEq? (num _) (flt _ _ _ _) = no λ ()
formulaEq? (var _) (num _) = no λ ()
formulaEq? (var x0) (var y0) with ℕP._≟_ x0 y0
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
formulaEq? (var _) (add _ _) = no λ ()
formulaEq? (var _) (sub _ _) = no λ ()
formulaEq? (var _) (max _ _) = no λ ()
formulaEq? (var _) (pct _ _) = no λ ()
formulaEq? (var _) (hlf _) = no λ ()
formulaEq? (var _) (fdiv _ _) = no λ ()
formulaEq? (var _) (fmod _ _) = no λ ()
formulaEq? (var _) (fmul _ _) = no λ ()
formulaEq? (var _) (flt _ _ _ _) = no λ ()
formulaEq? (add _ _) (num _) = no λ ()
formulaEq? (add _ _) (var _) = no λ ()
formulaEq? (add x0 x1) (add y0 y1) with formulaEq? x0 y0 | formulaEq? x1 y1
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬p = no λ { refl → ¬p refl }
formulaEq? (add _ _) (sub _ _) = no λ ()
formulaEq? (add _ _) (max _ _) = no λ ()
formulaEq? (add _ _) (pct _ _) = no λ ()
formulaEq? (add _ _) (hlf _) = no λ ()
formulaEq? (add _ _) (fdiv _ _) = no λ ()
formulaEq? (add _ _) (fmod _ _) = no λ ()
formulaEq? (add _ _) (fmul _ _) = no λ ()
formulaEq? (add _ _) (flt _ _ _ _) = no λ ()
formulaEq? (sub _ _) (num _) = no λ ()
formulaEq? (sub _ _) (var _) = no λ ()
formulaEq? (sub _ _) (add _ _) = no λ ()
formulaEq? (sub x0 x1) (sub y0 y1) with formulaEq? x0 y0 | formulaEq? x1 y1
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬p = no λ { refl → ¬p refl }
formulaEq? (sub _ _) (max _ _) = no λ ()
formulaEq? (sub _ _) (pct _ _) = no λ ()
formulaEq? (sub _ _) (hlf _) = no λ ()
formulaEq? (sub _ _) (fdiv _ _) = no λ ()
formulaEq? (sub _ _) (fmod _ _) = no λ ()
formulaEq? (sub _ _) (fmul _ _) = no λ ()
formulaEq? (sub _ _) (flt _ _ _ _) = no λ ()
formulaEq? (max _ _) (num _) = no λ ()
formulaEq? (max _ _) (var _) = no λ ()
formulaEq? (max _ _) (add _ _) = no λ ()
formulaEq? (max _ _) (sub _ _) = no λ ()
formulaEq? (max x0 x1) (max y0 y1) with formulaEq? x0 y0 | formulaEq? x1 y1
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬p = no λ { refl → ¬p refl }
formulaEq? (max _ _) (pct _ _) = no λ ()
formulaEq? (max _ _) (hlf _) = no λ ()
formulaEq? (max _ _) (fdiv _ _) = no λ ()
formulaEq? (max _ _) (fmod _ _) = no λ ()
formulaEq? (max _ _) (fmul _ _) = no λ ()
formulaEq? (max _ _) (flt _ _ _ _) = no λ ()
formulaEq? (pct _ _) (num _) = no λ ()
formulaEq? (pct _ _) (var _) = no λ ()
formulaEq? (pct _ _) (add _ _) = no λ ()
formulaEq? (pct _ _) (sub _ _) = no λ ()
formulaEq? (pct _ _) (max _ _) = no λ ()
formulaEq? (pct x0 x1) (pct y0 y1) with ℕP._≟_ x0 y0 | formulaEq? x1 y1
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬p = no λ { refl → ¬p refl }
formulaEq? (pct _ _) (hlf _) = no λ ()
formulaEq? (pct _ _) (fdiv _ _) = no λ ()
formulaEq? (pct _ _) (fmod _ _) = no λ ()
formulaEq? (pct _ _) (fmul _ _) = no λ ()
formulaEq? (pct _ _) (flt _ _ _ _) = no λ ()
formulaEq? (hlf _) (num _) = no λ ()
formulaEq? (hlf _) (var _) = no λ ()
formulaEq? (hlf _) (add _ _) = no λ ()
formulaEq? (hlf _) (sub _ _) = no λ ()
formulaEq? (hlf _) (max _ _) = no λ ()
formulaEq? (hlf _) (pct _ _) = no λ ()
formulaEq? (hlf x0) (hlf y0) with formulaEq? x0 y0
... | yes refl = yes refl
... | no ¬p = no λ { refl → ¬p refl }
formulaEq? (hlf _) (fdiv _ _) = no λ ()
formulaEq? (hlf _) (fmod _ _) = no λ ()
formulaEq? (hlf _) (fmul _ _) = no λ ()
formulaEq? (hlf _) (flt _ _ _ _) = no λ ()
formulaEq? (fdiv _ _) (num _) = no λ ()
formulaEq? (fdiv _ _) (var _) = no λ ()
formulaEq? (fdiv _ _) (add _ _) = no λ ()
formulaEq? (fdiv _ _) (sub _ _) = no λ ()
formulaEq? (fdiv _ _) (max _ _) = no λ ()
formulaEq? (fdiv _ _) (pct _ _) = no λ ()
formulaEq? (fdiv _ _) (hlf _) = no λ ()
formulaEq? (fdiv x0 x1) (fdiv y0 y1) with ℕP._≟_ x0 y0 | formulaEq? x1 y1
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬p = no λ { refl → ¬p refl }
formulaEq? (fdiv _ _) (fmod _ _) = no λ ()
formulaEq? (fdiv _ _) (fmul _ _) = no λ ()
formulaEq? (fdiv _ _) (flt _ _ _ _) = no λ ()
formulaEq? (fmod _ _) (num _) = no λ ()
formulaEq? (fmod _ _) (var _) = no λ ()
formulaEq? (fmod _ _) (add _ _) = no λ ()
formulaEq? (fmod _ _) (sub _ _) = no λ ()
formulaEq? (fmod _ _) (max _ _) = no λ ()
formulaEq? (fmod _ _) (pct _ _) = no λ ()
formulaEq? (fmod _ _) (hlf _) = no λ ()
formulaEq? (fmod _ _) (fdiv _ _) = no λ ()
formulaEq? (fmod x0 x1) (fmod y0 y1) with ℕP._≟_ x0 y0 | formulaEq? x1 y1
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬p = no λ { refl → ¬p refl }
formulaEq? (fmod _ _) (fmul _ _) = no λ ()
formulaEq? (fmod _ _) (flt _ _ _ _) = no λ ()
formulaEq? (fmul _ _) (num _) = no λ ()
formulaEq? (fmul _ _) (var _) = no λ ()
formulaEq? (fmul _ _) (add _ _) = no λ ()
formulaEq? (fmul _ _) (sub _ _) = no λ ()
formulaEq? (fmul _ _) (max _ _) = no λ ()
formulaEq? (fmul _ _) (pct _ _) = no λ ()
formulaEq? (fmul _ _) (hlf _) = no λ ()
formulaEq? (fmul _ _) (fdiv _ _) = no λ ()
formulaEq? (fmul _ _) (fmod _ _) = no λ ()
formulaEq? (fmul x0 x1) (fmul y0 y1) with ℕP._≟_ x0 y0 | formulaEq? x1 y1
... | yes refl | yes refl = yes refl
... | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | no ¬p = no λ { refl → ¬p refl }
formulaEq? (fmul _ _) (flt _ _ _ _) = no λ ()
formulaEq? (flt _ _ _ _) (num _) = no λ ()
formulaEq? (flt _ _ _ _) (var _) = no λ ()
formulaEq? (flt _ _ _ _) (add _ _) = no λ ()
formulaEq? (flt _ _ _ _) (sub _ _) = no λ ()
formulaEq? (flt _ _ _ _) (max _ _) = no λ ()
formulaEq? (flt _ _ _ _) (pct _ _) = no λ ()
formulaEq? (flt _ _ _ _) (hlf _) = no λ ()
formulaEq? (flt _ _ _ _) (fdiv _ _) = no λ ()
formulaEq? (flt _ _ _ _) (fmod _ _) = no λ ()
formulaEq? (flt _ _ _ _) (fmul _ _) = no λ ()
formulaEq? (flt x0 x1 x2 x3) (flt y0 y1 y2 y3) with formulaEq? x0 y0 | formulaEq? x1 y1 | formulaEq? x2 y2 | formulaEq? x3 y3
... | yes refl | yes refl | yes refl | yes refl = yes refl
... | no ¬p | _ | _ | _ = no λ { refl → ¬p refl }
... | _ | no ¬p | _ | _ = no λ { refl → ¬p refl }
... | _ | _ | no ¬p | _ = no λ { refl → ¬p refl }
... | _ | _ | _ | no ¬p = no λ { refl → ¬p refl }

elemEq? : DecidableEquality Elem
elemEq? (elem b₁ c₁) (elem b₂ c₂) with drawEq? ℕP._≟_ b₁ b₂ | MP.≡-dec (LP.≡-dec (MP.≡-dec formulaEq?)) c₁ c₂
... | yes refl | yes refl = yes refl
... | no ¬p   | _        = no λ { refl → ¬p refl }
... | _       | no ¬q    = no λ { refl → ¬q refl }

elemsEq? : DecidableEquality (List Elem)
elemsEq? = LP.≡-dec elemEq?

------------------------------------------------------------------------
-- Grouping ticks into phases

-- `runs prev k xs`: the entries of `xs`, which start at tick `k`, that differ from the one
-- emitted before them (`prev`), with the tick they are at
module _ {A : Set} (_≟_ : DecidableEquality A) where

  runs : Maybe A → ℕ → List A → List (ℕ × A)
  runs prev k []       = []
  runs prev k (a ∷ as) with prev
  ... | nothing = (k , a) ∷ runs (just a) (suc k) as
  ... | just p  = if ⌊ a ≟ p ⌋ then runs prev (suc k) as else (k , a) ∷ runs (just a) (suc k) as

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

  ≤ᵇ-true : ∀ {m n} → m ℕ.≤ n → (m ℕ.≤ᵇ n) ≡ true
  ≤ᵇ-true {m} {n} h = go (m ℕ.≤ᵇ n) (ℕP.≤⇒≤ᵇ h) where
    go : ∀ b → T b → b ≡ true
    go true _ = refl

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

------------------------------------------------------------------------
-- The shipped phases of a list of symbolic layouts

tickElems : Layout (Expr ℕ) → List Elem
tickElems l = map encodeDraw (Layout.draws l)

-- the phases of the symbolic frames, one layout per tick
phasesOf : List (Layout (Expr ℕ)) → List (ℕ × List Elem)
phasesOf ls = runs elemsEq? nothing 0 (map tickElems ls)

-- what the page draws at tick `k`, at the parameters `ρ`
pageFrame : List (ℕ × List Elem) → ℕ → (ℕ → ℚ) → Maybe (List (Draw ℚ))
pageFrame ps k ρ = Maybe.map (map (λ e → pageElem e ρ)) (active ps k)

private
  map-cong : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → ∀ xs → map f xs ≡ map g xs
  map-cong e []       = refl
  map-cong e (x ∷ xs) = cong₂ _∷_ (e x) (map-cong e xs)

-- At tick `k < length ls`, the page draws the symbolic layout of tick `k` evaluated at `ρ` in ℚ,
-- positions halved: the grouping into phases, the encoding of the formulas (folded when
-- exact) and the base elements lose nothing.
pageFrame-sem : ∀ (ls : List (Layout (Expr ℕ))) k L → nth ls k ≡ just L → ∀ ρ →
                pageFrame (phasesOf ls) k ρ
                ≡ just (map (λ dr → halve (mapDraw (evalWith ratOps ρ) dr)) (Layout.draws L))
pageFrame-sem ls k L h ρ
  rewrite phases-active elemsEq? (map tickElems ls) k
            (trans (PC.nth-map tickElems ls k) (cong (Maybe.map tickElems) h)) =
  cong just (trans (map-map (λ e → pageElem e ρ) encodeDraw (Layout.draws L))
                   (map-cong (λ dr → encodeDraw-sem dr ρ) (Layout.draws L)))
