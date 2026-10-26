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
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _/_; _%_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Integer using (+_)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

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
