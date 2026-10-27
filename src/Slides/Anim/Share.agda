{-# OPTIONS --safe --without-K #-}

-- Shared subformulas: a straight-line program for the formulas of a phase.
--
-- A template's formulas (`Slides.Anim.Formula`) are *trees*.  Two coordinates of one element
-- (and of different elements) repeat the same subformula many times: the angle of a pair of
-- points occurs in each of its four coordinates and, inside a table lookup, seven times in each.
-- Shipped as trees, the formulas of the 26 drifting pairs are a few hundred thousand nodes
-- (`docs/Design.md`).  What is shipped instead is the *same formulas as a program*: a list of
-- definitions, each over the parameters and the earlier definitions, and the formulas themselves
-- as nodes over those (`Node`: one operation applied to arguments that are a number, a parameter
-- or a reference to a definition, `Arg`).
--
-- The mathematics.  A program is a Kleisli family `σ i : Formula (Fin i ⊎ V)` and its meaning is
-- the evaluation of the term obtained by substituting, definition by definition, into the
-- formula (`>>=`, `Slides.Diagram.Ordered.substO`): evaluating after a substitution is evaluating at
-- the evaluated substitution (`Properties.Laws.evalO-substO`, `foldT-bind`; here the same fact for the
-- shipped formulas is `env-def`, one definition at a time).  The page does not substitute, it
-- evaluates the definitions in order, once per time step, and then each coordinate: the DAG whose
-- unfolding is the tree.  A tree becomes a program by *value numbering* (`share`): a store of
-- definitions, extended as the formula is traversed bottom-up, in which an operation applied to
-- the same arguments is defined once (hash consing).  Several formulas, shared through one store,
-- share their subformulas too.
--
-- The index of the store is a *hint*.  The memo (an AVL map, keyed by a list of numbers
-- describing the node) maps a node to the number of its definition; before using it, `intern`
-- checks that the definition it names is that node, so the memo can be wrong (and is only ever
-- extended) without making the result wrong.  What is proved depends on that check, not on the
-- map: `Inv` says every entry of the memo names a true definition.
--
-- Theorems (`Slides.Anim.Share.Properties`, module `Sound`, for every *reading* of formulas:
-- `Reading`, instances at ℚ and ℕ in `Slides.Anim.SharePhases.Properties`):
--
--   * `share-impl`: for a formula `g`, any parameters `ρ` and any store `st` with `Inv st`,
--     `share g st = (r , st′)` extends the store (`Ext`), keeps `Inv`, `r` refers only to
--     definitions of `st′`, and `r` evaluated against the definitions of `st′` is the value of
--     `g` at `ρ`;
--   * `output-impl`: the same for the *output* of a coordinate (`output`), where the top node of
--     a position is a real half (`hlf`) and the rest is read as it was;
--   * `env-def`: the value the evaluation assigns to a definition is the node evaluated at the
--     values of the earlier ones; `unfold`, `unfold-sound`: the tree obtained by substituting
--     the definitions (the unfolding of the DAG) evaluates to the value of the definition, and
--     `share-unfold`: the unfolding of the reference `share g` returns evaluates equal to `g`
--     at every assignment (the compact form and the tree form mean the same);
--   * `shareAll-impl`: for a list of coordinates, shared through one store: the claims hold of
--     every element at the final store (the earlier ones keep their values: `Ext`).
--
-- Not proved: the printing of the program as JSON and its reading by the page (`ev` in
-- `assets/animation.js`: definitions evaluated in order into an array, a reference `-1 - i`
-- reading entry `i`), and its floating point.  Those are tested (`tests/browser`).

module Slides.Anim.Share where

open import Data.List using (List; []; _∷_; reverse; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ; suc; _<_)
import Data.Nat.Properties as ℕP
import Data.Sum.Properties as SP
import Data.Product.Properties as PP
import Data.Unit.Properties as UP
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
import Data.List.Relation.Binary.Lex.Strict as Lex
import Data.Tree.AVL.Map as AVLMap

open import Slides.DecEq using (retract-dec)
open import Slides.Anim.Formula using (Formula; num; var; add; sub; max; fmin; pct; hlf; fdiv; fmod; fmul; flt; fease; easingEq?)
open import Slides.Anim.Track using (Easing)

------------------------------------------------------------------------
-- Nodes: one operation, applied to arguments

-- an argument: a number, the parameter of a segment, or a reference to a definition
data Arg : Set where
  anum apar aref : ℕ → Arg

data Op1 : Set where
  oPct oDiv oMod oMul : ℕ → Op1
  oHlf                : Op1
  oEase               : Easing → Op1

data Op2 : Set where
  oAdd oSub oMax oMin : Op2

-- a formula with one operation at its root and arguments for its children
data Node : Set where
  atom : Arg → Node
  un   : Op1 → Arg → Node
  bin  : Op2 → Arg → Arg → Node
  quad : Arg → Arg → Arg → Arg → Node

------------------------------------------------------------------------
-- Decidable equality (the index of the store is only a hint, and it is checked)

-- each type is a retract of sums and products of numbers (`Slides.DecEq`)
private
  _≟ⁿ_ = ℕP._≟_

arg≟ : DecidableEquality Arg
arg≟ = retract-dec to from rt (SP.≡-dec _≟ⁿ_ (SP.≡-dec _≟ⁿ_ _≟ⁿ_))
  where
    to : Arg → ℕ ⊎ ℕ ⊎ ℕ
    to (anum n) = inj₁ n
    to (apar n) = inj₂ (inj₁ n)
    to (aref n) = inj₂ (inj₂ n)
    from : ℕ ⊎ ℕ ⊎ ℕ → Arg
    from (inj₁ n)        = anum n
    from (inj₂ (inj₁ n)) = apar n
    from (inj₂ (inj₂ n)) = aref n
    rt : ∀ a → from (to a) ≡ a
    rt (anum _) = refl
    rt (apar _) = refl
    rt (aref _) = refl

op1≟ : DecidableEquality Op1
op1≟ = retract-dec to from rt (SP.≡-dec _≟ⁿ_ (SP.≡-dec _≟ⁿ_ (SP.≡-dec _≟ⁿ_ (SP.≡-dec _≟ⁿ_ (SP.≡-dec UP._≟_ easingEq?)))))
  where
    to : Op1 → ℕ ⊎ ℕ ⊎ ℕ ⊎ ℕ ⊎ ⊤ ⊎ Easing
    to (oPct n)  = inj₁ n
    to (oDiv n)  = inj₂ (inj₁ n)
    to (oMod n)  = inj₂ (inj₂ (inj₁ n))
    to (oMul n)  = inj₂ (inj₂ (inj₂ (inj₁ n)))
    to oHlf      = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ tt))))
    to (oEase e) = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ e))))
    from : ℕ ⊎ ℕ ⊎ ℕ ⊎ ℕ ⊎ ⊤ ⊎ Easing → Op1
    from (inj₁ n)                                = oPct n
    from (inj₂ (inj₁ n))                         = oDiv n
    from (inj₂ (inj₂ (inj₁ n)))                  = oMod n
    from (inj₂ (inj₂ (inj₂ (inj₁ n))))           = oMul n
    from (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _)))))    = oHlf
    from (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ e)))))    = oEase e
    rt : ∀ o → from (to o) ≡ o
    rt (oPct _)  = refl
    rt (oDiv _)  = refl
    rt (oMod _)  = refl
    rt (oMul _)  = refl
    rt oHlf      = refl
    rt (oEase _) = refl

op2≟ : DecidableEquality Op2
op2≟ = retract-dec to from rt (SP.≡-dec UP._≟_ (SP.≡-dec UP._≟_ (SP.≡-dec UP._≟_ UP._≟_)))
  where
    to : Op2 → ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊤
    to oAdd = inj₁ tt
    to oSub = inj₂ (inj₁ tt)
    to oMax = inj₂ (inj₂ (inj₁ tt))
    to oMin = inj₂ (inj₂ (inj₂ tt))
    from : ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊤ → Op2
    from (inj₁ _)                 = oAdd
    from (inj₂ (inj₁ _))          = oSub
    from (inj₂ (inj₂ (inj₁ _)))   = oMax
    from (inj₂ (inj₂ (inj₂ _)))   = oMin
    rt : ∀ o → from (to o) ≡ o
    rt oAdd = refl
    rt oSub = refl
    rt oMax = refl
    rt oMin = refl

node≟ : DecidableEquality Node
node≟ = retract-dec to from rt
  (SP.≡-dec arg≟ (SP.≡-dec (PP.≡-dec op1≟ arg≟)
    (SP.≡-dec (PP.≡-dec op2≟ (PP.≡-dec arg≟ arg≟)) (PP.≡-dec arg≟ (PP.≡-dec arg≟ (PP.≡-dec arg≟ arg≟))))))
  where
    to : Node → Arg ⊎ (Op1 × Arg) ⊎ (Op2 × Arg × Arg) ⊎ (Arg × Arg × Arg × Arg)
    to (atom a)       = inj₁ a
    to (un o a)       = inj₂ (inj₁ (o , a))
    to (bin o a b)    = inj₂ (inj₂ (inj₁ (o , a , b)))
    to (quad a b c d) = inj₂ (inj₂ (inj₂ (a , b , c , d)))
    from : Arg ⊎ (Op1 × Arg) ⊎ (Op2 × Arg × Arg) ⊎ (Arg × Arg × Arg × Arg) → Node
    from (inj₁ a)                              = atom a
    from (inj₂ (inj₁ (o , a)))                 = un o a
    from (inj₂ (inj₂ (inj₁ (o , a , b))))      = bin o a b
    from (inj₂ (inj₂ (inj₂ (a , b , c , d))))  = quad a b c d
    rt : ∀ n → from (to n) ≡ n
    rt (atom _)     = refl
    rt (un _ _)     = refl
    rt (bin _ _ _)  = refl
    rt (quad _ _ _ _) = refl


------------------------------------------------------------------------
-- The store

-- the memo is ordered by a list of numbers that describes a node (it need not be injective)
keyA : Arg → List ℕ
keyA (anum n) = 0 ∷ n ∷ []
keyA (apar n) = 1 ∷ n ∷ []
keyA (aref n) = 2 ∷ n ∷ []

key1 : Op1 → List ℕ
key1 (oPct n) = 0 ∷ n ∷ []
key1 (oDiv n) = 1 ∷ n ∷ []
key1 (oMod n) = 2 ∷ n ∷ []
key1 (oMul n) = 3 ∷ n ∷ []
key1 oHlf     = 4 ∷ []
key1 (oEase _) = 5 ∷ []      -- a hint only: not injective

key2 : Op2 → ℕ
key2 oAdd = 0
key2 oSub = 1
key2 oMax = 2
key2 oMin = 3

key : Node → List ℕ
key (atom a)       = 0 ∷ keyA a
key (un o a)       = 1 ∷ key1 o ++ keyA a
key (bin o a b)    = 2 ∷ key2 o ∷ keyA a ++ keyA b
key (quad a b c d) = 3 ∷ keyA a ++ keyA b ++ keyA c ++ keyA d

KeyOrder = Lex.<-strictTotalOrder ℕP.<-strictTotalOrder
module M  = AVLMap KeyOrder

-- `defs` are the definitions, the newest first (the oldest is number 0, and the newest is number
-- `size - 1`); `memo` maps the key of a node to the node and the number of its definition
record St : Set where
  field
    size : ℕ
    defs : List Node
    memo : M.Map (Node × ℕ)
open St

emptySt : St
emptySt = record { size = 0 ; defs = [] ; memo = M.empty }

-- define a node
fresh : Node → St → Arg × St
fresh nd st = aref (size st) ,
  record { size = suc (size st) ; defs = nd ∷ defs st ; memo = M.insert (key nd) (nd , size st) (memo st) }

-- the reference to the definition of a node: the existing one if the memo finds it (and the
-- definition it names is that node), else a new one
intern : Node → St → Arg × St
intern nd st with M.lookup (memo st) (key nd)
... | nothing          = fresh nd st
... | just (nd′ , i) with node≟ nd′ nd
...   | yes _ = aref i , st
...   | no  _ = fresh nd st

-- a computation in the store
Sh : Set → Set
Sh A = St → A × St

-- (Each intermediate result is a *parameter* of a helper, not a `let`: the compiled code shares
-- a parameter, and recomputes a `let`-bound application at each use, which is exponential in
-- the depth of the formula.)
un¹ : Op1 → Sh Arg → Sh Arg
un¹ o f st = un¹′ o (f st)
  where un¹′ : Op1 → Arg × St → Arg × St
        un¹′ o r = intern (un o (proj₁ r)) (proj₂ r)

bin² : Op2 → Sh Arg → Sh Arg → Sh Arg
bin² o f g st = step₁ (f st)
  where
    step₂ : Arg × St → Arg × St → Arg × St
    step₂ r₁ r₂ = intern (bin o (proj₁ r₁) (proj₁ r₂)) (proj₂ r₂)
    step₁ : Arg × St → Arg × St
    step₁ r₁ = step₂ r₁ (g (proj₂ r₁))

quad⁴ : Sh Arg → Sh Arg → Sh Arg → Sh Arg → Sh Arg
quad⁴ f g h k st = step₁ (f st)
  where
    step₄ : Arg × St → Arg × St → Arg × St → Arg × St → Arg × St
    step₄ r₁ r₂ r₃ r₄ = intern (quad (proj₁ r₁) (proj₁ r₂) (proj₁ r₃) (proj₁ r₄)) (proj₂ r₄)
    step₃ : Arg × St → Arg × St → Arg × St → Arg × St
    step₃ r₁ r₂ r₃ = step₄ r₁ r₂ r₃ (k (proj₂ r₃))
    step₂ : Arg × St → Arg × St → Arg × St
    step₂ r₁ r₂ = step₃ r₁ r₂ (h (proj₂ r₂))
    step₁ : Arg × St → Arg × St
    step₁ r₁ = step₂ r₁ (g (proj₂ r₁))

-- the formula as a reference (a leaf is not defined: it is its own argument)
share : Formula → Sh Arg
share (num n)       st = anum n , st
share (var i)       st = apar i , st
share (add a b)     = bin² oAdd (share a) (share b)
share (sub a b)     = bin² oSub (share a) (share b)
share (max a b)     = bin² oMax (share a) (share b)
share (fmin a b)    = bin² oMin (share a) (share b)
share (pct p a)     = un¹ (oPct p) (share a)
share (hlf a)       = un¹ oHlf (share a)
share (fdiv d a)    = un¹ (oDiv d) (share a)
share (fmod d a)    = un¹ (oMod d) (share a)
share (fmul n a)    = un¹ (oMul n) (share a)
share (fease e a)   = un¹ (oEase e) (share a)
share (flt a b x y) = quad⁴ (share a) (share b) (share x) (share y)

-- the output of a coordinate: the root of a position is a half (`Slides.Anim.Formula.half`) and
-- is not defined, the rest is a reference
output : Formula → Sh Node
output (hlf a) st = hlfOut (share a st)
  where hlfOut : Arg × St → Node × St
        hlfOut r = un oHlf (proj₁ r) , proj₂ r
output g       st = atomOut (share g st)
  where atomOut : Arg × St → Node × St
        atomOut r = atom (proj₁ r) , proj₂ r

-- the definitions as the page evaluates them: in order, the oldest first
program : St → List Node
program st = reverse (defs st)

-- sharing through one store across the parts of a structure
traverseL : ∀ {X Y : Set} → (X → Sh Y) → List X → Sh (List Y)
traverseL f []       st = [] , st
traverseL f (x ∷ xs) st = step₁ (f x st)
  where
    step₂ : _ → _ → _
    step₂ r₁ r₂ = proj₁ r₁ ∷ proj₁ r₂ , proj₂ r₂
    step₁ : _ → _
    step₁ r₁ = step₂ r₁ (traverseL f xs (proj₂ r₁))

traverseM : ∀ {X Y : Set} → (X → Sh Y) → Maybe X → Sh (Maybe Y)
traverseM f nothing  st = nothing , st
traverseM f (just x) st = wrap (f x st)
  where wrap : _ → _
        wrap r = just (proj₁ r) , proj₂ r
