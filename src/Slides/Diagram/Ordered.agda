{-# OPTIONS --safe --without-K #-}

-- The ordered layers of the scalar signature: one language of time-varying scalars.
--
-- `Slides.Diagram.Expr` has two layers (core, sub), read in ℕ and in ℚ.  Two more are added, each
-- with its own record of operations and its own signature, the sum read by the copairing of the
-- handlers (`Signature._⊕_`):
--
--     Ord    OrdC    Lt a b x y   `x` if a < b else `y` (one-sorted: no Bool)    Min a b
--     Floor  FloorC  DivBy d x    ⌊x / (d+1)⌋          ModBy d x   x − (d+1)·⌊x/(d+1)⌋
--                    MulLit n x   n · x
--     Ease   EaseC   Ease e x     `Slides.Anim.Track.progress e x`
--
--     OC = ExprC ⊎ OrdC ⊎ FloorC     the layers both clocks read:  OExpr V = Term OC V = OC ⋆ V
--     QC = OC ⊎ EaseC                ... and the one only ℚ reads:  QExpr V = Term QC V
--
-- Time is a parameter (`docs/Time.md` §7): a *model* is a scalar `S` with an `OOps S` (core, sub,
-- Ord, Floor; ℕ and ℚ have one: `natO`, `ratO`) or a `QOps S` (and Ease: ℚ only, `ratQ`) and, for
-- what the proofs need, the laws `QLaws` the operations satisfy (`ratQLaws`).  A lemma names the
-- layers it uses; a fact about a model beyond the laws (density, induction) is a hypothesis of the
-- lemma.  ℕ is the tick clock, read through `ι : ℕ → ℚ` (`Properties`: `IsOrdHom`, `IsFloorHom`).
--
-- Substitution is `_>>=_` of the free monad (`Properties.Laws`): delay, stretch, loop, hold are
-- Kleisli arrows.  A discrete template is a lowered term: `lowerO` sends the two nodes whose ℕ
-- reading differs from the ℚ one (monus, percentage) to programs that compute the ℕ value.

module Slides.Diagram.Ordered where

open import Data.Bool using (Bool; not; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer as ℤ using (ℤ)
import Data.Integer.DivMod as ℤ
open import Data.Nat as ℕ using (ℕ; _/_; _%_)
open import Data.Product using (_,_)
open import Data.Rational as ℚ using (ℚ)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (_▷_; _⇒_; shape; position)
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Container.Pick using (pick2; pick4)
open import Container.Lowering using (Lowering; lower; ret; translate)
open import Container.Sum using (inl; inr)
open import Slides.Cong using (cong₄)

open import Slides.Diagram.Scalar
open import Slides.Diagram.Signature
open import Slides.Diagram.Expr using (CoreC; SubC; ExprC; opsH; Pct; Sub; module CoreSyntax; module SubSyntax)
open import Slides.Anim.Track using (Easing; progress)

------------------------------------------------------------------------
-- The operations of the layers

record OrdOps (S : Set) : Set where
  field
    lt  : S → S → S → S → S      -- `lt a b x y`: x if a < b, else y
    min : S → S → S

record FloorOps (S : Set) : Set where
  field
    divBy  : ℕ → S → S           -- `divBy d x`: ⌊x / (d+1)⌋
    modBy  : ℕ → S → S           -- `modBy d x`: x − (d+1)·⌊x / (d+1)⌋
    mulLit : ℕ → S → S           -- `mulLit n x`: n · x

record EaseOps (S : Set) : Set where
  field
    ease : Easing → S → S

-- a scalar with the layers both clocks read
record OOps (S : Set) : Set where
  field
    ops   : Ops S
    ord   : OrdOps S
    floor : FloorOps S

-- ... and the one only ℚ reads
record QOps (S : Set) : Set where
  field
    o     : OOps S
    easeO : EaseOps S

------------------------------------------------------------------------
-- The signatures

data OrdOp : Set where
  Lt Min : OrdOp

ordArity : OrdOp → Set
ordArity Lt  = Fin 4
ordArity Min = Fin 2

OrdC : Sig
OrdC = OrdOp ▷ ordArity

data FloorOp : Set where
  DivBy ModBy MulLit : ℕ → FloorOp

floorArity : FloorOp → Set
floorArity _ = ⊤

FloorC : Sig
FloorC = FloorOp ▷ floorArity

data EaseOp : Set where
  Ease : Easing → EaseOp

easeArity : EaseOp → Set
easeArity _ = ⊤

EaseC : Sig
EaseC = EaseOp ▷ easeArity

OC QC : Sig
OC = ExprC ⊎ (OrdC ⊎ FloorC)
QC = OC ⊎ EaseC

OExpr QExpr : Set → Set
OExpr V = Term OC V
QExpr V = Term QC V

coreO : CoreC ⇒ OC
coreO = record { shape = λ o → inj₁ (inj₁ o) ; position = λ q → q }

subO : SubC ⇒ OC
subO = record { shape = λ o → inj₁ (inj₂ o) ; position = λ q → q }

ordO : OrdC ⇒ OC
ordO = record { shape = λ o → inj₂ (inj₁ o) ; position = λ q → q }

floorO : FloorC ⇒ OC
floorO = record { shape = λ o → inj₂ (inj₂ o) ; position = λ q → q }

------------------------------------------------------------------------
-- Constructors, for any signature containing the layers

module OrdSyntax {Σ : Sig} (i : OrdC ⇒ Σ) where
  -- `ltT a b x y`: if a < b then x else y
  ltT : ∀ {V} → Term Σ V → Term Σ V → Term Σ V → Term Σ V → Term Σ V
  ltT a b x y = impure (shape i Lt , λ q → pick4 a b x y (position i q))

  minT : ∀ {V} → Term Σ V → Term Σ V → Term Σ V
  minT a b = impure (shape i Min , λ q → pick2 a b (position i q))

  termOrd : ∀ {V} → OrdOps (Term Σ V)
  termOrd = record { lt = ltT ; min = minT }

module FloorSyntax {Σ : Sig} (i : FloorC ⇒ Σ) where
  divBy modBy mulLit : ∀ {V} → ℕ → Term Σ V → Term Σ V
  divBy d a  = impure (shape i (DivBy d) , λ _ → a)
  modBy d a  = impure (shape i (ModBy d) , λ _ → a)
  mulLit n a = impure (shape i (MulLit n) , λ _ → a)

  termFloor : ∀ {V} → FloorOps (Term Σ V)
  termFloor = record { divBy = divBy ; modBy = modBy ; mulLit = mulLit }

open OrdSyntax ordO public
open FloorSyntax floorO public
open CoreSyntax coreO public
open SubSyntax subO public

-- `Ease e a`: the easing `e` applied to the progress `a`
easeT : ∀ {V} → Easing → QExpr V → QExpr V
easeT e a = impure (shape (inr {C₁ = OC} {C₂ = EaseC}) (Ease e) , λ _ → a)

-- a term of `OC` is a term of `QC`
weakenQ : ∀ {V} → OExpr V → QExpr V
weakenQ = translate (inl {C₁ = OC} {C₂ = EaseC})

-- the time
tO : OExpr ⊤
tO = pure tt

------------------------------------------------------------------------
-- Handlers, one per layer, copaired

ordH : ∀ {S} → OrdOps S → Handler OrdC S
ordH O .Handler.handle Lt  k = OrdOps.lt O (k zero) (k (suc zero)) (k (suc (suc zero))) (k (suc (suc (suc zero))))
ordH O .Handler.handle Min k = OrdOps.min O (k zero) (k (suc zero))
ordH O .Handler.respects Lt  e = cong₄ (OrdOps.lt O) (e zero) (e (suc zero)) (e (suc (suc zero))) (e (suc (suc (suc zero))))
ordH O .Handler.respects Min e = cong₂ (OrdOps.min O) (e zero) (e (suc zero))

floorH : ∀ {S} → FloorOps S → Handler FloorC S
floorH O .Handler.handle (DivBy d)  k = FloorOps.divBy O d (k tt)
floorH O .Handler.handle (ModBy d)  k = FloorOps.modBy O d (k tt)
floorH O .Handler.handle (MulLit n) k = FloorOps.mulLit O n (k tt)
floorH O .Handler.respects (DivBy d)  e = cong (FloorOps.divBy O d) (e tt)
floorH O .Handler.respects (ModBy d)  e = cong (FloorOps.modBy O d) (e tt)
floorH O .Handler.respects (MulLit n) e = cong (FloorOps.mulLit O n) (e tt)

easeH : ∀ {S} → EaseOps S → Handler EaseC S
easeH O .Handler.handle (Ease e) k = EaseOps.ease O e (k tt)
easeH O .Handler.respects (Ease e) h = cong (EaseOps.ease O e) (h tt)

oH : ∀ {S} → OOps S → Handler OC S
oH O = opsH (OOps.ops O) ⊕ (ordH (OOps.ord O) ⊕ floorH (OOps.floor O))

qH : ∀ {S} → QOps S → Handler QC S
qH Q = oH (QOps.o Q) ⊕ easeH (QOps.easeO Q)

-- evaluation: the fold, into any scalar with the layers
evalO : ∀ {V S} → OOps S → (V → S) → OExpr V → S
evalO O = foldT (oH O)

evalQ : ∀ {V S} → QOps S → (V → S) → QExpr V → S
evalQ Q = foldT (qH Q)

------------------------------------------------------------------------
-- The readings in ℕ and in ℚ

natOrd : OrdOps ℕ
natOrd = record { lt = λ a b x y → if a ℕ.<ᵇ b then x else y ; min = ℕ._⊓_ }

natFloor : FloorOps ℕ
natFloor = record { divBy = λ d x → x / ℕ.suc d ; modBy = λ d x → x % ℕ.suc d ; mulLit = ℕ._*_ }

natO : OOps ℕ
natO = record { ops = natOps ; ord = natOrd ; floor = natFloor }

-- strict comparison
_<ᵇℚ_ : ℚ → ℚ → Bool
a <ᵇℚ b = not (b ℚ.≤ᵇ a)

fromℤ : ℤ → ℚ
fromℤ z = z ℚ./ 1

ratOrd : OrdOps ℚ
ratOrd = record { lt = λ a b x y → if a <ᵇℚ b then x else y ; min = ℚ._⊓_ }

ratFloor : FloorOps ℚ
ratFloor = record
  { divBy  = λ d x → fromℤ (ℚ.floor x ℤ./ ℤ.+ ℕ.suc d)
  ; modBy  = λ d x → x ℚ.- (ℤ.+ ℕ.suc d ℚ./ 1) ℚ.* fromℤ (ℚ.floor x ℤ./ ℤ.+ ℕ.suc d)
  ; mulLit = λ n x → (ℤ.+ n ℚ./ 1) ℚ.* x }

ratO : OOps ℚ
ratO = record { ops = ratOps ; ord = ratOrd ; floor = ratFloor }

-- `Ease` is the progress function of `Slides.Anim.Track`, unchanged
ratEase : EaseOps ℚ
ratEase = record { ease = progress }

ratQ : QOps ℚ
ratQ = record { o = ratO ; easeO = ratEase }

-- the free scalar with the layers of `OC`
termO : ∀ {V} → OOps (OExpr V)
termO = record
  { ops = record { core = termCore ; sub = termSub ; toℕ = evalO natO (λ _ → 0) }
  ; ord = termOrd ; floor = termFloor }

-- Substitution as the fold into the free scalar (`>>=` up to equality of programs): an
-- `Ops`-homomorphism by construction, which is what lets layout commute with it
-- (`Properties.Laws.layout-substO`).
substO : ∀ {V W} → (V → OExpr W) → OExpr V → OExpr W
substO σ = evalO termO σ

-- layout in the free scalar leaves every coordinate a formula
termOps : ∀ {V} → Ops (OExpr V)
termOps = OOps.ops termO

------------------------------------------------------------------------
-- The laws of a model

-- `ModBy` and `Min` are definable from the other operations (layers: Floor + Sub, Ord): a model
-- satisfies the laws iff it reads them so.  They stay primitive in the signature (one node
-- each on the page), and `Properties.Laws` derives from the laws the definitions of the nodes.
record QLaws {S : Set} (O : OOps S) : Set where
  private
    module Sb = Ops (OOps.ops O)
    module Or = OrdOps (OOps.ord O)
    module F = FloorOps (OOps.floor O)
  field
    modBy-spec : ∀ d x → F.modBy d x ≡ x Sb.- F.mulLit (ℕ.suc d) (F.divBy d x)
    min-spec   : ∀ a b → Or.min a b ≡ Or.lt a b a b

------------------------------------------------------------------------
-- Discrete templates are ordered ones: the lowering

-- The nodes that are not the same in ℕ and ℚ are sent to programs that compute the ℕ value in
-- any model, so no side condition is left (`Properties.Discrete.discrete-is-ordered`): the monus
-- `a ∸ b` is `(a ⊔ b) − b` (the minuend is the larger by construction, as in `atop`) and a
-- percentage is `⌊p·x / 100⌋`; every other node is its namesake.
lowerO : Lowering OC OC
lowerO (inj₁ (inj₁ (Pct p))) = divBy 99 (mulLit p (pure tt))
lowerO (inj₁ (inj₂ Sub))     = (pure zero ⊓ pure (suc zero)) ⊖ pure (suc zero)
lowerO s                     = ret s

lowerQ : ∀ {V} → OExpr V → OExpr V
lowerQ = lower lowerO

-- sample-and-hold: the template composed with `τ ↦ ⌊τ⌋`
holdT : OExpr ⊤
holdT = divBy 0 tO
