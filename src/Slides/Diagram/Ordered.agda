{-# OPTIONS --safe --without-K #-}

-- The ordered layers of the scalar signature: one language of time-varying scalars.
--
-- `Slides.Diagram.Expr` has two layers (core, sub) read in ℕ and in ℚ; `Slides.Diagram.Euclid` adds
-- a third, read in ℕ only, so that discrete templates and continuous ones are two languages.  Here
-- the same operations get a meaning in any scalar that supports them, and `Ease` joins them:
--
--     QC = ExprC ⊎ OrdC ⊎ FloorC ⊎ EaseC          QExpr V = Term QC V = QC ⋆ V
--
--     Ord    OrdC    Lt a b x y   `x` if a < b else `y` (one-sorted: no Bool)    Min a b
--     Floor  FloorC  DivBy d x    ⌊x / (d+1)⌋          ModBy d x   x − (d+1)·⌊x/(d+1)⌋
--                    MulLit n x   n · x
--     Ease   EaseC   Ease e x     `Slides.Anim.Track.progress e x`
--
-- Time is a parameter (`docs/Time.md` §7): a *model* is a scalar `S` with a `QOps S` (the operations
-- of every layer, each layer its own record, the sum read by the copairing `Signature._⊕_`) and, for
-- what the proofs need, the laws `QLaws` the operations satisfy.  ℚ is the first model (`ratQ`,
-- `ratQLaws`); ℕ is the tick clock and reads the core, sub, Ord and Floor layers (`Properties`:
-- `natOrd`, `natFloor`, joined to `ι : ℕ → ℚ` by `IsOrdHom`, `IsFloorHom`).  A lemma names the layers
-- it uses; a fact about a model beyond the laws (density, induction) is a hypothesis of the lemma.
--
-- Substitution is `_>>=_` of the free monad (`Properties.Laws`): delay, stretch, loop, hold are
-- Kleisli arrows.  A discrete template is a lowered term: `lowerQ` sends the two nodes whose ℕ
-- reading differs from the ℚ one (monus, percentage) to programs that compute the ℕ value.

module Slides.Diagram.Ordered where

open import Data.Bool using (Bool; not; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer as ℤ using (ℤ)
import Data.Integer.DivMod as ℤ
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_,_)
open import Data.Rational as ℚ using (ℚ)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (Container; _▷_; _⇒_; shape; position)
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Container.Pick using (pick2; pick4)
open import Container.Lowering using (Lowering; lower; translate)
open import Slides.Cong using (cong₄)

open import Slides.Diagram.Scalar
open import Slides.Diagram.Signature
open import Slides.Diagram.Expr
import Slides.Diagram.Euclid as E
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

-- a scalar with every layer
record QOps (S : Set) : Set where
  field
    ops   : Ops S
    ord   : OrdOps S
    floor : FloorOps S
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

-- the signature of time-varying scalars
QC : Sig
QC = ExprC ⊎ (OrdC ⊎ (FloorC ⊎ EaseC))

QExpr : Set → Set
QExpr V = Term QC V

ordQ : OrdC ⇒ QC
ordQ = record { shape = λ o → inj₂ (inj₁ o) ; position = λ q → q }

floorQ : FloorC ⇒ QC
floorQ = record { shape = λ o → inj₂ (inj₂ (inj₁ o)) ; position = λ q → q }

easeQ : EaseC ⇒ QC
easeQ = record { shape = λ o → inj₂ (inj₂ (inj₂ o)) ; position = λ q → q }

coreQ : CoreC ⇒ QC
coreQ = record { shape = λ o → inj₁ (inj₁ o) ; position = λ q → q }

subQ : SubC ⇒ QC
subQ = record { shape = λ o → inj₁ (inj₂ o) ; position = λ q → q }

-- smart constructors
open CoreSyntax coreQ public renaming (zero′ to zeroQ; lit to litQ; _⊞_ to _⊞ᵠ_; _⊓_ to _⊔ᵠ_; pct to pctQ; termCore to termCoreQ)
open SubSyntax subQ public renaming (_⊖_ to _⊖ᵠ_; termSub to termSubQ)

ltQ : ∀ {V} → QExpr V → QExpr V → QExpr V → QExpr V → QExpr V
ltQ a b x y = impure (shape ordQ Lt , λ q → pick4 a b x y (position ordQ {Lt} q))

minQ : ∀ {V} → QExpr V → QExpr V → QExpr V
minQ a b = impure (shape ordQ Min , λ q → pick2 a b (position ordQ {Min} q))

divByQ modByQ mulLitQ : ∀ {V} → ℕ → QExpr V → QExpr V
divByQ d a  = impure (shape floorQ (DivBy d) , λ _ → a)
modByQ d a  = impure (shape floorQ (ModBy d) , λ _ → a)
mulLitQ n a = impure (shape floorQ (MulLit n) , λ _ → a)

-- `Ease e a`: the easing `e` applied to the progress `a`
easeT : ∀ {V} → Easing → QExpr V → QExpr V
easeT e a = impure (shape easeQ (Ease e) , λ _ → a)

-- the time
tQ : QExpr ⊤
tQ = pure tt

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

qH : ∀ {S} → QOps S → Handler QC S
qH Q = opsH (QOps.ops Q) ⊕ (ordH (QOps.ord Q) ⊕ (floorH (QOps.floor Q) ⊕ easeH (QOps.easeO Q)))

-- evaluation: the fold, into any scalar with all four layers
evalQ : ∀ {V S} → QOps S → (V → S) → QExpr V → S
evalQ Q = foldT (qH Q)

------------------------------------------------------------------------
-- The reading in ℚ

-- strict comparison
_<ᵇ_ : ℚ → ℚ → Bool
a <ᵇ b = not (b ℚ.≤ᵇ a)

fromℤ : ℤ → ℚ
fromℤ z = z ℚ./ 1

ratOrd : OrdOps ℚ
ratOrd = record { lt = λ a b x y → if a <ᵇ b then x else y ; min = ℚ._⊓_ }

ratFloor : FloorOps ℚ
ratFloor = record
  { divBy  = λ d x → fromℤ (ℚ.floor x ℤ./ ℤ.+ ℕ.suc d)
  ; modBy  = λ d x → x ℚ.- (ℤ.+ ℕ.suc d ℚ./ 1) ℚ.* fromℤ (ℚ.floor x ℤ./ ℤ.+ ℕ.suc d)
  ; mulLit = λ n x → (ℤ.+ n ℚ./ 1) ℚ.* x }

-- `Ease` is the progress function of `Slides.Anim.Track`, unchanged
ratEase : EaseOps ℚ
ratEase = record { ease = progress }

ratQ : QOps ℚ
ratQ = record { ops = ratOps ; ord = ratOrd ; floor = ratFloor ; easeO = ratEase }

------------------------------------------------------------------------
-- The laws of a model

-- `ModBy` and `Min` are definable from the other operations (layers: Floor + Sub, Ord): a model
-- satisfies the laws iff it reads them so.  They stay primitive in the signature (one node
-- each on the page), and `Properties.Laws` derives from the laws the definitions of the nodes.
record QLaws {S : Set} (Q : QOps S) : Set where
  private
    module O = Ops (QOps.ops Q)
    module Or = OrdOps (QOps.ord Q)
    module F = FloorOps (QOps.floor Q)
  field
    modBy-spec : ∀ d x → F.modBy d x ≡ x O.- F.mulLit (ℕ.suc d) (F.divBy d x)
    min-spec   : ∀ a b → Or.min a b ≡ Or.lt a b a b

------------------------------------------------------------------------
-- Discrete templates are ordered ones: the lowering

-- The discrete reading as a *lowering* (a Kleisli map, `Container.Lowering`): the nodes that are
-- not the same in ℕ and ℚ are sent to programs that compute the ℕ value in ℚ, so no side
-- condition is left (`Properties.Discrete.discrete-is-ordered`).  The monus is `max (a − b) 0` (real subtraction clamped) and a percentage
-- is `⌊p·x / 100⌋`; every other node is its namesake.
lowerD : Lowering E.DExprC QC
lowerD (inj₁ (inj₁ Zero))    = impure (inj₁ (inj₁ Zero) , λ ())
lowerD (inj₁ (inj₁ (Lit n))) = impure (inj₁ (inj₁ (Lit n)) , λ ())
lowerD (inj₁ (inj₁ Plus))    = impure (inj₁ (inj₁ Plus) , pure)
lowerD (inj₁ (inj₁ Max))     = impure (inj₁ (inj₁ Max) , pure)
lowerD (inj₁ (inj₁ (Pct p))) = divByQ 99 (mulLitQ p (pure tt))
lowerD (inj₁ (inj₂ Sub))     = impure (inj₁ (inj₁ Max) , pick2 (impure (inj₁ (inj₂ Sub) , pure)) zeroQ)
lowerD (inj₂ (E.DivBy d))      = impure (inj₂ (inj₂ (inj₁ (DivBy d))) , pure)
lowerD (inj₂ (E.ModBy d))      = impure (inj₂ (inj₂ (inj₁ (ModBy d))) , pure)
lowerD (inj₂ (E.MulLit n))     = impure (inj₂ (inj₂ (inj₁ (MulLit n))) , pure)
lowerD (inj₂ E.Lt)             = impure (inj₂ (inj₁ Lt) , pure)

lowerQ : ∀ {V} → E.DExpr V → QExpr V
lowerQ = lower lowerD
