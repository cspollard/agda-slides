{-# OPTIONS --safe --without-K #-}

-- The Euclidean layer: discrete expressions of the tick.
--
-- Some animations are not paths in a continuum.  A "flipbook" body such as the drifting point
-- pairs (`Slides.Examples.PairsHero`) is a function of the *integer tick* `t`: a triangle wave
-- `tri t = let m = t % 64 in if m < 33 then m else 64 ∸ m`, an angle `(t / 4) % 8`, a table
-- lookup, a product with a constant.  Nothing in it is meaningful between two ticks, and
-- floor division is not exact division, so these operations cannot live in the layers of
-- `Slides.Diagram.Expr` (which are read in ℕ *and* in ℚ, `Slides.Diagram.ExprQ`).  They get
-- a layer of their own, read in ℕ only:
--
--     EuclidC = EuclidOp ▷ euclidArity
--         DivBy d x      x / (d+1)     (the divisor is `suc d`: never zero, no side condition)
--         ModBy d x      x % (d+1)
--         Lt a b x y     if a < b then x else y      (one-sorted: the four are scalars)
--         MulLit n x     n · x                       (a literal factor)
--     DExprC  = ExprC ⊎ EuclidC       core, sub, euclid
--
-- A term over `DExprC` is a *discrete template*; over `ExprC` a continuous one.  They are
-- different types, so a formula that needs floor division cannot be evaluated in ℚ by
-- mistake: `evalD` needs the algebra of all three layers (`DiscreteOps`), which only ℕ has
-- (`natD`).  `MulLit` is a ring operation valid in every scalar; it is here because nothing
-- in the continuous reading uses it, and adding it to `CoreOps` would change every scalar
-- and the continuous proofs for no gain.
--
-- The layers compose as sums of containers (`Slides.Diagram.Signature`), and everything the
-- layout needs is in the core and sub layers, so a layout in `DExpr V` is the layout of
-- `Slides.Diagram.Layout` in the scalar `dexprOps` (`Ops` from the first two layers): the
-- Euclidean operations only occur *inside the scalars*, as leaves' formulas (`Place` never
-- compares or divides: it takes sums, differences, maxima and percentages).  So
-- `Slides.Diagram.LayoutNatural` applies unchanged along `evalD` (`evalD-hom`).
--
-- As in `Slides.Diagram.Expr`: `DExpr V` is the free algebra (`foldT`), `substD` the
-- fold into the term algebra, `evalD-substD` evaluation after substitution, and the weakening
-- `weakenE : Expr V → DExpr V` (a monad morphism, `Slides.Diagram.Signature.weaken-bind`)
-- evaluates to the original (`evalD-weaken`): a continuous template is a discrete one, read in ℕ.

module Slides.Diagram.Euclid where

open import Level using (0ℓ)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat as ℕ using (ℕ; NonZero; _/_; _%_; _<ᵇ_; _*_)
open import Data.Bool using (if_then_else_)
open import Data.Product using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (Container; Shape; Position; _▷_; _⇒_; shape; position)
open import Data.Container.Combinator using (_⊎_)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Container.Lowering using (translate)
open import Container.Sum using (inl; inr)

open import Slides.Diagram.Scalar
open import Slides.Diagram.Signature
open import Slides.Diagram.Expr

------------------------------------------------------------------------
-- The layer

record EuclidOps (S : Set) : Set where
  field
    divBy  : ℕ → S → S                -- `divBy d x`: x / (d+1), rounded down
    modBy  : ℕ → S → S                -- `modBy d x`: x % (d+1)
    lt     : S → S → S → S → S        -- `lt a b x y`: x if a < b, else y
    mulLit : ℕ → S → S                -- `mulLit n x`: n · x

-- the scalars with all three layers
record DiscreteOps (S : Set) : Set where
  field
    ops    : Ops S
    euclid : EuclidOps S

natEuclid : EuclidOps ℕ
natEuclid = record
  { divBy = λ d x → x / ℕ.suc d ; modBy = λ d x → x % ℕ.suc d
  ; lt = λ a b x y → if a <ᵇ b then x else y ; mulLit = _*_ }

natD : DiscreteOps ℕ
natD = record { ops = natOps ; euclid = natEuclid }

data EuclidOp : Set where
  DivBy ModBy MulLit : ℕ → EuclidOp
  Lt                 : EuclidOp

euclidArity : EuclidOp → Set
euclidArity (DivBy _)  = ⊤
euclidArity (ModBy _)  = ⊤
euclidArity (MulLit _) = ⊤
euclidArity Lt         = Fin 4

EuclidC : Sig
EuclidC = EuclidOp ▷ euclidArity

-- the signature of discrete templates
DExprC : Sig
DExprC = ExprC ⊎ EuclidC

DExpr : Set → Set
DExpr V = Term DExprC V

------------------------------------------------------------------------
-- Inclusions

coreD : CoreC ⇒ DExprC
coreD = record { shape = λ o → inj₁ (inj₁ o) ; position = λ q → q }

subD : SubC ⇒ DExprC
subD = record { shape = λ o → inj₁ (inj₂ o) ; position = λ q → q }

euclidD : EuclidC ⇒ DExprC
euclidD = record { shape = λ o → inj₂ o ; position = λ q → q }

exprD : ExprC ⇒ DExprC
exprD = inl {C₁ = ExprC} {C₂ = EuclidC}

private
  pick4 : ∀ {A : Set} → A → A → A → A → Fin 4 → A
  pick4 a b c d zero                = a
  pick4 a b c d (suc zero)          = b
  pick4 a b c d (suc (suc zero))    = c
  pick4 a b c d (suc (suc (suc zero))) = d
  pick4 a b c d (suc (suc (suc (suc ()))))

module EuclidSyntax {Σ : Sig} (i : EuclidC ⇒ Σ) where
  -- `divBy d x` is `x / (d+1)`
  divBy modBy : ∀ {V} → ℕ → Term Σ V → Term Σ V
  divBy d a = impure (shape i (DivBy d) , λ _ → a)
  modBy d a = impure (shape i (ModBy d) , λ _ → a)

  mulLit : ∀ {V} → ℕ → Term Σ V → Term Σ V
  mulLit n a = impure (shape i (MulLit n) , λ _ → a)

  -- `ltT a b x y`: if a < b then x else y
  ltT : ∀ {V} → Term Σ V → Term Σ V → Term Σ V → Term Σ V → Term Σ V
  ltT a b x y = impure (shape i Lt , λ q → pick4 a b x y (position i q))

  termEuclid : ∀ {V} → EuclidOps (Term Σ V)
  termEuclid = record { divBy = divBy ; modBy = modBy ; lt = ltT ; mulLit = mulLit }

open EuclidSyntax euclidD public
open CoreSyntax coreD public
  renaming (zero′ to zeroD; lit to litD; _⊞_ to _⊞ᴰ_; _⊓_ to _⊓ᴰ_; pct to pctD; termCore to termCoreD)
open SubSyntax subD public renaming (_⊖_ to _⊖ᴰ_; termSub to termSubD)

------------------------------------------------------------------------
-- Interpretation: the Euclidean handler, copaired with the Expr one

euclidH : ∀ {S} → EuclidOps S → Handler EuclidC S
euclidH O .Handler.handle (DivBy d)  k = EuclidOps.divBy O d (k tt)
euclidH O .Handler.handle (ModBy d)  k = EuclidOps.modBy O d (k tt)
euclidH O .Handler.handle (MulLit n) k = EuclidOps.mulLit O n (k tt)
euclidH O .Handler.handle Lt         k =
  EuclidOps.lt O (k zero) (k (suc zero)) (k (suc (suc zero))) (k (suc (suc (suc zero))))
euclidH O .Handler.respects (DivBy d)  e = cong (EuclidOps.divBy O d) (e tt)
euclidH O .Handler.respects (ModBy d)  e = cong (EuclidOps.modBy O d) (e tt)
euclidH O .Handler.respects (MulLit n) e = cong (EuclidOps.mulLit O n) (e tt)
euclidH O .Handler.respects Lt e =
  cong₄ (EuclidOps.lt O) (e zero) (e (suc zero)) (e (suc (suc zero))) (e (suc (suc (suc zero))))
  where cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a a′ b b′ c c′ d d′} →
                a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → f a b c d ≡ f a′ b′ c′ d′
        cong₄ f refl refl refl refl = refl

dH : ∀ {S} → DiscreteOps S → Handler DExprC S
dH D = opsH (DiscreteOps.ops D) ⊕ euclidH (DiscreteOps.euclid D)

-- evaluation of a discrete template: the fold, only into scalars with all three layers
evalD : ∀ {V S} → DiscreteOps S → (V → S) → DExpr V → S
evalD D = foldT (dH D)

------------------------------------------------------------------------
-- Weakening: a continuous template is a discrete one

weakenE : ∀ {V} → Expr V → DExpr V
weakenE = translate exprD

-- read with the operations of the first two layers only
evalD-weaken : ∀ {V S} (D : DiscreteOps S) (ρ : V → S) (e : Expr V) →
               evalD D ρ (weakenE e) ≡ evalWith (DiscreteOps.ops D) ρ e
evalD-weaken D ρ e =
  trans (foldT-translate exprD (dH D) ρ e) (foldT-ext _ _ (λ s k → refl) ρ e)

------------------------------------------------------------------------
-- The `Ops` structure of discrete templates

dexprOps : ∀ {V} → Ops (DExpr V)
dexprOps = record { core = termCoreD ; sub = termSubD ; toℕ = evalD natD (λ _ → 0) }

dexprD : ∀ {V} → DiscreteOps (DExpr V)
dexprD = record { ops = dexprOps ; euclid = termEuclid }

-- homomorphisms of the Euclidean layer
record IsEuclidHom {S T : Set} (O : EuclidOps S) (P : EuclidOps T) (h : S → T) : Set where
  private module O = EuclidOps O
  private module P = EuclidOps P
  field
    h-divBy  : ∀ d a → h (O.divBy d a) ≡ P.divBy d (h a)
    h-modBy  : ∀ d a → h (O.modBy d a) ≡ P.modBy d (h a)
    h-mulLit : ∀ n a → h (O.mulLit n a) ≡ P.mulLit n (h a)
    h-lt     : ∀ a b x y → h (O.lt a b x y) ≡ P.lt (h a) (h b) (h x) (h y)

-- `evalD` is a homomorphism of all three layers, by construction
evalD-hom : ∀ {V S} (D : DiscreteOps S) (ρ : V → S) →
            IsOpsHom dexprOps (DiscreteOps.ops D) (evalD D ρ)
evalD-hom D ρ = record
  { coreHom = record
      { h-0 = refl ; h-+ = λ _ _ → refl ; h-⊔ = λ _ _ → refl
      ; h-fromℕ = λ _ → refl ; h-percentOf = λ _ _ → refl }
  ; subHom = record { h-- = λ _ _ → refl } }

evalD-euclid-hom : ∀ {V S} (D : DiscreteOps S) (ρ : V → S) →
                   IsEuclidHom termEuclid (DiscreteOps.euclid D) (evalD D ρ)
evalD-euclid-hom D ρ = record
  { h-divBy = λ _ _ → refl ; h-modBy = λ _ _ → refl ; h-mulLit = λ _ _ → refl ; h-lt = λ _ _ _ _ → refl }

evalD-hom-ℕ : ∀ {V} (ρ : V → ℕ) → IsOpsHom dexprOps natOps (evalD natD ρ)
evalD-hom-ℕ = evalD-hom natD

-- substitution, as the fold into the term algebra
substD : ∀ {V W} → (V → DExpr W) → DExpr V → DExpr W
substD {W = W} σ = evalD (dexprD {W}) σ

renameD : ∀ {V W} → (V → W) → DExpr V → DExpr W
renameD f = substD (λ v → pure (f v))

substD-hom : ∀ {V W} (σ : V → DExpr W) → IsOpsHom dexprOps dexprOps (substD σ)
substD-hom σ = evalD-hom dexprD σ

nodeD : ∀ {W S} (D : DiscreteOps S) (ρ : W → S) (s : Shape DExprC) (k : Position DExprC s → DExpr W) →
        evalD D ρ (dH (dexprD {W}) .Handler.handle s k) ≡ dH D .Handler.handle s (λ q → evalD D ρ (k q))
nodeD D ρ (inj₁ (inj₁ Zero))     k = refl
nodeD D ρ (inj₁ (inj₁ (Lit n)))  k = refl
nodeD D ρ (inj₁ (inj₁ Plus))     k = refl
nodeD D ρ (inj₁ (inj₁ Max))      k = refl
nodeD D ρ (inj₁ (inj₁ (Pct p)))  k = refl
nodeD D ρ (inj₁ (inj₂ Sub))      k = refl
nodeD D ρ (inj₂ (DivBy d))       k = refl
nodeD D ρ (inj₂ (ModBy d))       k = refl
nodeD D ρ (inj₂ (MulLit n))      k = refl
nodeD D ρ (inj₂ Lt)              k = refl

-- evaluating after substituting is evaluating with the evaluated substitution
evalD-substD : ∀ {V W S} (D : DiscreteOps S) (ρ : W → S) (σ : V → DExpr W) (e : DExpr V) →
               evalD D ρ (substD σ e) ≡ evalD D (λ v → evalD D ρ (σ v)) e
evalD-substD D ρ σ (pure v)         = refl
evalD-substD D ρ σ (impure (s , k)) =
  trans (nodeD D ρ s (λ q → substD σ (k q)))
        (dH D .Handler.respects s (λ q → evalD-substD D ρ σ (k q)))
