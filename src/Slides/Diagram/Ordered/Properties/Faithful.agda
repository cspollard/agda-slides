{-# OPTIONS --safe --without-K #-}

-- Where the discrete (ℕ) and the continuous (ℚ) readings of a formula differ.
--
-- A template's sizes are `OExpr`s (`Slides.Diagram.Ordered`).  The deck is laid out in ℕ, whose
-- difference is the monus and whose "p percent of" rounds down; the continuous player
-- (`Slides.Anim.Continuous`) evaluates the same formulas in ℚ (`ratO`), whose difference is
-- real subtraction and whose percentage is exact.  Both are `evalO` of the same free
-- algebra, and layout is natural in each (`Slides.Diagram.Layout.Properties`), so a template's
-- frame in either reading is the evaluation of *one* symbolic layout.  They agree exactly when
-- the ℕ operations were exact, i.e. at the nodes where
--
--   * a difference has its minuend at least its subtrahend (otherwise the monus clamps at 0
--     and the real difference is negative: that frame has a negative size, which `Valid`
--     rules out anyway), and
--   * a percentage divides evenly (otherwise ℕ rounds down).
--
-- Sums, maxima and literals always agree (`Slides.Diagram.NatQ`), and so do the nodes of the
-- ordered layers (`Slides.Diagram.Ordered.Properties`: `ι-ord`, `ι-floor`).  `FaithfulO ρ e` says
-- that every node of `e` is exact at the assignment `ρ`; `faithful` is the theorem that then
-- `ι (evalO natO ρ e) = evalO ratO (ι ∘ ρ) e`, `faithful-layout` its form for the layout of a
-- template.  Lowered terms (`lowerQ`) are faithful at every assignment (`faithful-lower`), and so is
-- a discrete body (`faithful-discrete`): the leaves of a discrete template need no hypothesis, only
-- the layout's own differences do.  Nothing is claimed for an assignment that is not whole: a
-- parameter between two whole numbers has no ℕ value (the discrete reading floors it,
-- `Slides.Anim.Syntax.units`).

module Slides.Diagram.Ordered.Properties.Faithful where

open import Data.Fin using (zero; suc)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.List using ([]; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat as ℕ using (ℕ; _≤_; _*_)
import Data.Nat.Properties as ℕP
import Data.Nat.DivMod as ℕDM
import Data.Integer.Properties as ℤP
import Data.Rational.Properties as ℚP
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Data.Rational.Unnormalised using (*≡*)
open import Data.Integer.Tactic.RingSolver using (solve-∀)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Integer as ℤ using (+_)
open import Data.Rational as ℚ using (ℚ; _/_)
open import Data.Unit using (⊤; tt)
open import Data.Container.Core using (Shape; Position)
open import Data.Container.FreeMonad using (pure; impure; _>>=_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)

open import Slides.Cong using (cong₃; cong₄)
open import Slides.Diagram.Draw
open import Slides.Diagram.Expr using (CoreOp; SubOp; ExprOp; coreArity; subArity; exprArity; Zero; Lit; Plus; Max; Pct; Sub; coreH; subH; opsH)
open import Slides.Diagram.Layout.Properties using (mapLayout-∘)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.NatQ
open import Slides.Diagram.NatQ.Properties
open import Slides.Diagram.Scalar using (Ops; natOps; ratOps)
open import Slides.Diagram.Signature using (Handler; foldT)
open import Slides.Diagram.Syntax using (Dia; mapDia)
open import Slides.Diagram.Ordered
open import Slides.Diagram.Ordered.Properties
open import Slides.Diagram.Ordered.Properties.Laws using (evalO-hom; foldT-bind; layout-evalO)

------------------------------------------------------------------------
-- ι, layer by layer
--
-- `ι : ℕ → ℚ` against the two layers of the scalar (`Slides.Diagram.Scalar`):
--
--   * core: `ι-0` and `ι-fromℕ` hold on the nose, `ι-+` and `ι-⊔` unconditionally
--     (`Slides.Diagram.NatQ`), and the percentage under `Exact%`.  So `ι` is a
--     homomorphism of the core layer on every node whose percentages are exact;
--   * sub: the monus is the difference only where `b ≤ a` (`ι-∸`).
--
-- The side condition of one node, given the ℕ values of its arguments, is `CoreSide` /
-- `SubSide`; those of the sum are copaired like the operations.  `Faithful` is all of the
-- side conditions of a term, and nothing else.

CoreSide : (o : CoreOp) → (coreArity o → ℕ) → Set
CoreSide (Pct p) k = Exact% p (k tt)
CoreSide Zero    k = ⊤
CoreSide (Lit _) k = ⊤
CoreSide Plus    k = ⊤
CoreSide Max     k = ⊤

SubSide : (o : SubOp) → (subArity o → ℕ) → Set
SubSide Sub k = k (suc zero) ≤ k zero

ExprSide : (s : ExprOp) → (exprArity s → ℕ) → Set
ExprSide (inj₁ o) = CoreSide o
ExprSide (inj₂ o) = SubSide o

-- `ι` commutes with the handlers of the core layer where the side condition holds
ι-core : ∀ o (k : coreArity o → ℕ) → CoreSide o k →
         ι (coreH (Ops.core natOps) .Handler.handle o k) ≡ coreH (Ops.core ratOps) .Handler.handle o (λ q → ι (k q))
ι-core Zero     k _  = refl
ι-core (Lit n)  k _  = refl
ι-core Plus     k _  = ι-+ (k zero) (k (suc zero))
ι-core Max      k _  = ι-⊔ (k zero) (k (suc zero))
ι-core (Pct p)  k ex = ex

ι-sub : ∀ o (k : subArity o → ℕ) → SubSide o k →
        ι (subH (Ops.sub natOps) .Handler.handle o k) ≡ subH (Ops.sub ratOps) .Handler.handle o (λ q → ι (k q))
ι-sub Sub k h = ι-∸ (k zero) (k (suc zero)) h

ι-node : ∀ s (k : exprArity s → ℕ) → ExprSide s k →
         ι (opsH natOps .Handler.handle s k) ≡ opsH ratOps .Handler.handle s (λ q → ι (k q))
ι-node (inj₁ o) = ι-core o
ι-node (inj₂ o) = ι-sub o

------------------------------------------------------------------------
-- The side conditions of a term over the ordered layers: those of the core and sub layers only

OSide : (s : Shape OC) → (Position OC s → ℕ) → Set
OSide (inj₁ s) k = ExprSide s k
OSide (inj₂ _) k = ⊤

-- the side condition depends on the values only
OSide-cong : ∀ s {k k′ : Position OC s → ℕ} → (∀ q → k q ≡ k′ q) → OSide s k → OSide s k′
OSide-cong (inj₁ (inj₁ (Pct p))) e ex = subst (Exact% p) (e tt) ex
OSide-cong (inj₁ (inj₂ Sub))     e ex = subst₂ ℕ._≤_ (e (suc zero)) (e zero) ex
OSide-cong (inj₁ (inj₁ Zero))    e ex = tt
OSide-cong (inj₁ (inj₁ (Lit _))) e ex = tt
OSide-cong (inj₁ (inj₁ Plus))    e ex = tt
OSide-cong (inj₁ (inj₁ Max))     e ex = tt
OSide-cong (inj₂ _)              e ex = tt

-- every node of `e` is exact at `ρ`
FaithfulO : ∀ {V} → (V → ℕ) → OExpr V → Set
FaithfulO ρ (pure v)         = ⊤
FaithfulO ρ (impure (s , k)) = (∀ q → FaithfulO ρ (k q)) × OSide s (λ q → evalO natO ρ (k q))

-- `ι` commutes with the handler of a node where its side condition holds
ι-nodeO : ∀ s (k : Position OC s → ℕ) → OSide s k →
          ι (oH natO .Handler.handle s k) ≡ oH ratO .Handler.handle s (λ q → ι (k q))
ι-nodeO (inj₁ s) k ex = ι-node s k ex
ι-nodeO (inj₂ s) k _  = ι-ordfloor s k

-- Exactness gives agreement of the two evaluations.
faithful : ∀ {V} (ρ : V → ℕ) (e : OExpr V) → FaithfulO ρ e → ι (evalO natO ρ e) ≡ evalO ratO (ι ∘ ρ) e
faithful ρ (pure v)         _        = refl
faithful ρ (impure (s , k)) (f , ex) =
  trans (ι-nodeO s (λ q → evalO natO ρ (k q)) ex)
        (oH ratO .Handler.respects s (λ q → faithful ρ (k q) (f q)))

------------------------------------------------------------------------
-- Lowered terms are exact at every assignment

-- exactness is preserved by substitution of exact terms for the variables
faithful->>= : ∀ {V W} (ρ : W → ℕ) (m : OExpr V) (σ : V → OExpr W) →
               FaithfulO (λ v → evalO natO ρ (σ v)) m → (∀ v → FaithfulO ρ (σ v)) → FaithfulO ρ (m >>= σ)
faithful->>= ρ (pure v)         σ _        g = g v
faithful->>= ρ (impure (s , k)) σ (f , ex) g =
  (λ q → faithful->>= ρ (k q) σ (f q) g)
  , OSide-cong s (λ q → sym (foldT-bind (oH natO) ρ σ (k q))) ex

-- the program a node is lowered to is exact at every assignment
faithful-lowerO : ∀ s {ρ′ : Position OC s → ℕ} → FaithfulO ρ′ (lowerO s)
faithful-lowerO (inj₁ (inj₁ (Pct p))) = (λ _ → (λ _ → tt) , tt) , tt
faithful-lowerO (inj₁ (inj₂ Sub))     {ρ′} =
  (λ { zero → (λ { zero → tt ; (suc zero) → tt }) , tt ; (suc zero) → tt }) , ℕP.m≤n⊔m (ρ′ zero) (ρ′ (suc zero))
faithful-lowerO (inj₁ (inj₁ Zero))    = (λ ()) , tt
faithful-lowerO (inj₁ (inj₁ (Lit _))) = (λ ()) , tt
faithful-lowerO (inj₁ (inj₁ Plus))    = (λ _ → tt) , tt
faithful-lowerO (inj₁ (inj₁ Max))     = (λ _ → tt) , tt
faithful-lowerO (inj₂ _)              = (λ _ → tt) , tt

faithful-lower : ∀ {V} (ρ : V → ℕ) (e : OExpr V) → FaithfulO ρ (lowerQ e)
faithful-lower ρ (pure v)         = tt
faithful-lower ρ (impure (s , k)) =
  faithful->>= ρ (lowerO s) (λ q → lowerQ (k q)) (faithful-lowerO s) (λ q → faithful-lower ρ (k q))

-- ... and so is a discrete body: the formulas of `d` lowered and held
faithful-discrete : ∀ (ρ : ⊤ → ℕ) (e : OExpr ⊤) → FaithfulO ρ (lowerQ e >>= λ _ → holdT)
faithful-discrete ρ e = faithful->>= ρ (lowerQ e) (λ _ → holdT) (faithful-lower _ e) (λ _ → (λ _ → tt) , tt)

------------------------------------------------------------------------
-- Layouts: every coordinate exact

AllDraw : ∀ {S} → (S → Set) → Draw S → Set
AllDraw P (rect x y w h _)   = P x × P y × P w × P h
AllDraw P (circle x y r _)   = P x × P y × P r
AllDraw P (line a b c d _)   = P a × P b × P c × P d
AllDraw P (arrow a b c d _)  = P a × P b × P c × P d
AllDraw P (label x y _ _ _)  = P x × P y

AllBox : ∀ {S} → (S → Set) → Box S → Set
AllBox P (box l t w h) = P l × P t × P w × P h

-- the property holds of every scalar a layout is made of
AllLayout : ∀ {S} → (S → Set) → Layout S → Set
AllLayout P l = P (Layout.width l) × P (Layout.height l)
              × All (AllDraw P) (Layout.draws l) × All (λ a → AllBox P (proj₂ a)) (Layout.anchors l)

module _ {S T : Set} {P : S → Set} {f g : S → T} (eq : ∀ x → P x → f x ≡ g x) where

  mapDraw-on : ∀ d → AllDraw P d → mapDraw f d ≡ mapDraw g d
  mapDraw-on (rect x y w h s)  (px , py , pw , ph) =
    cong₄ (λ a b c d → rect a b c d s) (eq x px) (eq y py) (eq w pw) (eq h ph)
  mapDraw-on (circle x y r s)  (px , py , pr) =
    cong₃ (λ a b c → circle a b c s) (eq x px) (eq y py) (eq r pr)
  mapDraw-on (line a b c d s)  (pa , pb , pc , pd) =
    cong₄ (λ p q r t → line p q r t s) (eq a pa) (eq b pb) (eq c pc) (eq d pd)
  mapDraw-on (arrow a b c d s) (pa , pb , pc , pd) =
    cong₄ (λ p q r t → arrow p q r t s) (eq a pa) (eq b pb) (eq c pc) (eq d pd)
  mapDraw-on (label x y n t s) (px , py) =
    cong₂ (λ a b → label a b n t s) (eq x px) (eq y py)

  mapAnchor-on : ∀ a → AllBox P (proj₂ a) → mapAnchor f a ≡ mapAnchor g a
  mapAnchor-on (n , box l t w h) (pl , pt , pw , ph) =
    cong₄ (λ a b c d → n , box a b c d) (eq l pl) (eq t pt) (eq w pw) (eq h ph)

  map-on : ∀ {A B : Set} {Q : A → Set} {u v : A → B} → (∀ x → Q x → u x ≡ v x) →
           ∀ xs → All Q xs → map u xs ≡ map v xs
  map-on e []       []         = refl
  map-on e (x ∷ xs) (q ∷ qs)   = cong₂ _∷_ (e x q) (map-on e xs qs)

  -- two maps that agree on the scalars a layout is made of give the same layout
  mapLayout-on : ∀ l → AllLayout P l → mapLayout f l ≡ mapLayout g l
  mapLayout-on l (pw , ph , pds , pas) =
    cong₄ layout (eq _ pw) (eq _ ph) (map-on mapDraw-on (Layout.draws l) pds)
                  (map-on mapAnchor-on (Layout.anchors l) pas)

-- Discrete and continuous frames of a template agree when its layout is exact: sending the ℕ
-- frame through `ι` is the ℚ frame at the parameter `ι ∘ ρ`.
faithful-layout : ∀ {V} (ρ : V → ℕ) (d : Dia (OExpr V)) →
  AllLayout (FaithfulO ρ) (LayoutWith.layout termOps d) →
  mapLayout ι (LayoutWith.layout natOps (mapDia (evalO natO ρ) d))
  ≡ LayoutWith.layout ratOps (mapDia (evalO ratO (ι ∘ ρ)) d)
faithful-layout ρ d ok =
  trans (cong (mapLayout ι) (sym (layout-evalO natO ρ d)))
 (trans (mapLayout-∘ ι (evalO natO ρ) L)
 (trans (mapLayout-on (λ x → faithful ρ x) L ok)
        (layout-evalO ratO ρ′ d)))
  where L = LayoutWith.layout termOps d
        ρ′ = ι ∘ ρ
