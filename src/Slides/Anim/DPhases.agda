{-# OPTIONS --safe --without-K #-}

-- What the backend ships for a discrete parametric animation, and that it means the symbolic
-- frames (`Slides.Anim.DParam`).  As `Slides.Anim.Phases`, with the formulas read in ℕ.
--
-- The shipped data are the same `Elem`s and phases as for continuous templates (`Elem`, `runs`,
-- `phasesOf`'s grouping are shared: nothing in them depends on how a formula is read).  What
-- differs is the encoding of a number (`encD`, which folds closed subformulas in ℕ, with no side
-- condition) and the reading of a shipped number by the page (`⟦_⟧ᴰ`: the formula in ℕ, a real
-- half for the positions).  We prove, as for continuous templates,
--
--   * `encodeDrawD-sem`: for a drawing command `dr` of a symbolic layout, the numbers the page
--     sets for `encodeDrawD dr` at `ρ` are those of `dr` evaluated in ℕ at `ρ` (`evalD natD ρ`),
--     positions halved: `halve (mapDraw (ι ∘ evalD natD ρ) dr)`.  This includes that the folded
--     closed subformulas are exact (`Slides.Anim.Formula.encD-semN`, no hypotheses) and that the
--     base numbers, taken at the all-zero assignment, are the right ones where the formula is a
--     folded constant (`enc-numN`);
--   * `pageFrameD-sem`: so at tick `k` the page's frame, at `ρ`, is the symbolic layout of tick `k`
--     evaluated in ℕ at `ρ` and halved.  With `Slides.Anim.DParamCorrect.discrete-assemblyD`
--     that is the frame the flipbook shows.
--
-- Not proved: the printing of this data as JSON and its reading by the player (the discrete
-- evaluator `evD` of `assets/animation.js`), and its floating point.  Those are tested.

module Slides.Anim.DPhases where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ; _/_; _+_; _∸_; _⊔_)
open import Data.Fin using (zero) renaming (suc to fsuc)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Integer using (+_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Slides.Diagram.Draw using (Draw; mapDraw; Layout)
open import Slides.Diagram.Euclid using (DExpr; evalD; natD)
import Slides.Diagram.Euclid as Eu
import Slides.Diagram.Expr as E
open import Slides.Diagram.NatQ using (ι)
open import Slides.Anim.Formula
open import Slides.Anim.Nth using (nth; nth-map)
open import Slides.Anim.Phases
open Elem

------------------------------------------------------------------------
-- One drawing command, as shipped

-- the formula of a number: positions are halved
slotFD : Kind × DExpr ℕ → Formula
slotFD (pos  , e) = half (encD e)
slotFD (size , e) = encD e

encodeDrawD : Draw (DExpr ℕ) → Elem
encodeDrawD dr = elem (mapDraw (evalD natD (λ _ → 0)) dr) (coordsOf (map slotFD (nums dr)))

-- the numbers the page sets: the formula's value where there is one, else the base number
pageNumsD : List (Kind × ℕ) → List (Maybe Formula) → (ℕ → ℕ) → List ℚ
pageNumsD []       _              ρ = []
pageNumsD (b ∷ bs) []             ρ = baseNum b ∷ pageNumsD bs [] ρ
pageNumsD (b ∷ bs) (nothing ∷ es) ρ = baseNum b ∷ pageNumsD bs es ρ
pageNumsD (b ∷ bs) (just f  ∷ es) ρ = ⟦ f ⟧ᴰ ρ ∷ pageNumsD bs es ρ

pageElemD : Elem → (ℕ → ℕ) → Draw ℚ
pageElemD e ρ = withNums (base e) (pageNumsD (nums (base e)) (entries (coords e)) ρ) 0ℚ

------------------------------------------------------------------------
-- A drawing command means what it ships

private
  -- the encoder never produces a half except at the root (`half`)
  fold1-hlf : ∀ f mk → (∀ a c → mk a ≡ hlf c → ⊥) → ∀ a c → fold1 f mk a ≡ hlf c → ⊥
  fold1-hlf f mk nn a c h with numOf a
  fold1-hlf f mk nn a c () | just _
  fold1-hlf f mk nn a c h  | nothing = nn a c h

  fold2-hlf : ∀ f mk → (∀ a b c → mk a b ≡ hlf c → ⊥) → ∀ a b c → fold2 f mk a b ≡ hlf c → ⊥
  fold2-hlf f mk nn a b c h with numOf a | numOf b
  fold2-hlf f mk nn a b c () | just _ | just _
  fold2-hlf f mk nn a b c h  | just _ | nothing = nn a b c h
  fold2-hlf f mk nn a b c h  | nothing | _ = nn a b c h

  ltF-hlf : ∀ a b x y c → ltF a b x y ≡ hlf c → (x ≡ hlf c) ⊎ (y ≡ hlf c)
  ltF-hlf a b x y c h with numOf a | numOf b
  ltF-hlf a b x y c h | just u | just v with u ℕ.<ᵇ v
  ltF-hlf a b x y c h | just u | just v | true  = inj₁ h
  ltF-hlf a b x y c h | just u | just v | false = inj₂ h
  ltF-hlf a b x y c () | just _ | nothing
  ltF-hlf a b x y c () | nothing | _

encD-hlf : ∀ (e : DExpr ℕ) c → encD e ≡ hlf c → ⊥
encD-hlf (pure v) c ()
encD-hlf (impure (inj₁ (inj₁ E.Zero) , _)) c ()
encD-hlf (impure (inj₁ (inj₁ (E.Lit n)) , _)) c ()
encD-hlf (impure (inj₁ (inj₁ E.Plus) , k)) c h = fold2-hlf _+_ add (λ _ _ _ ()) (encD (k zero)) (encD (k (fsuc zero))) c h
encD-hlf (impure (inj₁ (inj₁ E.Max) , k)) c h = fold2-hlf _⊔_ max (λ _ _ _ ()) (encD (k zero)) (encD (k (fsuc zero))) c h
encD-hlf (impure (inj₁ (inj₁ (E.Pct p)) , k)) c h = fold1-hlf _ (pct p) (λ _ _ ()) (encD (k tt)) c h
encD-hlf (impure (inj₁ (inj₂ E.Sub) , k)) c h = fold2-hlf _∸_ sub (λ _ _ _ ()) (encD (k zero)) (encD (k (fsuc zero))) c h
encD-hlf (impure (inj₂ (Eu.DivBy d) , k)) c h = fold1-hlf _ (fdiv d) (λ _ _ ()) (encD (k tt)) c h
encD-hlf (impure (inj₂ (Eu.ModBy d) , k)) c h = fold1-hlf _ (fmod d) (λ _ _ ()) (encD (k tt)) c h
encD-hlf (impure (inj₂ (Eu.MulLit n) , k)) c h = fold1-hlf _ (fmul n) (λ _ _ ()) (encD (k tt)) c h
encD-hlf (impure (inj₂ Eu.Lt , k)) c h with ltF-hlf (encD (k zero)) (encD (k (fsuc zero))) (encD (k (fsuc (fsuc zero)))) (encD (k (fsuc (fsuc (fsuc zero))))) c h
... | inj₁ hx = encD-hlf (k (fsuc (fsuc zero))) c hx
... | inj₂ hy = encD-hlf (k (fsuc (fsuc (fsuc zero)))) c hy

private
  -- the value a number should have at `ρ`
  target : (ℕ → ℕ) → Kind × DExpr ℕ → ℚ
  target ρ (k , e) = halfIf k (ι (evalD natD ρ e))

  base0 : Kind × DExpr ℕ → Kind × ℕ
  base0 (k , e) = k , evalD natD (λ _ → 0) e

  -- a formula that is not a half is read as its value in ℕ
  val-nohlf : ∀ f ρ → (∀ c → f ≡ hlf c → ⊥) → ⟦ f ⟧ᴰ ρ ≡ ι (⟦ f ⟧ᴺ ρ)
  val-nohlf (num _)       ρ nn = refl
  val-nohlf (var _)       ρ nn = refl
  val-nohlf (add _ _)     ρ nn = refl
  val-nohlf (sub _ _)     ρ nn = refl
  val-nohlf (max _ _)     ρ nn = refl
  val-nohlf (pct _ _)     ρ nn = refl
  val-nohlf (hlf a)       ρ nn = ⊥-elim (nn a refl)
  val-nohlf (fdiv _ _)    ρ nn = refl
  val-nohlf (fmod _ _)    ρ nn = refl
  val-nohlf (fmul _ _)    ρ nn = refl
  val-nohlf (flt _ _ _ _) ρ nn = refl

  slot-val : ∀ x ρ → ⟦ slotFD x ⟧ᴰ ρ ≡ target ρ x
  slot-val (pos  , e) ρ = trans (half-semN (encD e) ρ) (cong (λ v → (+ 1 ℚ./ 2) ℚ.* ι v) (encD-semN e ρ))
  slot-val (size , e) ρ = trans (val-nohlf (encD e) ρ (encD-hlf e)) (cong ι (encD-semN e ρ))

  -- a number that folded to a constant is the base number
  slot-num : ∀ x c ρ → slotFD x ≡ num c → baseNum (base0 x) ≡ target ρ x
  slot-num (pos , e) c ρ h with half-num-inv (encD e) c h
  ... | a , e₁ , _ , refl =
    trans (cong (λ v → ι (v / 2)) (enc-numN e a e₁ (λ _ → 0)))
          (trans (cong (λ f → ⟦ f ⟧ᴰ ρ) (sym h)) (slot-val (pos , e) ρ))
  slot-num (size , e) c ρ h =
    trans (cong ι (enc-numN e c h (λ _ → 0)))
          (trans (cong (λ f → ⟦ f ⟧ᴰ ρ) (sym h)) (slot-val (size , e) ρ))

  -- the rest of an all-constant list is all-constant
  allNum-tail : ∀ f fs → allNum (f ∷ fs) ≡ true → allNum fs ≡ true
  allNum-tail (num _)       fs h = h
  allNum-tail (var _)       fs ()
  allNum-tail (add _ _)     fs ()
  allNum-tail (sub _ _)     fs ()
  allNum-tail (max _ _)     fs ()
  allNum-tail (pct _ _)     fs ()
  allNum-tail (hlf _)       fs ()
  allNum-tail (fdiv _ _)    fs ()
  allNum-tail (fmod _ _)    fs ()
  allNum-tail (fmul _ _)    fs ()
  allNum-tail (flt _ _ _ _) fs ()

  entry-just : ∀ f → numOf f ≡ nothing → entry f ≡ just f
  entry-just (num _)       ()
  entry-just (var _)       _ = refl
  entry-just (add _ _)     _ = refl
  entry-just (sub _ _)     _ = refl
  entry-just (max _ _)     _ = refl
  entry-just (pct _ _)     _ = refl
  entry-just (hlf _)       _ = refl
  entry-just (fdiv _ _)    _ = refl
  entry-just (fmod _ _)    _ = refl
  entry-just (fmul _ _)    _ = refl
  entry-just (flt _ _ _ _) _ = refl

  pageNums-A : ∀ ns ρ → pageNumsD (map base0 ns) (map (λ x → entry (slotFD x)) ns) ρ ≡ map (target ρ) ns
  pageNums-A []       ρ = refl
  pageNums-A (x ∷ ns) ρ with numOf (slotFD x) in eq
  ... | just c  =
    trans (cong (λ f → pageNumsD (base0 x ∷ map base0 ns) (entry f ∷ map (λ y → entry (slotFD y)) ns) ρ)
                (numOf-eq (slotFD x) eq))
          (cong₂ _∷_ (slot-num x c ρ (numOf-eq (slotFD x) eq)) (pageNums-A ns ρ))
  ... | nothing rewrite entry-just (slotFD x) eq =
    cong₂ _∷_ (slot-val x ρ) (pageNums-A ns ρ)

  pageNums-B : ∀ ns ρ → allNum (map slotFD ns) ≡ true → pageNumsD (map base0 ns) [] ρ ≡ map (target ρ) ns
  pageNums-B []       ρ h = refl
  pageNums-B (x ∷ ns) ρ h with numOf (slotFD x) in eq
  ... | just c  =
    trans (cong (λ f → pageNumsD (base0 x ∷ map base0 ns) [] ρ) (numOf-eq (slotFD x) eq))
          (cong₂ _∷_ (slot-num x c ρ (numOf-eq (slotFD x) eq)) (pageNums-B ns ρ (allNum-tail (slotFD x) (map slotFD ns) h)))
  pageNums-B (x ∷ ns) ρ h | nothing = ⊥-elim (notNum (slotFD x) eq h)
    where
      notNum : ∀ f → numOf f ≡ nothing → allNum (f ∷ map slotFD ns) ≡ true → ⊥
      notNum (num _)       ()
      notNum (var _)       _ ()
      notNum (add _ _)     _ ()
      notNum (sub _ _)     _ ()
      notNum (max _ _)     _ ()
      notNum (pct _ _)     _ ()
      notNum (hlf _)       _ ()
      notNum (fdiv _ _)    _ ()
      notNum (fmod _ _)    _ ()
      notNum (fmul _ _)    _ ()
      notNum (flt _ _ _ _) _ ()

  map-map : ∀ {A B C : Set} (f : B → C) (g : A → B) xs → map f (map g xs) ≡ map (λ x → f (g x)) xs
  map-map f g []       = refl
  map-map f g (x ∷ xs) = cong₂ _∷_ refl (map-map f g xs)

-- The drawn element of what is shipped for a command of a symbolic layout is the command, at `ρ`,
-- in ℕ, with positions halved.
encodeDrawD-sem : ∀ (dr : Draw (DExpr ℕ)) ρ →
                  pageElemD (encodeDrawD dr) ρ ≡ halve (mapDraw (λ e → ι (evalD natD ρ e)) dr)
encodeDrawD-sem dr ρ =
  trans (withNums-mapDraw (evalD natD (λ _ → 0)) dr L₁ 0ℚ)
 (trans (cong (λ ts → withNums dr ts 0ℚ) (trans L₁≡T (sym L₂≡T)))
        (sym (withNums-mapDraw (λ e → ι (evalD natD ρ e)) dr L₂ 0ℚ)))
  where
    ns = nums dr
    cs = coordsOf (map slotFD ns)
    L₁ = pageNumsD (nums (mapDraw (evalD natD (λ _ → 0)) dr)) (entries cs) ρ
    L₂ = map (λ ks → halfIf (proj₁ ks) (proj₂ ks)) (nums (mapDraw (λ e → ι (evalD natD ρ e)) dr))
    L₂≡T : L₂ ≡ map (target ρ) ns
    L₂≡T = trans (cong (map (λ ks → halfIf (proj₁ ks) (proj₂ ks))) (nums-mapDraw (λ e → ι (evalD natD ρ e)) dr))
                 (map-map (λ ks → halfIf (proj₁ ks) (proj₂ ks)) (λ ks → proj₁ ks , ι (evalD natD ρ (proj₂ ks))) ns)
    go : ∀ b → allNum (map slotFD ns) ≡ b →
         pageNumsD (map base0 ns) (entries (if b then nothing else just (map entry (map slotFD ns)))) ρ ≡ map (target ρ) ns
    go true  h = pageNums-B ns ρ h
    go false h = trans (cong (λ es → pageNumsD (map base0 ns) es ρ) (map-map entry slotFD ns)) (pageNums-A ns ρ)
    L₁≡T : L₁ ≡ map (target ρ) ns
    L₁≡T = trans (cong (λ bs → pageNumsD bs (entries cs) ρ) (nums-mapDraw (evalD natD (λ _ → 0)) dr))
                 (go (allNum (map slotFD ns)) refl)

------------------------------------------------------------------------
-- The shipped phases of a list of symbolic layouts

tickElemsD : Layout (DExpr ℕ) → List Elem
tickElemsD l = map encodeDrawD (Layout.draws l)

phasesOfD : List (Layout (DExpr ℕ)) → List (ℕ × List Elem)
phasesOfD ls = runs elemsEq? nothing 0 (map tickElemsD ls)

-- what the page draws at tick `k`, at the parameters `ρ`
pageFrameD : List (ℕ × List Elem) → ℕ → (ℕ → ℕ) → Maybe (List (Draw ℚ))
pageFrameD ps k ρ = Maybe.map (map (λ e → pageElemD e ρ)) (active ps k)

private
  map-cong : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → ∀ xs → map f xs ≡ map g xs
  map-cong e []       = refl
  map-cong e (x ∷ xs) = cong₂ _∷_ (e x) (map-cong e xs)

-- At tick `k < length ls`, the page draws the symbolic layout of tick `k` evaluated at `ρ` in ℕ,
-- positions halved.
pageFrameD-sem : ∀ (ls : List (Layout (DExpr ℕ))) k L → nth ls k ≡ just L → ∀ ρ →
                 pageFrameD (phasesOfD ls) k ρ
                 ≡ just (map (λ dr → halve (mapDraw (λ e → ι (evalD natD ρ e)) dr)) (Layout.draws L))
pageFrameD-sem ls k L h ρ
  rewrite phases-active elemsEq? (map tickElemsD ls) k
            (trans (nth-map tickElemsD ls k) (cong (Maybe.map tickElemsD) h)) =
  cong just (trans (map-map (λ e → pageElemD e ρ) encodeDrawD (Layout.draws L))
                   (map-cong (λ dr → encodeDrawD-sem dr ρ) (Layout.draws L)))
