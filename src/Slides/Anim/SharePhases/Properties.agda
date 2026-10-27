{-# OPTIONS --safe --without-K #-}

-- Sharing the subformulas of the shipped phases (`Slides.Anim.SharePhases`) means what the unshared
-- phases mean.
--
-- A phase (`Slides.Anim.Phases`) is a list of elements, each with the formulas of its numbers.
-- Here the formulas of *all the elements of a phase* are shared through one store
-- (`Slides.Anim.Share`): the phase ships its program (`prog`: the definitions, oldest first)
-- and, for each element, its base command and its numbers as nodes over those definitions
-- (`SElem`).  The page evaluates the program once per time step, in order, and then the numbers.
--
-- Meaning.  Let `pageElemS` be what the page sets for a shared element, with the program
-- evaluated in order (`Sound.env`).  For every reading of formulas `R` (`Share.Reading`) with a
-- semantics `S`:
--
--   * `pageFrameS-sem`: at every tick `k`, at every assignment `ρ`, the frame the page draws from
--     the shared phases of `ps` is the frame it draws from the phases `ps` themselves
--     (`Slides.Anim.Phases.pageElem`, with the numbers read as `ref`), *as lists of drawing
--     commands*: sharing changes nothing the page shows;
--   * the instances at ℚ (`pageFrameS-sem-ℚ`, readings of `Slides.Anim.Formula.⟦_⟧`) and at ℕ
--     (`pageFrameS-sem-ℕ`, `⟦_⟧ᴺ` and the output `⟦_⟧ᴰ`), whose composition with
--     `Slides.Anim.Phases.pageFrame-sem` and `Slides.Anim.DPhases.pageFrameD-sem` says that the
--     shared page shows the symbolic layout of tick `k` evaluated at `ρ`: the continuous frame,
--     respectively the discrete one the flipbook shows (`Slides.Anim.DParam.Properties.discrete-assemblyD`).
--
-- The base command of a shared element has the numbers that a formula overwrites zeroed
-- (`shareElem`, `zeroBase-sem`: the page sets the same numbers), so that elements that differ
-- only in those numbers ship the same `<svg>` string, once (`Slides.Backend.Diagram`).
--
-- Hypotheses: none beyond the readings being the folds `Semantics` says they are (the instances
-- below are by definition, `refl`), and that `ref`, what a phase's formula is read as, is
-- `refOut` (`Slides.Anim.Share.Semantics.refOut`: a half at the root of a position is a real half).
--
-- Not proved: the printing as JSON and the page's evaluation of the program (see `Share`).

module Slides.Anim.SharePhases.Properties where

open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; map; reverse; length)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
import Data.List.Properties as LP
open import Data.Nat as ℕ using (ℕ; suc; _/_; _%_; _*_; _∸_; _⊔_; _<ᵇ_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Integer using (+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

open import Slides.Diagram.Draw using (Draw; rect; circle; line; arrow; label)
open import Slides.Diagram.NatQ using (ι)
open import Slides.Diagram.Ordered using (OrdOps; FloorOps; ratOrd; ratFloor)
open import Slides.Anim.Track using (progress)
open import Slides.Anim.Formula
open import Slides.Anim.Formula.Properties
open import Slides.Anim.Phases using (Elem; Kind; nums; entries; withNums)
open import Slides.Anim.Phases.Properties using (baseNum; pageNumsG; pageElemG; active; active-map)
open import Slides.Anim.Share
open import Slides.Anim.Share.Properties
open import Slides.Anim.SharePhases
open St using (defs)
open SElem
open SBody

------------------------------------------------------------------------
-- The readings

private
  halfQ : ℚ → ℚ
  halfQ x = (+ 1 ℚ./ 2) ℚ.* x

-- formulas read in ℚ (`⟦_⟧`): the output is the value, a half at the root a real half
readingℚ : Reading ℚ ℚ
readingℚ = record
  { rnum = ι ; app1 = a1 ; app2 = a2 ; app4 = a4 ; out = λ x → x ; outHlf = halfQ }
  where
    a1 : Op1 → ℚ → ℚ
    a1 (oPct p) x = (+ p ℚ./ 100) ℚ.* x
    a1 oHlf     x = halfQ x
    a1 (oDiv d) x = FloorOps.divBy ratFloor d x
    a1 (oMod d) x = FloorOps.modBy ratFloor d x
    a1 (oMul n) x = FloorOps.mulLit ratFloor n x
    a1 (oEase e) x = progress e x
    a2 : Op2 → ℚ → ℚ → ℚ
    a2 oAdd = ℚ._+_
    a2 oSub = ℚ._-_
    a2 oMax = ℚ._⊔_
    a2 oMin = ℚ._⊓_
    a4 : ℚ → ℚ → ℚ → ℚ → ℚ
    a4 = OrdOps.lt ratOrd

semℚ : Semantics readingℚ
semℚ = record
  { sem = ⟦_⟧
  ; s-num = λ _ _ → refl ; s-var = λ _ _ → refl ; s-add = λ _ _ _ → refl ; s-sub = λ _ _ _ → refl
  ; s-max = λ _ _ _ → refl ; s-pct = λ _ _ _ → refl ; s-hlf = λ _ _ → refl ; s-fdiv = λ _ _ _ → refl
  ; s-fmod = λ _ _ _ → refl ; s-fmul = λ _ _ _ → refl ; s-flt = λ _ _ _ _ _ → refl
  ; s-fmin = λ _ _ _ → refl ; s-fease = λ _ _ _ → refl }

-- formulas read in ℕ (`⟦_⟧ᴺ`), the output a rational (`⟦_⟧ᴰ`)
readingℕ : Reading ℕ ℚ
readingℕ = record
  { rnum = λ n → n ; app1 = a1 ; app2 = a2 ; app4 = a4 ; out = ι ; outHlf = λ x → halfQ (ι x) }
  where
    a1 : Op1 → ℕ → ℕ
    a1 (oPct p) x = (x * p) / 100
    a1 oHlf     x = x / 2
    a1 (oDiv d) x = x / suc d
    a1 (oMod d) x = x % suc d
    a1 (oMul n) x = n * x
    a1 (oEase _) x = x          -- an easing has no ℕ reading (removed with this reading)
    a2 : Op2 → ℕ → ℕ → ℕ
    a2 oAdd = ℕ._+_
    a2 oSub = _∸_
    a2 oMax = _⊔_
    a2 oMin = ℕ._⊓_
    a4 : ℕ → ℕ → ℕ → ℕ → ℕ
    a4 a b x y = if a <ᵇ b then x else y

semℕ : Semantics readingℕ
semℕ = record
  { sem = ⟦_⟧ᴺ
  ; s-num = λ _ _ → refl ; s-var = λ _ _ → refl ; s-add = λ _ _ _ → refl ; s-sub = λ _ _ _ → refl
  ; s-max = λ _ _ _ → refl ; s-pct = λ _ _ _ → refl ; s-hlf = λ _ _ → refl ; s-fdiv = λ _ _ _ → refl
  ; s-fmod = λ _ _ _ → refl ; s-fmul = λ _ _ _ → refl ; s-flt = λ _ _ _ _ _ → refl
  ; s-fmin = λ _ _ _ → refl ; s-fease = λ _ _ _ → refl }

-- the output reading is the existing one
refOutℚ : ∀ g ρ → Semantics.refOut semℚ g ρ ≡ ⟦ g ⟧ ρ
refOutℚ (num _)       ρ = refl
refOutℚ (var _)       ρ = refl
refOutℚ (add _ _)     ρ = refl
refOutℚ (sub _ _)     ρ = refl
refOutℚ (max _ _)     ρ = refl
refOutℚ (pct _ _)     ρ = refl
refOutℚ (hlf _)       ρ = refl
refOutℚ (fdiv _ _)    ρ = refl
refOutℚ (fmod _ _)    ρ = refl
refOutℚ (fmul _ _)    ρ = refl
refOutℚ (flt _ _ _ _) ρ = refl
refOutℚ (fmin _ _)    ρ = refl
refOutℚ (fease _ _)   ρ = refl

refOutℕ : ∀ g ρ → Semantics.refOut semℕ g ρ ≡ ⟦ g ⟧ᴰ ρ
refOutℕ (num _)       ρ = refl
refOutℕ (var _)       ρ = refl
refOutℕ (add _ _)     ρ = refl
refOutℕ (sub _ _)     ρ = refl
refOutℕ (max _ _)     ρ = refl
refOutℕ (pct _ _)     ρ = refl
refOutℕ (hlf _)       ρ = refl
refOutℕ (fdiv _ _)    ρ = refl
refOutℕ (fmod _ _)    ρ = refl
refOutℕ (fmul _ _)    ρ = refl
refOutℕ (flt _ _ _ _) ρ = refl
refOutℕ (fmin _ _)    ρ = refl
refOutℕ (fease _ _)   ρ = refl

------------------------------------------------------------------------
-- What the page sets

-- the same for shared numbers, with `val` the value of a node
pageNumsS : (Node → ℚ) → List (Kind × ℕ) → List (Maybe Node) → List ℚ
pageNumsS v []       _              = []
pageNumsS v (b ∷ bs) []             = baseNum b ∷ pageNumsS v bs []
pageNumsS v (b ∷ bs) (nothing ∷ es) = baseNum b ∷ pageNumsS v bs es
pageNumsS v (b ∷ bs) (just n  ∷ es) = v n ∷ pageNumsS v bs es

pageElemS : (Node → ℚ) → SElem → Draw ℚ
pageElemS v e = withNums (base e) (pageNumsS v (nums (base e)) (entriesS (coords e))) 0ℚ

------------------------------------------------------------------------
-- Zeroing the numbers the formulas overwrite changes nothing the page sets

-- the slots with other numbers
zipK : List (Kind × ℕ) → List ℕ → List (Kind × ℕ)
zipK []             _        = []
zipK ((k , n) ∷ bs) []       = (k , n) ∷ zipK bs []
zipK ((k , n) ∷ bs) (m ∷ zs) = (k , m) ∷ zipK bs zs

length-zeroAt : ∀ bs es → length (zeroAt bs es) ≡ length bs
length-zeroAt []             es             = refl
length-zeroAt ((k , n) ∷ bs) []             = cong suc (length-zeroAt bs [])
length-zeroAt ((k , n) ∷ bs) (nothing ∷ es) = cong suc (length-zeroAt bs es)
length-zeroAt ((k , n) ∷ bs) (just _  ∷ es) = cong suc (length-zeroAt bs es)

-- a command refilled with numbers is a command whose slots have those numbers (the kinds stay)
nums-withNums : ∀ d zs → length zs ≡ length (nums d) → nums (withNums d zs 0) ≡ zipK (nums d) zs
nums-withNums (rect _ _ _ _ _) (a ∷ b ∷ c ∷ e ∷ []) _ = refl
nums-withNums (rect _ _ _ _ _) []                     ()
nums-withNums (rect _ _ _ _ _) (_ ∷ [])               ()
nums-withNums (rect _ _ _ _ _) (_ ∷ _ ∷ [])           ()
nums-withNums (rect _ _ _ _ _) (_ ∷ _ ∷ _ ∷ [])       ()
nums-withNums (rect _ _ _ _ _) (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _) ()
nums-withNums (circle _ _ _ _) (a ∷ b ∷ c ∷ [])       _ = refl
nums-withNums (circle _ _ _ _) []                     ()
nums-withNums (circle _ _ _ _) (_ ∷ [])               ()
nums-withNums (circle _ _ _ _) (_ ∷ _ ∷ [])           ()
nums-withNums (circle _ _ _ _) (_ ∷ _ ∷ _ ∷ _ ∷ _)    ()
nums-withNums (line _ _ _ _ _) (a ∷ b ∷ c ∷ e ∷ [])   _ = refl
nums-withNums (line _ _ _ _ _) []                     ()
nums-withNums (line _ _ _ _ _) (_ ∷ [])               ()
nums-withNums (line _ _ _ _ _) (_ ∷ _ ∷ [])           ()
nums-withNums (line _ _ _ _ _) (_ ∷ _ ∷ _ ∷ [])       ()
nums-withNums (line _ _ _ _ _) (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _) ()
nums-withNums (arrow _ _ _ _ _) (a ∷ b ∷ c ∷ e ∷ [])  _ = refl
nums-withNums (arrow _ _ _ _ _) []                    ()
nums-withNums (arrow _ _ _ _ _) (_ ∷ [])              ()
nums-withNums (arrow _ _ _ _ _) (_ ∷ _ ∷ [])          ()
nums-withNums (arrow _ _ _ _ _) (_ ∷ _ ∷ _ ∷ [])      ()
nums-withNums (arrow _ _ _ _ _) (_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _) ()
nums-withNums (label _ _ _ _ _) (a ∷ b ∷ [])          _ = refl
nums-withNums (label _ _ _ _ _) []                    ()
nums-withNums (label _ _ _ _ _) (_ ∷ [])              ()
nums-withNums (label _ _ _ _ _) (_ ∷ _ ∷ _ ∷ _)       ()

-- refilling ignores the numbers a command has
withNums-withNums : ∀ {T : Set} (d : Draw ℕ) zs (z : ℕ) (ts : List T) (z′ : T) →
                    withNums (withNums d zs z) ts z′ ≡ withNums d ts z′
withNums-withNums (rect _ _ _ _ _)  zs z ts z′ = refl
withNums-withNums (circle _ _ _ _)  zs z ts z′ = refl
withNums-withNums (line _ _ _ _ _)  zs z ts z′ = refl
withNums-withNums (arrow _ _ _ _ _) zs z ts z′ = refl
withNums-withNums (label _ _ _ _ _) zs z ts z′ = refl

pageNumsS-zip : ∀ v bs es → pageNumsS v (zipK bs (zeroAt bs es)) es ≡ pageNumsS v bs es
pageNumsS-zip v []             es             = refl
pageNumsS-zip v ((k , n) ∷ bs) []             = cong (baseNum (k , n) ∷_) (pageNumsS-zip v bs [])
pageNumsS-zip v ((k , n) ∷ bs) (nothing ∷ es) = cong (baseNum (k , n) ∷_) (pageNumsS-zip v bs es)
pageNumsS-zip v ((k , n) ∷ bs) (just m  ∷ es) = cong (v m ∷_) (pageNumsS-zip v bs es)

-- the page sets the same numbers on a shared element whose base is zeroed
zeroBase-sem : ∀ v d cs → pageElemS v (selem (zeroBase d cs) cs) ≡ pageElemS v (selem d cs)
zeroBase-sem v d cs =
  trans (withNums-withNums d zs 0 (pageNumsS v (nums (withNums d zs 0)) es) 0ℚ)
        (cong (λ ts → withNums d ts 0ℚ)
          (trans (cong (λ l → pageNumsS v l es) (nums-withNums d zs (length-zeroAt (nums d) es)))
                 (pageNumsS-zip v (nums d) es)))
  where
    es = entriesS cs
    zs = zeroAt (nums d) es

------------------------------------------------------------------------
-- Sharing means the same, for any reading

module Lift {A : Set} (R : Reading A ℚ) (S : Semantics R) (ref : Formula → (ℕ → A) → ℚ)
            (ref≡ : ∀ g ρ → Semantics.refOut S g ρ ≡ ref g ρ) where
  open Sound R S

  -- an element and its shared version: the same base, and numbers that read the same
  ElemQ : (ℕ → A) → List Node → Elem → SElem → Set
  ElemQ ρ ds e se = base se ≡ zeroBase (Elem.base e) (coords se) × MaybeQ (AllQ (MaybeQ (OutQ ρ))) ds (Elem.coords e) (coords se)

  ElemQ-stable : ∀ ρ → Stable (ElemQ ρ)
  ElemQ-stable ρ x (b , q) =
    b , MaybeQ-stable {Q = AllQ (MaybeQ (OutQ ρ))} (AllQ-stable {Q = MaybeQ (OutQ ρ)} (MaybeQ-stable {Q = OutQ ρ} (OutQ-stable ρ))) x q

  shareCoords-realises : ∀ ρ → Realises (MaybeQ (AllQ (MaybeQ (OutQ ρ)))) shareCoords
  shareCoords-realises ρ =
    traverseM-realises {Q = AllQ (MaybeQ (OutQ ρ))}
      (traverseL-realises {Q = MaybeQ (OutQ ρ)} (MaybeQ-stable {Q = OutQ ρ} (OutQ-stable ρ))
        (traverseM-realises {Q = OutQ ρ} (output-realises ρ)))

  shareElem-realises : ∀ ρ → Realises (ElemQ ρ) shareElem
  shareElem-realises ρ e st I with shareCoords-realises ρ (Elem.coords e) st I
  ... | I′ , x , q = I′ , x , refl , q

  shareElems-realises : ∀ ρ → Realises (AllQ (ElemQ ρ)) (traverseL shareElem)
  shareElems-realises ρ = traverseL-realises (ElemQ-stable ρ) (shareElem-realises ρ)

  -- the numbers of an element read the same
  pageNumsS-sem : ∀ ρ ds (v : Node → ℚ) bs es ns →
                  (∀ g nd → OutQ ρ ds g nd → v nd ≡ ref g ρ) →
                  AllQ (MaybeQ (OutQ ρ)) ds es ns →
                  pageNumsS v bs ns ≡ pageNumsG (λ f → ref f ρ) bs es
  pageNumsS-sem ρ ds v []       es ns h q = refl
  pageNumsS-sem ρ ds v (b ∷ bs) [] [] h [] = cong (baseNum b ∷_) (pageNumsS-sem ρ ds v bs [] [] h [])
  pageNumsS-sem ρ ds v (b ∷ bs) (nothing ∷ es) (nothing ∷ ns) h (nothingQ ∷ qs) =
    cong (baseNum b ∷_) (pageNumsS-sem ρ ds v bs es ns h qs)
  pageNumsS-sem ρ ds v (b ∷ bs) (just g ∷ es) (just nd ∷ ns) h (justQ q ∷ qs) =
    cong₂ _∷_ (h g nd q) (pageNumsS-sem ρ ds v bs es ns h qs)

  entries-Q : ∀ {ρ ds cs ns} → MaybeQ (AllQ (MaybeQ (OutQ ρ))) ds cs ns →
              AllQ (MaybeQ (OutQ ρ)) ds (entries cs) (entriesS ns)
  entries-Q nothingQ  = []
  entries-Q (justQ q) = q

  pageElemS-sem : ∀ ρ ds (v : Node → ℚ) e se →
                  (∀ g nd → OutQ ρ ds g nd → v nd ≡ ref g ρ) →
                  ElemQ ρ ds e se → pageElemS v se ≡ pageElemG (λ f → ref f ρ) e
  pageElemS-sem ρ ds v e se h (b , q) =
    trans (cong (pageElemS v) {x = se} {y = selem (zeroBase (Elem.base e) (coords se)) (coords se)} (cong (λ d → selem d (coords se)) b))
   (trans (zeroBase-sem v (Elem.base e) (coords se))
          (cong (λ ns → withNums (Elem.base e) ns 0ℚ)
                (pageNumsS-sem ρ ds v (nums (Elem.base e)) (entries (Elem.coords e)) (entriesS (coords se)) h (entries-Q q))))

  pageElemsS-sem : ∀ ρ ds (v : Node → ℚ) es ses →
                   (∀ g nd → OutQ ρ ds g nd → v nd ≡ ref g ρ) →
                   AllQ (ElemQ ρ) ds es ses →
                   map (pageElemS v) ses ≡ map (pageElemG (λ f → ref f ρ)) es
  pageElemsS-sem ρ ds v []       []         h []       = refl
  pageElemsS-sem ρ ds v (e ∷ es) (se ∷ ses) h (q ∷ qs) =
    cong₂ _∷_ (pageElemS-sem ρ ds v e se h q) (pageElemsS-sem ρ ds v es ses h qs)

  -- the value of a node, against a program evaluated in order
  valProg : (ℕ → A) → List Node → Node → ℚ
  valProg ρ p = evalOut ρ (env ρ (reverse p))

  -- what the page draws at tick `k` from the shared phases
  pageFrameS : List (ℕ × SBody) → ℕ → (ℕ → A) → Maybe (List (Draw ℚ))
  pageFrameS sps k ρ =
    Maybe.map (λ b → map (pageElemS (valProg ρ (prog b))) (elems b)) (active sps k)

  -- a phase and its shared version read the same
  shareBody-sem : ∀ ρ es → map (pageElemS (valProg ρ (prog (shareBody es)))) (elems (shareBody es))
                         ≡ map (pageElemG (λ f → ref f ρ)) es
  shareBody-sem ρ es with shareElems-realises ρ es emptySt Inv-empty
  ... | I , x , qs = pageElemsS-sem ρ ds v es ses h qs
    where
      ses = proj₁ (traverseL shareElem es emptySt)
      st′ = proj₂ (traverseL shareElem es emptySt)
      ds  = defs st′
      v   = valProg ρ (program st′)
      -- the program evaluated in order is the store's own environment
      v≡ : ∀ nd → v nd ≡ evalOut ρ (env ρ ds) nd
      v≡ nd = cong (λ d → evalOut ρ (env ρ d) nd) {x = reverse (reverse ds)} {y = ds} (LP.reverse-involutive ds)
      h : ∀ g nd → OutQ ρ ds g nd → v nd ≡ ref g ρ
      h g nd q = trans (v≡ nd) (trans (OutQ.val q) (ref≡ g ρ))

------------------------------------------------------------------------
-- The theorems

module Frame {A : Set} (R : Reading A ℚ) (S : Semantics R) (ref : Formula → (ℕ → A) → ℚ)
             (ref≡ : ∀ g ρ → Semantics.refOut S g ρ ≡ ref g ρ) where
  open Lift R S ref ref≡

  -- Sharing the phases changes nothing the page draws.
  pageFrameS-sem : ∀ ps k ρ →
    pageFrameS (sharePhases ps) k ρ
    ≡ Maybe.map (map (pageElemG (λ f → ref f ρ))) (active ps k)
  pageFrameS-sem ps k ρ =
    trans (cong (Maybe.map (λ b → map (pageElemS (valProg ρ (prog b))) (elems b)))
                (active-map shareBody ps k))
          (go (active ps k))
    where
      go : ∀ m → Maybe.map (λ b → map (pageElemS (valProg ρ (prog b))) (elems b)) (Maybe.map shareBody m)
               ≡ Maybe.map (map (pageElemG (λ f → ref f ρ))) m
      go nothing   = refl
      go (just es) = cong just (shareBody-sem ρ es)

-- continuous templates: the shared phases show what `Slides.Anim.Phases.pageFrame` shows
module Continuous = Frame readingℚ semℚ ⟦_⟧ refOutℚ
module Discrete   = Frame readingℕ semℕ ⟦_⟧ᴰ refOutℕ
