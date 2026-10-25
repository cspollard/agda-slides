{-# OPTIONS --safe --without-K #-}

-- Laws of the layout operations (`Slides.Diagram.Place`), for any scalar whose
-- `Ops` form a commutative ring up to some equivalence `_≈_`, with a maximum
-- that is congruent, commutative and associative (`IsLawful`).  ℤ is one
-- (`lawfulℤ`, with `_≈_` = `_≡_`); ℕ is not (its difference is the monus), so ℕ
-- runs the layout but is not covered here.
--
--   * translation is an action: `shift 0 d ≈ᴸ d`, `shift a (shift b d) ≈ᴸ shift (b + a) d`
--   * `∥`, `═` and `⊙` are associative
--   * for a layout of non-negative size, the empty diagram is a unit of each
--   * annotations do not change a layout's size or anchors
--   * the size of a layout is a fold of its own, `sizeAlgebra` (fusion)
--
-- Equality of layouts is the scalar's equality lifted pointwise
-- (`Slides.Diagram.Equality`): a layout is plain data, so no function
-- extensionality is needed, and the scalar's equality need not be `_≡_`.

module Slides.Diagram.Laws where

open import Level using (0ℓ)
open import Algebra using (CommutativeRing; IsCommutativeRing)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Properties as ℤP
import Data.Rational as ℚ
import Data.Rational.Properties as ℚP
open import Data.List using (List; []; _∷_; map; _++_)
import Data.List.Properties as L
open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise; _∷_; [])
open import Data.Maybe using (just; nothing)
open import Data.Nat using () renaming (_*_ to _*ℕ_; _/_ to _/ℕ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit using (tt)
open import Data.Container.FreeMonad using (pure; impure)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

open import Slides.Diagram.Draw
open import Slides.Diagram.Scalar
open import Slides.Diagram.Syntax
  using ( Dia; Algebra; fold; arity; Op; Rectangle; Disc; Segment; Text; Spacer; Raw
        ; Beside; Above; Atop; LabelAbove; LabelBelow; Named; Connect
        ; VAlign; top; middle; bottom; Align; left; centred; right )
open import Slides.Diagram.TextMetrics using (textWidth)
import Slides.Diagram.Layout as Lay
open import Tactic.RingSolver.Core.AlmostCommutativeRing using (fromCommutativeRing)
import Tactic.RingSolver.NonReflective as NonReflective

-- What the laws need of a scalar `O`: a commutative ring structure on its sum
-- and zero, up to an equivalence `_≈_`; a difference that is the ring's; and a
-- maximum that is congruent, commutative and associative.  The ring operations
-- that `Ops` does not mention (`*`, `1`, negation) are given here.
record IsLawful {S : Set} (O : Ops S) : Set₁ where
  open Ops O
  field
    _≈_      : Rel S 0ℓ
    _*_      : S → S → S
    1#       : S
    neg      : S → S
    isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ neg 0# 1#
    sub≈     : ∀ a b → (a - b) ≈ (a + neg b)
    ⊔-cong   : ∀ {x x′ y y′} → x ≈ x′ → y ≈ y′ → (x ⊔ y) ≈ (x′ ⊔ y′)
    ⊔-comm   : ∀ x y → (x ⊔ y) ≈ (y ⊔ x)
    ⊔-assoc  : ∀ x y z → ((x ⊔ y) ⊔ z) ≈ (x ⊔ (y ⊔ z))

lawfulℤ : IsLawful intOps
lawfulℤ = record
  { _≈_ = _≡_ ; _*_ = ℤ._*_ ; 1# = ℤ.+ 1 ; neg = ℤ.-_
  ; isCommutativeRing = ℤP.+-*-isCommutativeRing
  ; sub≈ = λ _ _ → refl
  ; ⊔-cong = cong₂ ℤ._⊔_
  ; ⊔-comm = ℤP.⊔-comm
  ; ⊔-assoc = ℤP.⊔-assoc }

lawfulℚ : IsLawful ratOps
lawfulℚ = record
  { _≈_ = _≡_ ; _*_ = ℚ._*_ ; 1# = ℚ.1ℚ ; neg = ℚ.-_
  ; isCommutativeRing = ℚP.+-*-isCommutativeRing
  ; sub≈ = λ _ _ → refl
  ; ⊔-cong = cong₂ ℚ._⊔_
  ; ⊔-comm = ℚP.⊔-comm
  ; ⊔-assoc = ℚP.⊔-assoc }

module Proofs {S : Set} (O : Ops S) (L : IsLawful O) where
  open Ops O
  open IsLawful L
  open import Slides.Diagram.Place O

  ring : CommutativeRing 0ℓ 0ℓ
  ring = record
    { Carrier = S ; _≈_ = _≈_ ; _+_ = _+_ ; _*_ = _*_ ; -_ = neg ; 0# = 0# ; 1# = 1#
    ; isCommutativeRing = isCommutativeRing }

  module R = CommutativeRing ring

  open import Slides.Diagram.Equality R.isEquivalence

  ----------------------------------------------------------------------
  -- Offsets

  -- add the offsets of two shifts
  infixl 6 _⊞_
  _⊞_ : S × S → S × S → S × S
  p ⊞ q = proj₁ p + proj₁ q , proj₂ p + proj₂ q

  -- equal offsets
  infix 4 _≈ₚ_
  _≈ₚ_ : S × S → S × S → Set
  p ≈ₚ q = proj₁ p ≈ proj₁ q × proj₂ p ≈ proj₂ q

  +-assoc : ∀ x y z → ((x + y) + z) ≈ (x + (y + z))
  +-assoc = R.+-assoc

  +-identityʳ : ∀ x → (x + 0#) ≈ x
  +-identityʳ = R.+-identityʳ

  +-identityˡ : ∀ x → (0# + x) ≈ x
  +-identityˡ = R.+-identityˡ

  +-cong : ∀ {x x′ y y′} → x ≈ x′ → y ≈ y′ → (x + y) ≈ (x′ + y′)
  +-cong = R.+-cong

  ----------------------------------------------------------------------
  -- Shifting

  shiftDraw′ : S × S → Draw S → Draw S
  shiftDraw′ p = shiftDraw (proj₁ p) (proj₂ p)

  shiftAnchor′ : S × S → String × Box S → String × Box S
  shiftAnchor′ p = shiftAnchor (proj₁ p) (proj₂ p)

  shiftDraw-cong : ∀ {p p′} → p ≈ₚ p′ → ∀ x → shiftDraw′ p x ≈ᵈ shiftDraw′ p′ x
  shiftDraw-cong (ex , ey) (rect x y w h s) = rect≈ (+-cong R.refl ex) (+-cong R.refl ey) R.refl R.refl
  shiftDraw-cong (ex , ey) (circle x y r s) = circle≈ (+-cong R.refl ex) (+-cong R.refl ey) R.refl
  shiftDraw-cong (ex , ey) (line a b c d s) =
    line≈ (+-cong R.refl ex) (+-cong R.refl ey) (+-cong R.refl ex) (+-cong R.refl ey)
  shiftDraw-cong (ex , ey) (arrow a b c d s) =
    arrow≈ (+-cong R.refl ex) (+-cong R.refl ey) (+-cong R.refl ex) (+-cong R.refl ey)
  shiftDraw-cong (ex , ey) (label x y n t s) = label≈ (+-cong R.refl ex) (+-cong R.refl ey)
  shiftDraw-cong (ex , ey) (fixed e) = fixed≈

  shiftAnchor-cong : ∀ {p p′} → p ≈ₚ p′ → ∀ x → shiftAnchor′ p x ≈ᵃ shiftAnchor′ p′ x
  shiftAnchor-cong (ex , ey) (n , box l t w h) =
    refl , box≈ (+-cong R.refl ex) (+-cong R.refl ey) R.refl R.refl

  shiftDraw-∘ : ∀ p q x → shiftDraw′ p (shiftDraw′ q x) ≈ᵈ shiftDraw′ (q ⊞ p) x
  shiftDraw-∘ p q (rect x y w h s) =
    rect≈ (+-assoc x (proj₁ q) (proj₁ p)) (+-assoc y (proj₂ q) (proj₂ p)) R.refl R.refl
  shiftDraw-∘ p q (circle x y r s) =
    circle≈ (+-assoc x (proj₁ q) (proj₁ p)) (+-assoc y (proj₂ q) (proj₂ p)) R.refl
  shiftDraw-∘ p q (line a b c d s) =
    line≈ (+-assoc a (proj₁ q) (proj₁ p)) (+-assoc b (proj₂ q) (proj₂ p))
          (+-assoc c (proj₁ q) (proj₁ p)) (+-assoc d (proj₂ q) (proj₂ p))
  shiftDraw-∘ p q (arrow a b c d s) =
    arrow≈ (+-assoc a (proj₁ q) (proj₁ p)) (+-assoc b (proj₂ q) (proj₂ p))
           (+-assoc c (proj₁ q) (proj₁ p)) (+-assoc d (proj₂ q) (proj₂ p))
  shiftDraw-∘ p q (label x y n t s) =
    label≈ (+-assoc x (proj₁ q) (proj₁ p)) (+-assoc y (proj₂ q) (proj₂ p))
  shiftDraw-∘ p q (fixed e) = fixed≈

  shiftAnchor-∘ : ∀ p q x → shiftAnchor′ p (shiftAnchor′ q x) ≈ᵃ shiftAnchor′ (q ⊞ p) x
  shiftAnchor-∘ p q (n , box l t w h) =
    refl , box≈ (+-assoc l (proj₁ q) (proj₁ p)) (+-assoc t (proj₂ q) (proj₂ p)) R.refl R.refl

  shiftDraw-0 : ∀ x → shiftDraw′ (0# , 0#) x ≈ᵈ x
  shiftDraw-0 (rect x y w h s)  = rect≈ (+-identityʳ x) (+-identityʳ y) R.refl R.refl
  shiftDraw-0 (circle x y r s)  = circle≈ (+-identityʳ x) (+-identityʳ y) R.refl
  shiftDraw-0 (line a b c d s)  = line≈ (+-identityʳ a) (+-identityʳ b) (+-identityʳ c) (+-identityʳ d)
  shiftDraw-0 (arrow a b c d s) = arrow≈ (+-identityʳ a) (+-identityʳ b) (+-identityʳ c) (+-identityʳ d)
  shiftDraw-0 (label x y n t s) = label≈ (+-identityʳ x) (+-identityʳ y)
  shiftDraw-0 (fixed e)         = fixed≈

  shiftAnchor-0 : ∀ x → shiftAnchor′ (0# , 0#) x ≈ᵃ x
  shiftAnchor-0 (n , box l t w h) = refl , box≈ (+-identityʳ l) (+-identityʳ t) R.refl R.refl

  -- Shifting lists of things: the offsets add, equal offsets agree, shifting by
  -- nothing does nothing, and three lists nested to the right or to the left
  -- agree when the positions add up.
  module Lists {X : Set} {_≈ₓ_ : Rel X 0ℓ} (eqX : IsEquivalence _≈ₓ_)
               (act : S × S → X → X)
               (act-cong : ∀ {p p′} → p ≈ₚ p′ → ∀ x → act p x ≈ₓ act p′ x)
               (act-∘ : ∀ p q x → act p (act q x) ≈ₓ act (q ⊞ p) x)
               (act-0 : ∀ x → act (0# , 0#) x ≈ₓ x) where

    private
      module X = IsEquivalence eqX
      listSetoid : Setoid 0ℓ 0ℓ
      listSetoid = PW.setoid (record { Carrier = X ; _≈_ = _≈ₓ_ ; isEquivalence = eqX })
      module LS = Setoid listSetoid
      infix 4 _≈*_
      _≈*_ = Pointwise _≈ₓ_

    ≡⇒≈* : ∀ {xs ys : List X} → xs ≡ ys → xs ≈* ys
    ≡⇒≈* refl = PW.refl X.refl

    trans* : ∀ {xs ys zs : List X} → xs ≈* ys → ys ≈* zs → xs ≈* zs
    trans* = LS.trans

    map-act-∘ : ∀ p q xs → map (act p) (map (act q) xs) ≈* map (act (q ⊞ p)) xs
    map-act-∘ p q []       = []
    map-act-∘ p q (x ∷ xs) = act-∘ p q x ∷ map-act-∘ p q xs

    map-act-cong : ∀ {p p′} → p ≈ₚ p′ → ∀ xs → map (act p) xs ≈* map (act p′) xs
    map-act-cong e []       = []
    map-act-cong e (x ∷ xs) = act-cong e x ∷ map-act-cong e xs

    map-act-0 : ∀ xs → map (act (0# , 0#)) xs ≈* xs
    map-act-0 []       = []
    map-act-0 (x ∷ xs) = act-0 x ∷ map-act-0 xs

    -- a list shifted by a position that is nothing
    map-act-zero : ∀ {p} → p ≈ₚ (0# , 0#) → ∀ xs → map (act p) xs ≈* xs
    map-act-zero e xs = trans* (map-act-cong e xs) (map-act-0 xs)

    -- a layout inside a combination inside a combination
    assoc3 : ∀ {p₁ p₂ q₁ q₂ r₁ r₂ s₁ s₂} (A B C : List X) →
      p₁ ≈ₚ s₁ ⊞ r₁ → q₁ ⊞ p₂ ≈ₚ s₂ ⊞ r₁ → q₂ ⊞ p₂ ≈ₚ r₂ →
      map (act p₁) A ++ map (act p₂) (map (act q₁) B ++ map (act q₂) C)
        ≈* map (act r₁) (map (act s₁) A ++ map (act s₂) B) ++ map (act r₂) C
    assoc3 {p₁} {p₂} {q₁} {q₂} {r₁} {r₂} {s₁} {s₂} A B C e₁ e₂ e₃ = begin
      map (act p₁) A ++ map (act p₂) (map (act q₁) B ++ map (act q₂) C)
        ≈⟨ PW.++⁺ (PW.refl X.refl) inner ⟩
      map (act p₁) A ++ (map (act (q₁ ⊞ p₂)) B ++ map (act (q₂ ⊞ p₂)) C)
        ≈⟨ PW.++⁺ (map-act-cong e₁ A) (PW.++⁺ (map-act-cong e₂ B) (map-act-cong e₃ C)) ⟩
      map (act (s₁ ⊞ r₁)) A ++ (map (act (s₂ ⊞ r₁)) B ++ map (act r₂) C)
        ≈⟨ ≡⇒≈* (sym (L.++-assoc (map (act (s₁ ⊞ r₁)) A) (map (act (s₂ ⊞ r₁)) B) (map (act r₂) C))) ⟩
      (map (act (s₁ ⊞ r₁)) A ++ map (act (s₂ ⊞ r₁)) B) ++ map (act r₂) C
        ≈⟨ PW.++⁺ (PW.symmetric X.sym outer) (PW.refl X.refl) ⟩
      map (act r₁) (map (act s₁) A ++ map (act s₂) B) ++ map (act r₂) C ∎
      where
        open Reasoning listSetoid
        inner : map (act p₂) (map (act q₁) B ++ map (act q₂) C)
                  ≈* map (act (q₁ ⊞ p₂)) B ++ map (act (q₂ ⊞ p₂)) C
        inner = trans* (≡⇒≈* (L.map-++ (act p₂) (map (act q₁) B) (map (act q₂) C)))
                       (PW.++⁺ (map-act-∘ p₂ q₁ B) (map-act-∘ p₂ q₂ C))
        outer : map (act r₁) (map (act s₁) A ++ map (act s₂) B)
                  ≈* map (act (s₁ ⊞ r₁)) A ++ map (act (s₂ ⊞ r₁)) B
        outer = trans* (≡⇒≈* (L.map-++ (act r₁) (map (act s₁) A) (map (act s₂) B)))
                       (PW.++⁺ (map-act-∘ r₁ s₁ A) (map-act-∘ r₁ s₂ B))

  module DL = Lists ≈ᵈ-isEquivalence shiftDraw′ shiftDraw-cong shiftDraw-∘ shiftDraw-0
  module AL = Lists ≈ᵃ-isEquivalence shiftAnchor′ shiftAnchor-cong shiftAnchor-∘ shiftAnchor-0

  -- Combining three layouts, nested to the right or to the left, gives the same
  -- layout when the sizes agree and the positions add up.
  combine-assoc :
    ∀ {w h w′ h′ w₂ h₂ w₃ h₃ : S} {p₁ p₂ q₁ q₂ r₁ r₂ s₁ s₂ : S × S} (a b c : Layout S) →
    w ≈ w₂ → h ≈ h₂ →
    p₁ ≈ₚ s₁ ⊞ r₁ → q₁ ⊞ p₂ ≈ₚ s₂ ⊞ r₁ → q₂ ⊞ p₂ ≈ₚ r₂ →
    combine w h p₁ a p₂ (combine w′ h′ q₁ b q₂ c)
      ≈ᴸ combine w₂ h₂ r₁ (combine w₃ h₃ s₁ a s₂ b) r₂ c
  combine-assoc a b c ew eh e₁ e₂ e₃ =
    layout≈ ew eh
      (DL.assoc3 (Layout.draws a) (Layout.draws b) (Layout.draws c) e₁ e₂ e₃)
      (AL.assoc3 (Layout.anchors a) (Layout.anchors b) (Layout.anchors c) e₁ e₂ e₃)

  -- A frame holding a layout and an empty spacer is that layout, when the
  -- sizes agree and the layout sits at the origin.
  combine-unitˡ : ∀ {w h pe p} (sw sh : S) (a : Layout S) →
    w ≈ Layout.width a → h ≈ Layout.height a → p ≈ₚ (0# , 0#) →
    combine w h pe (spacer sw sh) p a ≈ᴸ a
  combine-unitˡ sw sh a ew eh ep =
    layout≈ ew eh (DL.map-act-zero ep (Layout.draws a)) (AL.map-act-zero ep (Layout.anchors a))

  combine-unitʳ : ∀ {w h p pe} (a : Layout S) (sw sh : S) →
    w ≈ Layout.width a → h ≈ Layout.height a → p ≈ₚ (0# , 0#) →
    combine w h p a pe (spacer sw sh) ≈ᴸ a
  combine-unitʳ a sw sh ew eh ep =
    layout≈ ew eh
      (DL.trans* (DL.≡⇒≈* (L.++-identityʳ _)) (DL.map-act-zero ep (Layout.draws a)))
      (AL.trans* (AL.≡⇒≈* (L.++-identityʳ _)) (AL.map-act-zero ep (Layout.anchors a)))

  ----------------------------------------------------------------------
  -- Translation is an action

  shift : S → S → Layout S → Layout S
  shift dx dy d = inFrame (width d) (height d) dx dy d

  shift-∘ : ∀ p q d → shift (proj₁ p) (proj₂ p) (shift (proj₁ q) (proj₂ q) d)
                       ≈ᴸ shift (proj₁ (q ⊞ p)) (proj₂ (q ⊞ p)) d
  shift-∘ p q d =
    layout≈ R.refl R.refl (DL.map-act-∘ p q (Layout.draws d)) (AL.map-act-∘ p q (Layout.anchors d))

  shift-0 : ∀ d → shift 0# 0# d ≈ᴸ d
  shift-0 (layout w h ds as) = layout≈ R.refl R.refl (DL.map-act-0 ds) (AL.map-act-0 as)

  ----------------------------------------------------------------------
  -- Ring identities, by the ring solver

  private
    ring′ = fromCommutativeRing ring (λ _ → nothing)

  open NonReflective ring′ using (solve; _⊜_) renaming (_⊕_ to infixl 6 _:+_)

  -- (The solver cannot cancel `x + - x` in an abstract ring, so differences are
  -- kept as opaque terms and cancelled by hand.)
  swap : ∀ o m a b → ((m + a) + (o + b)) ≈ ((o + a) + (m + b))
  swap = λ o m a b →
    solve 4 (λ o m a b → ((m :+ a) :+ (o :+ b)) ⊜ ((o :+ a) :+ (m :+ b))) R.refl o m a b

  +-inverseʳ : ∀ x → (x + neg x) ≈ 0#
  +-inverseʳ = R.-‿inverseʳ

  sub-self : ∀ x → (x - x) ≈ 0#
  sub-self x = R.trans (sub≈ x x) (+-inverseʳ x)

  sub-congˡ : ∀ {o o′} i → o ≈ o′ → (o - i) ≈ (o′ - i)
  sub-congˡ i e = R.trans (sub≈ _ i) (R.trans (+-cong e R.refl) (R.sym (sub≈ _ i)))

  -- placing in the middle frame, then that frame in the outer one
  off-comp : ∀ o m i → ((m - i) + (o - m)) ≈ (o - i)
  off-comp o m i =
    R.trans (+-cong (sub≈ m i) (sub≈ o m))
      (R.trans (swap o m (neg i) (neg m))
        (R.trans (+-cong R.refl (+-inverseʳ m))
          (R.trans (+-identityʳ _) (R.sym (sub≈ o i)))))

  dbl-off-comp : ∀ o m i → (dbl (m - i) + dbl (o - m)) ≈ dbl (o - i)
  dbl-off-comp o m i =
    R.trans (solve 2 (λ x y → ((x :+ x) :+ (y :+ y)) ⊜ ((x :+ y) :+ (x :+ y))) R.refl (m - i) (o - m))
            (+-cong (off-comp o m i) (off-comp o m i))

  vo-comp : ∀ al o m i → (valignOffset al m i + valignOffset al o m) ≈ valignOffset al o i
  vo-comp top    o m i = +-identityʳ 0#
  vo-comp middle o m i = off-comp o m i
  vo-comp bottom o m i = dbl-off-comp o m i

  ao-comp : ∀ al o m i → (alignOffset al m i + alignOffset al o m) ≈ alignOffset al o i
  ao-comp left    o m i = +-identityʳ 0#
  ao-comp centred o m i = off-comp o m i
  ao-comp right   o m i = dbl-off-comp o m i

  vo-congˡ : ∀ al {o o′} i → o ≈ o′ → valignOffset al o i ≈ valignOffset al o′ i
  vo-congˡ top    i e = R.refl
  vo-congˡ middle i e = sub-congˡ i e
  vo-congˡ bottom i e = +-cong (sub-congˡ i e) (sub-congˡ i e)

  ao-congˡ : ∀ al {o o′} i → o ≈ o′ → alignOffset al o i ≈ alignOffset al o′ i
  ao-congˡ left    i e = R.refl
  ao-congˡ centred i e = sub-congˡ i e
  ao-congˡ right   i e = +-cong (sub-congˡ i e) (sub-congˡ i e)

  -- a layout the size of its frame sits at the origin
  vo-zero : ∀ al {h} ha → h ≈ ha → valignOffset al h ha ≈ 0#
  vo-zero top    ha e = R.refl
  vo-zero middle ha e = R.trans (sub-congˡ ha e) (sub-self ha)
  vo-zero bottom ha e =
    R.trans (+-cong (R.trans (sub-congˡ ha e) (sub-self ha)) (R.trans (sub-congˡ ha e) (sub-self ha)))
            (+-identityʳ 0#)

  ao-zero : ∀ al {w} wa → w ≈ wa → alignOffset al w wa ≈ 0#
  ao-zero left    wa e = R.refl
  ao-zero centred wa e = R.trans (sub-congˡ wa e) (sub-self wa)
  ao-zero right   wa e =
    R.trans (+-cong (R.trans (sub-congˡ wa e) (sub-self wa)) (R.trans (sub-congˡ wa e) (sub-self wa)))
            (+-identityʳ 0#)

  ----------------------------------------------------------------------
  -- Associativity of ∥, ═ and ⊙

  -- Three sizes nested to the right and to the left, and an offset `off outer
  -- inner` that composes (`comp`): the three position conditions of
  -- `combine-assoc` for one coordinate.
  module Triple (off : S → S → S) (comp : ∀ o m i → (off m i + off o m) ≈ off o i)
                (off-cong : ∀ {o o′} i → o ≈ o′ → off o i ≈ off o′ i) (a b c : S) where
    W≡ : (a ⊔ (b ⊔ c)) ≈ ((a ⊔ b) ⊔ c)
    W≡ = R.sym (⊔-assoc a b c)

    t₁ : off (a ⊔ (b ⊔ c)) a ≈ (off (a ⊔ b) a + off ((a ⊔ b) ⊔ c) (a ⊔ b))
    t₁ = R.trans (off-cong a W≡) (R.sym (comp ((a ⊔ b) ⊔ c) (a ⊔ b) a))

    t₂ : (off (b ⊔ c) b + off (a ⊔ (b ⊔ c)) (b ⊔ c)) ≈ (off (a ⊔ b) b + off ((a ⊔ b) ⊔ c) (a ⊔ b))
    t₂ = R.trans (comp (a ⊔ (b ⊔ c)) (b ⊔ c) b)
           (R.trans (off-cong b W≡) (R.sym (comp ((a ⊔ b) ⊔ c) (a ⊔ b) b)))

    t₃ : (off (b ⊔ c) c + off (a ⊔ (b ⊔ c)) (b ⊔ c)) ≈ off ((a ⊔ b) ⊔ c) c
    t₃ = R.trans (comp (a ⊔ (b ⊔ c)) (b ⊔ c) c) (off-cong c W≡)

  dbl2 : ∀ a b → (dbl b + dbl a) ≈ dbl (a + b)
  dbl2 = λ a b →
    solve 2 (λ a b → ((b :+ b) :+ (a :+ a)) ⊜ ((a :+ b) :+ (a :+ b))) R.refl a b

  comm0 : ∀ x → (0# + x) ≈ (x + 0#)
  comm0 x = R.trans (+-identityˡ x) (R.sym (+-identityʳ x))

  ∥-assoc : ∀ al a b c →
    besideA al a (besideA al b c) ≈ᴸ besideA al (besideA al a b) c
  ∥-assoc al a b c =
    combine-assoc {w′ = width b + width c} {h′ = height b ⊔ height c}
                  {w₃ = width a + width b} {h₃ = height a ⊔ height b} a b c
      (R.sym (+-assoc (width a) (width b) (width c)))
      (R.sym (⊔-assoc (height a) (height b) (height c)))
      (R.sym (+-identityʳ 0#) , t₁)
      (comm0 _ , t₂)
      (dbl2 (width a) (width b) , t₃)
    where open Triple (valignOffset al) (vo-comp al) (vo-congˡ al) (height a) (height b) (height c)

  ═-assoc : ∀ al a b c →
    aboveA al a (aboveA al b c) ≈ᴸ aboveA al (aboveA al a b) c
  ═-assoc al a b c =
    combine-assoc {w′ = width b ⊔ width c} {h′ = height b + height c}
                  {w₃ = width a ⊔ width b} {h₃ = height a + height b} a b c
      (R.sym (⊔-assoc (width a) (width b) (width c)))
      (R.sym (+-assoc (height a) (height b) (height c)))
      (t₁ , R.sym (+-identityʳ 0#))
      (t₂ , comm0 _)
      (t₃ , dbl2 (height a) (height b))
    where open Triple (alignOffset al) (ao-comp al) (ao-congˡ al) (width a) (width b) (width c)

  ⊙-assoc : ∀ a b c → atop a (atop b c) ≈ᴸ atop (atop a b) c
  ⊙-assoc a b c =
    combine-assoc {w′ = width b ⊔ width c} {h′ = height b ⊔ height c}
                  {w₃ = width a ⊔ width b} {h₃ = height a ⊔ height b} a b c
      (R.sym (⊔-assoc (width a) (width b) (width c)))
      (R.sym (⊔-assoc (height a) (height b) (height c)))
      (X.t₁ , Y.t₁)
      (X.t₂ , Y.t₂)
      (X.t₃ , Y.t₃)
    where module X = Triple _-_ off-comp sub-congˡ (width a) (width b) (width c)
          module Y = Triple _-_ off-comp sub-congˡ (height a) (height b) (height c)

  ----------------------------------------------------------------------
  -- The empty diagram is a unit, for layouts of non-negative size

  Nonneg : S → Set
  Nonneg x = (0# ⊔ x) ≈ x

  nonneg-flip : ∀ {x} → Nonneg x → (x ⊔ 0#) ≈ x
  nonneg-flip n = R.trans (⊔-comm _ 0#) n

  Valid : Layout S → Set
  Valid l = Nonneg (width l) × Nonneg (height l)

  empty : Layout S
  empty = spacer 0# 0#

  ∥-unitˡ : ∀ al a → Valid a → besideA al empty a ≈ᴸ a
  ∥-unitˡ al a (nw , nh) =
    combine-unitˡ {w = 0# + width a} {h = 0# ⊔ height a}
      {pe = 0# , valignOffset al (0# ⊔ height a) 0#}
      {p = dbl 0# , valignOffset al (0# ⊔ height a) (height a)} 0# 0# a
      (+-identityˡ (width a)) nh
      (+-identityʳ 0# , vo-zero al (height a) nh)

  ∥-unitʳ : ∀ al a → Valid a → besideA al a empty ≈ᴸ a
  ∥-unitʳ al a (nw , nh) =
    combine-unitʳ {w = width a + 0#} {h = height a ⊔ 0#}
      {p = 0# , valignOffset al (height a ⊔ 0#) (height a)}
      {pe = dbl (width a) , valignOffset al (height a ⊔ 0#) 0#} a 0# 0#
      (+-identityʳ (width a)) (nonneg-flip nh)
      (R.refl , vo-zero al (height a) (nonneg-flip nh))

  ═-unitˡ : ∀ al a → Valid a → aboveA al empty a ≈ᴸ a
  ═-unitˡ al a (nw , nh) =
    combine-unitˡ {w = 0# ⊔ width a} {h = 0# + height a}
      {pe = alignOffset al (0# ⊔ width a) 0# , 0#}
      {p = alignOffset al (0# ⊔ width a) (width a) , dbl 0#} 0# 0# a
      nw (+-identityˡ (height a))
      (ao-zero al (width a) nw , +-identityʳ 0#)

  ═-unitʳ : ∀ al a → Valid a → aboveA al a empty ≈ᴸ a
  ═-unitʳ al a (nw , nh) =
    combine-unitʳ {w = width a ⊔ 0#} {h = height a + 0#}
      {p = alignOffset al (width a ⊔ 0#) (width a) , 0#}
      {pe = alignOffset al (width a ⊔ 0#) 0# , dbl (height a)} a 0# 0#
      (nonneg-flip nw) (+-identityʳ (height a))
      (ao-zero al (width a) (nonneg-flip nw) , R.refl)

  ⊙-unitˡ : ∀ a → Valid a → atop empty a ≈ᴸ a
  ⊙-unitˡ a (nw , nh) =
    combine-unitˡ {w = 0# ⊔ width a} {h = 0# ⊔ height a}
      {pe = (0# ⊔ width a) - 0# , (0# ⊔ height a) - 0#}
      {p = (0# ⊔ width a) - width a , (0# ⊔ height a) - height a} 0# 0# a nw nh
      (R.trans (sub-congˡ (width a) nw) (sub-self (width a))
      , R.trans (sub-congˡ (height a) nh) (sub-self (height a)))

  ⊙-unitʳ : ∀ a → Valid a → atop a empty ≈ᴸ a
  ⊙-unitʳ a (nw , nh) =
    combine-unitʳ {w = width a ⊔ 0#} {h = height a ⊔ 0#}
      {p = (width a ⊔ 0#) - width a , (height a ⊔ 0#) - height a}
      {pe = (width a ⊔ 0#) - 0# , (height a ⊔ 0#) - 0#} a 0# 0#
      (nonneg-flip nw) (nonneg-flip nh)
      (R.trans (sub-congˡ (width a) (nonneg-flip nw)) (sub-self (width a))
      , R.trans (sub-congˡ (height a) (nonneg-flip nh)) (sub-self (height a)))

  ----------------------------------------------------------------------
  -- Annotations do not change a layout's size or anchors

  named-size : ∀ n d → (width (named n d) ≡ width d) × (height (named n d) ≡ height d)
  named-size n d = refl , refl

  connectP-size : ∀ a pa b pb s d →
    (width (connectP a pa b pb s d) ≡ width d) × (height (connectP a pa b pb s d) ≡ height d)
    × (Layout.anchors (connectP a pa b pb s d) ≡ Layout.anchors d)
  connectP-size a pa b pb s d with findAnchor a (Layout.anchors d) | findAnchor b (Layout.anchors d)
  ... | just _  | just _  = refl , refl , refl
  ... | just _  | nothing = refl , refl , refl
  ... | nothing | _       = refl , refl , refl

  ----------------------------------------------------------------------
  -- Size fusion: the size of a layout is computed from the sizes of its parts

  -- the size algebra: what `layoutAlgebra` does to (width , height), alone
  sizeAlgebra : Algebra S (S × S)
  sizeAlgebra (Rectangle w h _)   _ = w , h
  sizeAlgebra (Disc r _)          _ = dbl r , dbl r
  sizeAlgebra (Segment w h _)     _ = w , h
  sizeAlgebra (Text pct size t _) _ = fromℕ ((textWidth size t *ℕ pct) /ℕ 100) , fromℕ ((size *ℕ 3) /ℕ 2)
  sizeAlgebra (Spacer w h)        _ = w , h
  sizeAlgebra (Raw w h _)         _ = w , h
  sizeAlgebra (Beside _) k =
    proj₁ (k zero) + proj₁ (k (suc zero)) , proj₂ (k zero) ⊔ proj₂ (k (suc zero))
  sizeAlgebra (Above _) k =
    proj₁ (k zero) ⊔ proj₁ (k (suc zero)) , proj₂ (k zero) + proj₂ (k (suc zero))
  sizeAlgebra Atop k =
    proj₁ (k zero) ⊔ proj₁ (k (suc zero)) , proj₂ (k zero) ⊔ proj₂ (k (suc zero))
  sizeAlgebra LabelAbove k =
    proj₁ (k zero) ⊔ (proj₁ (k (suc zero)) ⊔ 0#)
      , proj₂ (k zero) + (proj₂ (k (suc zero)) + proj₂ (k zero))
  sizeAlgebra LabelBelow k =
    0# ⊔ (proj₁ (k (suc zero)) ⊔ proj₁ (k zero))
      , proj₂ (k zero) + (proj₂ (k (suc zero)) + proj₂ (k zero))
  sizeAlgebra (Named _) k = k tt
  sizeAlgebra (Connect _ _ _ _ _) k = k tt

  module LW = Lay.LayoutWith O

  size : Layout S → S × S
  size l = width l , height l

  size-fusion : ∀ d → size (LW.layout d) ≈ₚ fold sizeAlgebra d
  size-fusion (pure ())
  size-fusion (impure (Rectangle _ _ _ , _)) = R.refl , R.refl
  size-fusion (impure (Disc _ _ , _))        = R.refl , R.refl
  size-fusion (impure (Segment _ _ _ , _))   = R.refl , R.refl
  size-fusion (impure (Text _ _ _ _ , _))    = R.refl , R.refl
  size-fusion (impure (Spacer _ _ , _))      = R.refl , R.refl
  size-fusion (impure (Raw _ _ _ , _))       = R.refl , R.refl
  size-fusion (impure (Beside _ , k)) = +-cong w₀ w₁ , ⊔-cong h₀ h₁
    where
    w₀ = proj₁ (size-fusion (k zero))
    h₀ = proj₂ (size-fusion (k zero))
    w₁ = proj₁ (size-fusion (k (suc zero)))
    h₁ = proj₂ (size-fusion (k (suc zero)))
  size-fusion (impure (Above _ , k)) = ⊔-cong w₀ w₁ , +-cong h₀ h₁
    where
    w₀ = proj₁ (size-fusion (k zero))
    h₀ = proj₂ (size-fusion (k zero))
    w₁ = proj₁ (size-fusion (k (suc zero)))
    h₁ = proj₂ (size-fusion (k (suc zero)))
  size-fusion (impure (Atop , k)) = ⊔-cong w₀ w₁ , ⊔-cong h₀ h₁
    where
    w₀ = proj₁ (size-fusion (k zero))
    h₀ = proj₂ (size-fusion (k zero))
    w₁ = proj₁ (size-fusion (k (suc zero)))
    h₁ = proj₂ (size-fusion (k (suc zero)))
  size-fusion (impure (LabelAbove , k)) =
    ⊔-cong w₀ (⊔-cong w₁ R.refl) , +-cong h₀ (+-cong h₁ h₀)
    where
    w₀ = proj₁ (size-fusion (k zero))
    h₀ = proj₂ (size-fusion (k zero))
    w₁ = proj₁ (size-fusion (k (suc zero)))
    h₁ = proj₂ (size-fusion (k (suc zero)))
  size-fusion (impure (LabelBelow , k)) =
    ⊔-cong R.refl (⊔-cong w₁ w₀) , +-cong h₀ (+-cong h₁ h₀)
    where
    w₀ = proj₁ (size-fusion (k zero))
    h₀ = proj₂ (size-fusion (k zero))
    w₁ = proj₁ (size-fusion (k (suc zero)))
    h₁ = proj₂ (size-fusion (k (suc zero)))
  size-fusion (impure (Named n , k)) = size-fusion (k tt)
  size-fusion (impure (Connect a pa b pb s , k)) =
    R.trans (R.reflexive (proj₁ sz)) (proj₁ ih) , R.trans (R.reflexive (proj₁ (proj₂ sz))) (proj₂ ih)
    where ih = size-fusion (k tt)
          sz = connectP-size a pa b pb s (LW.layout (k tt))

-- the laws, for ℤ and ℚ
module ForInts = Proofs intOps lawfulℤ
module ForRats = Proofs ratOps lawfulℚ
