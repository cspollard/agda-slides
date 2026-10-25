{-# OPTIONS --safe --without-K #-}

-- Laws of the layout operations (`Slides.Diagram.Place`), for any scalar whose
-- `Ops` form a commutative ring under propositional equality, with an
-- associative maximum (`IsLawful`): ℤ is one (`lawfulℤ`), ℕ is not (its
-- difference is the monus), so ℕ runs the layout but is not covered here.
--
--   * translation is an action: `shift 0 d ≡ d`, `shift a (shift b d) ≡ shift (b + a) d`
--   * `∥`, `═` and `⊙` (with no gap) are associative
--   * annotations do not change a layout's size
--   * the size of a layout is a fold of its own, `sizeAlgebra` (fusion)
--
-- Equality is `_≡_` on `Layout S`: a layout is plain data (sizes, drawing
-- commands, anchors), not a function, so no extensionality is needed.

module Slides.Diagram.Laws where

open import Level using (0ℓ)
open import Algebra using (CommutativeRing; IsCommutativeRing)
open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Properties as ℤP
open import Data.List using (List; []; _∷_; map; _++_)
import Data.List.Properties as L
open import Data.Nat using (ℕ)
open import Data.Maybe using (just; nothing)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Container.FreeMonad using (pure; impure)
open import Data.String using (String)
open import Slides.Diagram.Syntax
  using ( Dia; Algebra; fold; arity; PrimShape; Rectangle; Disc; Segment; Text; Spacer; Raw
        ; Connective; Beside; Above; Atop; Margin; MinWidth; TopAlign; LabelAbove; LabelBelow
        ; Annotation; Named; Connect
        ; VAlign; top; middle; bottom; Align; left; centred; right )
open import Slides.Diagram.TextMetrics using (textWidth)
import Slides.Diagram.Layout as Lay
open import Data.Nat using () renaming (_*_ to _*ℕ_; _/_ to _/ℕ_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Slides.Diagram.Draw
open import Slides.Diagram.Scalar
open import Tactic.RingSolver.Core.AlmostCommutativeRing using (fromCommutativeRing)
import Tactic.RingSolver.NonReflective as NonReflective

-- What the laws need of a scalar `O`: a commutative ring structure on its sum
-- and zero (under `_≡_`, so a layout's equality is `_≡_` too), a difference
-- that is the ring's, and an associative maximum.  The ring operations that
-- `Ops` does not mention (`*`, `1`, negation) are given here.
record IsLawful {S : Set} (O : Ops S) : Set where
  open Ops O
  field
    _*_      : S → S → S
    1#       : S
    neg      : S → S
    isCommutativeRing : IsCommutativeRing _≡_ _+_ _*_ neg 0# 1#
    sub≡     : ∀ a b → a - b ≡ a + neg b
    ⊔-assoc  : ∀ x y z → (x ⊔ y) ⊔ z ≡ x ⊔ (y ⊔ z)

lawfulℤ : IsLawful intOps
lawfulℤ = record
  { _*_ = ℤ._*_ ; 1# = ℤ.+ 1 ; neg = ℤ.-_
  ; isCommutativeRing = ℤP.+-*-isCommutativeRing
  ; sub≡ = λ _ _ → refl
  ; ⊔-assoc = ℤP.⊔-assoc }

module Proofs {S : Set} (O : Ops S) (L : IsLawful O) where
  open Ops O
  open IsLawful L
  open import Slides.Diagram.Place O

  ring : CommutativeRing 0ℓ 0ℓ
  ring = record
    { Carrier = S ; _≈_ = _≡_ ; _+_ = _+_ ; _*_ = _*_ ; -_ = neg ; 0# = 0# ; 1# = 1#
    ; isCommutativeRing = isCommutativeRing }

  module R = CommutativeRing ring

  -- add the offsets of two shifts
  infixl 6 _⊞_
  _⊞_ : S × S → S × S → S × S
  p ⊞ q = proj₁ p + proj₁ q , proj₂ p + proj₂ q

  +-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
  +-assoc x y z = R.+-assoc x y z

  +-identityʳ : ∀ x → x + 0# ≡ x
  +-identityʳ x = R.+-identityʳ x

  ----------------------------------------------------------------------
  -- Translation is an action

  shiftDraw′ : S × S → Draw S → Draw S
  shiftDraw′ p = shiftDraw (proj₁ p) (proj₂ p)

  shiftAnchor′ : S × S → String × Box S → String × Box S
  shiftAnchor′ p = shiftAnchor (proj₁ p) (proj₂ p)

  cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a′ b b′ c c′} →
          a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
  cong₃ f refl refl refl = refl

  cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a a′ b b′ c c′ d d′} →
          a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → f a b c d ≡ f a′ b′ c′ d′
  cong₄ f refl refl refl refl = refl

  shiftDraw-∘ : ∀ p q x → shiftDraw′ p (shiftDraw′ q x) ≡ shiftDraw′ (q ⊞ p) x
  shiftDraw-∘ p q (rect x y w h s) =
    cong₂ (λ a b → rect a b w h s) (+-assoc x (proj₁ q) (proj₁ p)) (+-assoc y (proj₂ q) (proj₂ p))
  shiftDraw-∘ p q (circle x y r s) =
    cong₂ (λ a b → circle a b r s) (+-assoc x (proj₁ q) (proj₁ p)) (+-assoc y (proj₂ q) (proj₂ p))
  shiftDraw-∘ p q (line a b c d s) =
    cong₄ (λ a b c d → line a b c d s)
      (+-assoc a (proj₁ q) (proj₁ p)) (+-assoc b (proj₂ q) (proj₂ p))
      (+-assoc c (proj₁ q) (proj₁ p)) (+-assoc d (proj₂ q) (proj₂ p))
  shiftDraw-∘ p q (arrow a b c d s) =
    cong₄ (λ a b c d → arrow a b c d s)
      (+-assoc a (proj₁ q) (proj₁ p)) (+-assoc b (proj₂ q) (proj₂ p))
      (+-assoc c (proj₁ q) (proj₁ p)) (+-assoc d (proj₂ q) (proj₂ p))
  shiftDraw-∘ p q (label x y n t s) =
    cong₂ (λ a b → label a b n t s) (+-assoc x (proj₁ q) (proj₁ p)) (+-assoc y (proj₂ q) (proj₂ p))
  shiftDraw-∘ p q (fixed e) = refl

  shiftAnchor-∘ : ∀ p q x → shiftAnchor′ p (shiftAnchor′ q x) ≡ shiftAnchor′ (q ⊞ p) x
  shiftAnchor-∘ p q (n , box l t w h) =
    cong (λ b → n , b) (cong₂ (λ a b → box a b w h) (+-assoc l (proj₁ q) (proj₁ p)) (+-assoc t (proj₂ q) (proj₂ p)))

  -- shifting a list of things, one after the other, adds the offsets
  module _ {X : Set} (act : S × S → X → X)
           (act-∘ : ∀ p q x → act p (act q x) ≡ act (q ⊞ p) x) where

    map-act-∘ : ∀ p q xs → map (act p) (map (act q) xs) ≡ map (act (q ⊞ p)) xs
    map-act-∘ p q xs = trans (sym (L.map-∘ xs)) (L.map-cong (act-∘ p q) xs)

    -- a layout inside a combination inside a combination
    assoc3 : ∀ p₁ p₂ q₁ q₂ r₁ r₂ s₁ s₂ (A B C : List X) →
      p₁ ≡ s₁ ⊞ r₁ → q₁ ⊞ p₂ ≡ s₂ ⊞ r₁ → q₂ ⊞ p₂ ≡ r₂ →
      map (act p₁) A ++ map (act p₂) (map (act q₁) B ++ map (act q₂) C)
        ≡ map (act r₁) (map (act s₁) A ++ map (act s₂) B) ++ map (act r₂) C
    assoc3 p₁ p₂ q₁ q₂ r₁ r₂ s₁ s₂ A B C e₁ e₂ e₃ = begin
      map (act p₁) A ++ map (act p₂) (map (act q₁) B ++ map (act q₂) C)
        ≡⟨ cong (map (act p₁) A ++_) inner ⟩
      map (act p₁) A ++ (map (act (q₁ ⊞ p₂)) B ++ map (act (q₂ ⊞ p₂)) C)
        ≡⟨ cong₃ (λ x y z → map (act x) A ++ (map (act y) B ++ map (act z) C)) e₁ e₂ e₃ ⟩
      map (act (s₁ ⊞ r₁)) A ++ (map (act (s₂ ⊞ r₁)) B ++ map (act r₂) C)
        ≡⟨ sym (L.++-assoc (map (act (s₁ ⊞ r₁)) A) (map (act (s₂ ⊞ r₁)) B) (map (act r₂) C)) ⟩
      (map (act (s₁ ⊞ r₁)) A ++ map (act (s₂ ⊞ r₁)) B) ++ map (act r₂) C
        ≡⟨ cong (_++ map (act r₂) C) (sym outer) ⟩
      map (act r₁) (map (act s₁) A ++ map (act s₂) B) ++ map (act r₂) C ∎
      where
        inner : map (act p₂) (map (act q₁) B ++ map (act q₂) C)
                  ≡ map (act (q₁ ⊞ p₂)) B ++ map (act (q₂ ⊞ p₂)) C
        inner = trans (L.map-++ (act p₂) (map (act q₁) B) (map (act q₂) C))
                      (cong₂ _++_ (map-act-∘ p₂ q₁ B) (map-act-∘ p₂ q₂ C))
        outer : map (act r₁) (map (act s₁) A ++ map (act s₂) B)
                  ≡ map (act (s₁ ⊞ r₁)) A ++ map (act (s₂ ⊞ r₁)) B
        outer = trans (L.map-++ (act r₁) (map (act s₁) A) (map (act s₂) B))
                      (cong₂ _++_ (map-act-∘ r₁ s₁ A) (map-act-∘ r₁ s₂ B))

  -- Combining three layouts, nested to the right or to the left, gives the same
  -- layout when the sizes agree and the positions add up.
  combine-assoc :
    ∀ {w h w′ h′ w₂ h₂ w₃ h₃ : S} {p₁ p₂ q₁ q₂ r₁ r₂ s₁ s₂ : S × S} (a b c : Layout S) →
    w ≡ w₂ → h ≡ h₂ →
    p₁ ≡ s₁ ⊞ r₁ → q₁ ⊞ p₂ ≡ s₂ ⊞ r₁ → q₂ ⊞ p₂ ≡ r₂ →
    combine w h p₁ a p₂ (combine w′ h′ q₁ b q₂ c)
      ≡ combine w₂ h₂ r₁ (combine w₃ h₃ s₁ a s₂ b) r₂ c
  combine-assoc {p₁ = p₁} {p₂} {q₁} {q₂} {r₁} {r₂} {s₁} {s₂} a b c refl refl e₁ e₂ e₃ =
    cong₂ (layout _ _)
      (assoc3 shiftDraw′ shiftDraw-∘ p₁ p₂ q₁ q₂ r₁ r₂ s₁ s₂
         (Layout.draws a) (Layout.draws b) (Layout.draws c) e₁ e₂ e₃)
      (assoc3 shiftAnchor′ shiftAnchor-∘ p₁ p₂ q₁ q₂ r₁ r₂ s₁ s₂
         (Layout.anchors a) (Layout.anchors b) (Layout.anchors c) e₁ e₂ e₃)

  ----------------------------------------------------------------------
  -- Translation is an action

  shift : S → S → Layout S → Layout S
  shift dx dy d = inFrame (width d) (height d) dx dy d

  shift-∘ : ∀ p q d → shift (proj₁ p) (proj₂ p) (shift (proj₁ q) (proj₂ q) d)
                       ≡ shift (proj₁ (q ⊞ p)) (proj₂ (q ⊞ p)) d
  shift-∘ p q d =
    cong₂ (layout (width d) (height d))
      (map-act-∘ shiftDraw′ shiftDraw-∘ p q (Layout.draws d))
      (map-act-∘ shiftAnchor′ shiftAnchor-∘ p q (Layout.anchors d))

  shiftDraw-0 : ∀ x → shiftDraw 0# 0# x ≡ x
  shiftDraw-0 (rect x y w h s)       = cong₂ (λ a b → rect a b w h s) (+-identityʳ x) (+-identityʳ y)
  shiftDraw-0 (circle x y r s)       = cong₂ (λ a b → circle a b r s) (+-identityʳ x) (+-identityʳ y)
  shiftDraw-0 (line a b c d s)       =
    cong₄ (λ a b c d → line a b c d s) (+-identityʳ a) (+-identityʳ b) (+-identityʳ c) (+-identityʳ d)
  shiftDraw-0 (arrow a b c d s)      =
    cong₄ (λ a b c d → arrow a b c d s) (+-identityʳ a) (+-identityʳ b) (+-identityʳ c) (+-identityʳ d)
  shiftDraw-0 (label x y n t s)      = cong₂ (λ a b → label a b n t s) (+-identityʳ x) (+-identityʳ y)
  shiftDraw-0 (fixed e)              = refl

  shiftAnchor-0 : ∀ x → shiftAnchor 0# 0# x ≡ x
  shiftAnchor-0 (n , box l t w h) =
    cong (λ b → n , b) (cong₂ (λ a b → box a b w h) (+-identityʳ l) (+-identityʳ t))

  shift-0 : ∀ d → shift 0# 0# d ≡ d
  shift-0 (layout w h ds as) =
    cong₂ (layout w h)
      (trans (L.map-cong shiftDraw-0 ds) (L.map-id ds))
      (trans (L.map-cong shiftAnchor-0 as) (L.map-id as))

  ----------------------------------------------------------------------
  -- Ring identities, by the ring solver

  private
    ring′ = fromCommutativeRing ring (λ _ → nothing)

  open NonReflective ring′ using (solve; _⊜_; Κ) renaming (_⊕_ to infixl 6 _:+_; ⊝_ to infixr 8 :-_)

  +-identityˡ : ∀ x → 0# + x ≡ x
  +-identityˡ x = R.+-identityˡ x

  -- (The solver cannot cancel `x + - x` in an abstract ring, so differences are
  -- kept as opaque terms and cancelled by hand.)
  swap : ∀ o m a b → (m + a) + (o + b) ≡ (o + a) + (m + b)
  swap = λ o m a b →
    solve 4 (λ o m a b → ((m :+ a) :+ (o :+ b)) ⊜ ((o :+ a) :+ (m :+ b))) R.refl o m a b

  +-inverseʳ : ∀ x → x + neg x ≡ 0#
  +-inverseʳ x = R.-‿inverseʳ x

  -- placing in the middle frame, then that frame in the outer one
  off-comp : ∀ o m i → (m - i) + (o - m) ≡ o - i
  off-comp o m i =
    trans (cong₂ _+_ (sub≡ m i) (sub≡ o m))
      (trans (swap o m (neg i) (neg m))
        (trans (cong (λ t → (o + neg i) + t) (+-inverseʳ m))
          (trans (+-identityʳ _) (sym (sub≡ o i)))))

  dbl-off-comp : ∀ o m i → dbl (m - i) + dbl (o - m) ≡ dbl (o - i)
  dbl-off-comp o m i =
    trans (solve 2 (λ x y → ((x :+ x) :+ (y :+ y)) ⊜ ((x :+ y) :+ (x :+ y))) R.refl (m - i) (o - m))
          (cong (λ t → t + t) (off-comp o m i))

  vo-comp : ∀ al o m i → valignOffset al m i + valignOffset al o m ≡ valignOffset al o i
  vo-comp top    o m i = +-identityʳ 0#
  vo-comp middle o m i = off-comp o m i
  vo-comp bottom o m i = dbl-off-comp o m i

  ao-comp : ∀ al o m i → alignOffset al m i + alignOffset al o m ≡ alignOffset al o i
  ao-comp left    o m i = +-identityʳ 0#
  ao-comp centred o m i = off-comp o m i
  ao-comp right   o m i = dbl-off-comp o m i

  ----------------------------------------------------------------------
  -- Associativity of ∥, ═ and ⊙

  -- Three sizes nested to the right and to the left, and an offset `off outer
  -- inner` that composes (`comp`): the three position conditions of
  -- `combine-assoc` for one coordinate.
  module Triple (off : S → S → S) (comp : ∀ o m i → off m i + off o m ≡ off o i) (a b c : S) where
    W≡ : a ⊔ (b ⊔ c) ≡ (a ⊔ b) ⊔ c
    W≡ = sym (⊔-assoc a b c)

    t₁ : off (a ⊔ (b ⊔ c)) a ≡ off (a ⊔ b) a + off ((a ⊔ b) ⊔ c) (a ⊔ b)
    t₁ = trans (cong (λ t → off t a) W≡) (sym (comp ((a ⊔ b) ⊔ c) (a ⊔ b) a))

    t₂ : off (b ⊔ c) b + off (a ⊔ (b ⊔ c)) (b ⊔ c) ≡ off (a ⊔ b) b + off ((a ⊔ b) ⊔ c) (a ⊔ b)
    t₂ = trans (comp (a ⊔ (b ⊔ c)) (b ⊔ c) b)
           (trans (cong (λ t → off t b) W≡) (sym (comp ((a ⊔ b) ⊔ c) (a ⊔ b) b)))

    t₃ : off (b ⊔ c) c + off (a ⊔ (b ⊔ c)) (b ⊔ c) ≡ off ((a ⊔ b) ⊔ c) c
    t₃ = trans (comp (a ⊔ (b ⊔ c)) (b ⊔ c) c) (cong (λ t → off t c) W≡)

  -- sizes that add: `(a + z) + ((b + z) + c)` and the like, with `z` the zero
  sum3 : ∀ a b c z → (a + z) + ((b + z) + c) ≡ (((a + z) + b) + z) + c
  sum3 = λ a b c z →
    solve 4 (λ a b c z → ((a :+ z) :+ ((b :+ z) :+ c)) ⊜ ((((a :+ z) :+ b) :+ z) :+ c)) R.refl a b c z

  dbl3 : ∀ a b z → dbl (b + z) + dbl (a + z) ≡ dbl (((a + z) + b) + z)
  dbl3 = λ a b z →
    solve 3 (λ a b z → (((b :+ z) :+ (b :+ z)) :+ ((a :+ z) :+ (a :+ z)))
                         ⊜ ((((a :+ z) :+ b) :+ z) :+ (((a :+ z) :+ b) :+ z))) R.refl a b z

  comm0 : ∀ x → 0# + x ≡ x + 0#
  comm0 x = trans (+-identityˡ x) (sym (+-identityʳ x))

  ∥-assoc : ∀ al a b c →
    besideA al 0# a (besideA al 0# b c) ≡ besideA al 0# (besideA al 0# a b) c
  ∥-assoc al a b c =
    combine-assoc {w′ = width b + 0# + width c} {h′ = height b ⊔ height c}
                  {w₃ = width a + 0# + width b} {h₃ = height a ⊔ height b} a b c
      (sum3 (width a) (width b) (width c) 0#)
      (sym (⊔-assoc (height a) (height b) (height c)))
      (cong₂ _,_ (sym (+-identityʳ 0#)) t₁)
      (cong₂ _,_ (comm0 _) t₂)
      (cong₂ _,_ (dbl3 (width a) (width b) 0#) t₃)
    where open Triple (valignOffset al) (vo-comp al) (height a) (height b) (height c)

  ═-assoc : ∀ al a b c →
    aboveA al 0# a (aboveA al 0# b c) ≡ aboveA al 0# (aboveA al 0# a b) c
  ═-assoc al a b c =
    combine-assoc {w′ = width b ⊔ width c} {h′ = height b + 0# + height c}
                  {w₃ = width a ⊔ width b} {h₃ = height a + 0# + height b} a b c
      (sym (⊔-assoc (width a) (width b) (width c)))
      (sum3 (height a) (height b) (height c) 0#)
      (cong₂ _,_ t₁ (sym (+-identityʳ 0#)))
      (cong₂ _,_ t₂ (comm0 _))
      (cong₂ _,_ t₃ (dbl3 (height a) (height b) 0#))
    where open Triple (alignOffset al) (ao-comp al) (width a) (width b) (width c)

  ⊙-assoc : ∀ a b c → atop a (atop b c) ≡ atop (atop a b) c
  ⊙-assoc a b c =
    combine-assoc {w′ = width b ⊔ width c} {h′ = height b ⊔ height c}
                  {w₃ = width a ⊔ width b} {h₃ = height a ⊔ height b} a b c
      (sym (⊔-assoc (width a) (width b) (width c)))
      (sym (⊔-assoc (height a) (height b) (height c)))
      (cong₂ _,_ (X.t₁) (Y.t₁))
      (cong₂ _,_ (X.t₂) (Y.t₂))
      (cong₂ _,_ (X.t₃) (Y.t₃))
    where module X = Triple _-_ off-comp (width a) (width b) (width c)
          module Y = Triple _-_ off-comp (height a) (height b) (height c)

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
  sizeAlgebra : Algebra (S × S)
  sizeAlgebra = record { prim = sizePrim ; connective = sizeConnective ; annotation = λ _ sz → sz }
    where
    sizePrim : PrimShape → S × S
    sizePrim (Rectangle w h _)   = fromℕ w , fromℕ h
    sizePrim (Disc r _)          = dbl (fromℕ r) , dbl (fromℕ r)
    sizePrim (Segment w h _)     = fromℕ w , fromℕ h
    sizePrim (Text pct size t _) = fromℕ ((textWidth size t *ℕ pct) /ℕ 100) , fromℕ ((size *ℕ 3) /ℕ 2)
    sizePrim (Spacer w h)        = fromℕ w , fromℕ h
    sizePrim (Raw w h _)         = fromℕ w , fromℕ h

    sizeConnective : (c : Connective) → (Fin (arity c) → S × S) → S × S
    sizeConnective (Beside _ g) k =
      proj₁ (k zero) + fromℕ g + proj₁ (k (suc zero)) , proj₂ (k zero) ⊔ proj₂ (k (suc zero))
    sizeConnective (Above _ g) k =
      proj₁ (k zero) ⊔ proj₁ (k (suc zero)) , proj₂ (k zero) + fromℕ g + proj₂ (k (suc zero))
    sizeConnective Atop k =
      proj₁ (k zero) ⊔ proj₁ (k (suc zero)) , proj₂ (k zero) ⊔ proj₂ (k (suc zero))
    sizeConnective (Margin l t r b) k =
      fromℕ l + proj₁ (k zero) + fromℕ r , fromℕ t + proj₂ (k zero) + fromℕ b
    sizeConnective (MinWidth w) k = fromℕ w ⊔ proj₁ (k zero) , proj₂ (k zero)
    sizeConnective (TopAlign h) k = proj₁ (k zero) , fromℕ h ⊔ proj₂ (k zero)
    sizeConnective (LabelAbove g) k =
      proj₁ (k zero) ⊔ (proj₁ (k (suc zero)) ⊔ 0#)
        , proj₂ (k zero) + fromℕ g + (proj₂ (k (suc zero)) + fromℕ g + proj₂ (k zero))
    sizeConnective (LabelBelow g) k =
      0# ⊔ (proj₁ (k (suc zero)) ⊔ proj₁ (k zero))
        , proj₂ (k zero) + fromℕ g + (proj₂ (k (suc zero)) + fromℕ g + proj₂ (k zero))

  module LW = Lay.LayoutWith O

  size : Layout S → S × S
  size l = width l , height l

  size-fusion : ∀ d → size (LW.layout d) ≡ fold sizeAlgebra d
  size-fusion (pure ())
  size-fusion (impure (inj₁ p , _)) = prim p
    where
    prim : ∀ p → size (LW.layoutAlgebra .Algebra.prim p) ≡ sizeAlgebra .Algebra.prim p
    prim (Rectangle _ _ _) = refl
    prim (Disc _ _)        = refl
    prim (Segment _ _ _)   = refl
    prim (Text _ _ _ _)    = refl
    prim (Spacer _ _)      = refl
    prim (Raw _ _ _)       = refl
  size-fusion (impure (inj₂ (inj₁ (Beside _ g)) , k)) =
    cong₂ _,_ (cong₂ (λ x y → x + fromℕ g + y) w₀ w₁) (cong₂ _⊔_ h₀ h₁)
    where
    w₀ = cong proj₁ (size-fusion (k zero))
    h₀ = cong proj₂ (size-fusion (k zero))
    w₁ = cong proj₁ (size-fusion (k (suc zero)))
    h₁ = cong proj₂ (size-fusion (k (suc zero)))
  size-fusion (impure (inj₂ (inj₁ (Above _ g)) , k)) =
    cong₂ _,_ (cong₂ _⊔_ w₀ w₁) (cong₂ (λ x y → x + fromℕ g + y) h₀ h₁)
    where
    w₀ = cong proj₁ (size-fusion (k zero))
    h₀ = cong proj₂ (size-fusion (k zero))
    w₁ = cong proj₁ (size-fusion (k (suc zero)))
    h₁ = cong proj₂ (size-fusion (k (suc zero)))
  size-fusion (impure (inj₂ (inj₁ Atop) , k)) =
    cong₂ _,_ (cong₂ _⊔_ w₀ w₁) (cong₂ _⊔_ h₀ h₁)
    where
    w₀ = cong proj₁ (size-fusion (k zero))
    h₀ = cong proj₂ (size-fusion (k zero))
    w₁ = cong proj₁ (size-fusion (k (suc zero)))
    h₁ = cong proj₂ (size-fusion (k (suc zero)))
  size-fusion (impure (inj₂ (inj₁ (Margin l t r b)) , k)) =
    cong₂ _,_ (cong (λ x → fromℕ l + x + fromℕ r) w₀) (cong (λ y → fromℕ t + y + fromℕ b) h₀)
    where
    w₀ = cong proj₁ (size-fusion (k zero))
    h₀ = cong proj₂ (size-fusion (k zero))
  size-fusion (impure (inj₂ (inj₁ (MinWidth w)) , k)) =
    cong₂ _,_ (cong (λ x → fromℕ w ⊔ x) w₀) h₀
    where
    w₀ = cong proj₁ (size-fusion (k zero))
    h₀ = cong proj₂ (size-fusion (k zero))
  size-fusion (impure (inj₂ (inj₁ (TopAlign h)) , k)) =
    cong₂ _,_ w₀ (cong (λ y → fromℕ h ⊔ y) h₀)
    where
    w₀ = cong proj₁ (size-fusion (k zero))
    h₀ = cong proj₂ (size-fusion (k zero))
  size-fusion (impure (inj₂ (inj₁ (LabelAbove g)) , k)) =
    cong₂ _,_ (cong₂ (λ x y → x ⊔ (y ⊔ 0#)) w₀ w₁)
              (cong₂ (λ x y → x + fromℕ g + (y + fromℕ g + x)) h₀ h₁)
    where
    w₀ = cong proj₁ (size-fusion (k zero))
    h₀ = cong proj₂ (size-fusion (k zero))
    w₁ = cong proj₁ (size-fusion (k (suc zero)))
    h₁ = cong proj₂ (size-fusion (k (suc zero)))
  size-fusion (impure (inj₂ (inj₁ (LabelBelow g)) , k)) =
    cong₂ _,_ (cong₂ (λ x y → 0# ⊔ (y ⊔ x)) w₀ w₁)
              (cong₂ (λ x y → x + fromℕ g + (y + fromℕ g + x)) h₀ h₁)
    where
    w₀ = cong proj₁ (size-fusion (k zero))
    h₀ = cong proj₂ (size-fusion (k zero))
    w₁ = cong proj₁ (size-fusion (k (suc zero)))
    h₁ = cong proj₂ (size-fusion (k (suc zero)))
  size-fusion (impure (inj₂ (inj₂ a) , k)) = ann a
    where
    ih = size-fusion (k tt)
    ann : ∀ a → size (LW.layoutAlgebra .Algebra.annotation a (LW.layout (k tt)))
                  ≡ sizeAlgebra .Algebra.annotation a (fold sizeAlgebra (k tt))
    ann (Named n)           = ih
    ann (Connect a pa b pb s) = trans (cong₂ _,_ (proj₁ sz) (proj₁ (proj₂ sz))) ih
      where sz = connectP-size a pa b pb s (LW.layout (k tt))

-- the laws, for ℤ
module ForInts = Proofs intOps lawfulℤ
