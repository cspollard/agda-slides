{-# OPTIONS --safe --without-K #-}

-- The hero template is the hero frame.
--
-- `Slides.Examples.PairsHero.Frame` writes the frame once, over any scalar with the three layers
-- of `Slides.Diagram.Euclid`.  Such a construction is natural along a homomorphism of scalars
-- (of the core and sub layers, `IsOpsHom`, and of the Euclidean one, `IsEuclidHom`): building
-- the frame and then mapping the scalars is mapping the tick and then building (`frame-natural`).
-- Along `evalD natD (λ _ → t) : DExpr ⊤ → ℕ`, which is such a homomorphism, the template at the
-- variable `tickD` is the flipbook's frame at the tick `t` (`heroT-correct`).  So the shipped
-- template needs no separate trust: with `Slides.Anim.DParamCorrect.discrete-assemblyD` (the
-- frames of the animation are the symbolic layouts evaluated) the page's formulas are the
-- flipbook frames.

module Slides.Examples.PairsHeroNatural where

open import Data.Bool using (Bool; if_then_else_; true; false)
open import Data.List using (List; []; _∷_; zipWith; upTo; foldr)
open import Data.Nat as ℕ using (ℕ; suc; _<ᵇ_; _∸_; _*_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Nat.Show using (show)
open import Data.List using (List)
open import Slides.Diagram using (withClass; defaultStyle)
open import Slides.Diagram.Notation using (east; west)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Slides.Diagram.Scalar
open import Slides.Diagram.Syntax using (Dia; mapDia; atop; spacer; connect; named; disc)
open import Slides.Diagram.Draw using ()
open import Slides.Diagram.Euclid
open import Slides.Examples.PairsHero

module Natural {S T : Set} (D₁ : DiscreteOps S) (D₂ : DiscreteOps T) (h : S → T)
               (HO : IsOpsHom (DiscreteOps.ops D₁) (DiscreteOps.ops D₂) h)
               (HE : IsEuclidHom (DiscreteOps.euclid D₁) (DiscreteOps.euclid D₂) h) where
  private
    module F₁ = Frame D₁
    module F₂ = Frame D₂
    module O₁ = Ops (DiscreteOps.ops D₁)
    module O₂ = Ops (DiscreteOps.ops D₂)
    module E₁ = EuclidOps (DiscreteOps.euclid D₁)
    module E₂ = EuclidOps (DiscreteOps.euclid D₂)
  open IsOpsHom HO
  open IsEuclidHom HE

  cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a a′ b b′ c c′ d d′} →
          a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → f a b c d ≡ f a′ b′ c′ d′
  cong₄ f refl refl refl refl = refl

  sel-natural : ∀ i xs a → h (F₁.sel i xs a) ≡ F₂.sel i xs (h a)
  sel-natural i []           a = h-fromℕ 0
  sel-natural i (x ∷ [])     a = h-fromℕ x
  sel-natural i (x ∷ y ∷ xs) a =
    trans (h-lt a (O₁.fromℕ (suc i)) (O₁.fromℕ x) (F₁.sel (suc i) (y ∷ xs) a))
          (cong₄ E₂.lt refl (h-fromℕ (suc i)) (h-fromℕ x) (sel-natural (suc i) (y ∷ xs) a))

  tri-natural : ∀ t → h (F₁.tri t) ≡ F₂.tri (h t)
  tri-natural t =
    trans (h-lt m (O₁.fromℕ 33) m (O₁.fromℕ period O₁.- m))
          (cong₄ E₂.lt mn (h-fromℕ 33) mn (trans (h-- (O₁.fromℕ period) m) (cong₂ O₂._-_ (h-fromℕ period) mn)))
    where m = E₁.modBy 63 t
          mn = h-modBy 63 t

  private
    ifs : ∀ (b₁ b₂ : Bool) (q : S) → h (if b₁ then O₁.fromℕ 8 O₁.- q else (if b₂ then O₁.fromℕ 0 else q))
          ≡ (if b₁ then O₂.fromℕ 8 O₂.- h q else (if b₂ then O₂.fromℕ 0 else h q))
    ifs true  b₂ q = trans (h-- (O₁.fromℕ 8) q) (cong₂ O₂._-_ (h-fromℕ 8) refl)
    ifs false true  q = h-fromℕ 0
    ifs false false q = refl

  angle-natural : ∀ p t → h (F₁.angle′ p t) ≡ F₂.angle′ p (h t)
  angle-natural p t =
    trans (h-modBy 7 (O₁.fromℕ (Pair.angle p) O₁.+ sp₁))
    (cong (E₂.modBy 7)
      (trans (h-+ (O₁.fromℕ (Pair.angle p)) sp₁)
             (cong₂ O₂._+_ (h-fromℕ (Pair.angle p))
               (trans (ifs (Pair.spin p <ᵇ 1) (Pair.spin p <ᵇ 2) q₁)
                      (cong (λ q → if Pair.spin p <ᵇ 1 then O₂.fromℕ 8 O₂.- q else (if Pair.spin p <ᵇ 2 then O₂.fromℕ 0 else q)) qn)))))
    where
      q₁ = E₁.modBy 7 (E₁.divBy 3 t)
      qn : h q₁ ≡ E₂.modBy 7 (E₂.divBy 3 (h t))
      qn = trans (h-modBy 7 (E₁.divBy 3 t)) (cong (E₂.modBy 7) (h-divBy 3 t))
      sp₁ = if Pair.spin p <ᵇ 1 then O₁.fromℕ 8 O₁.- q₁ else (if Pair.spin p <ᵇ 2 then O₁.fromℕ 0 else q₁)

  sway-natural : ∀ p t → h (F₁.swayD p t) ≡ F₂.swayD p (h t)
  sway-natural p t =
    trans (h-divBy 31 (E₁.mulLit (Pair.amp p) (F₁.tri t)))
          (cong (E₂.divBy 31) (trans (h-mulLit (Pair.amp p) (F₁.tri t)) (cong (E₂.mulLit (Pair.amp p)) (tri-natural t))))

  private
    ifd : ∀ (b : Bool) amp (d : S) →
          h (if b then d else O₁.fromℕ amp O₁.- d) ≡ (if b then h d else O₂.fromℕ amp O₂.- h d)
    ifd true  amp d = refl
    ifd false amp d = trans (h-- (O₁.fromℕ amp) d) (cong₂ O₂._-_ (h-fromℕ amp) refl)

  -- the four coordinates of a pair
  record AtNat (p : Pair) (t : S) : Set where
    v₁ = F₁.at p t
    v₂ = F₂.at p (h t)
    field
      lxN : h (F₁.At.lx v₁) ≡ F₂.At.lx v₂
      lyN : h (F₁.At.ly v₁) ≡ F₂.At.ly v₂
      rxN : h (F₁.At.rx v₁) ≡ F₂.At.rx v₂
      ryN : h (F₁.At.ry v₁) ≡ F₂.At.ry v₂

  at-natural : ∀ p t → AtNat p t
  at-natural p t = record { lxN = lxN ; lyN = lyN ; rxN = rxN ; ryN = ryN }
    where
      open Pair p using (cx; cy; radius; amp; swayX; swayY)
      a₁ = F₁.angle′ p t
      an = angle-natural p t
      d₁ = F₁.swayD p t
      dn = sway-natural p t
      dxN = trans (h-divBy 99 (E₁.mulLit radius (F₁.dirX a₁)))
                  (cong (E₂.divBy 99) (trans (h-mulLit radius (F₁.dirX a₁))
                    (cong (E₂.mulLit radius) (trans (sel-natural 0 tabX a₁) (cong (F₂.sel 0 tabX) an)))))
      dyN = trans (h-divBy 99 (E₁.mulLit radius (F₁.dirY a₁)))
                  (cong (E₂.divBy 99) (trans (h-mulLit radius (F₁.dirY a₁))
                    (cong (E₂.mulLit radius) (trans (sel-natural 0 tabY a₁) (cong (F₂.sel 0 tabY) an)))))
      oxN = trans (h-+ (O₁.fromℕ (cx ∸ amp)) _)
              (cong₂ O₂._+_ (h-fromℕ (cx ∸ amp))
                (trans (ifd swayX amp d₁) (cong (λ x → if swayX then x else O₂.fromℕ amp O₂.- x) dn)))
      oyN = trans (h-+ (O₁.fromℕ (cy ∸ amp)) _)
              (cong₂ O₂._+_ (h-fromℕ (cy ∸ amp))
                (trans (ifd swayY amp d₁) (cong (λ x → if swayY then x else O₂.fromℕ amp O₂.- x) dn)))
      lxN = trans (h-- _ _) (cong₂ O₂._-_ oxN dxN)
      rxN = trans (h-+ _ _) (cong₂ O₂._+_ oxN dxN)
      lyN = trans (h-lt a₁ _ _ _) (cong₄ E₂.lt an (h-fromℕ 5)
              (trans (h-- _ _) (cong₂ O₂._-_ oyN dyN)) (trans (h-+ _ _) (cong₂ O₂._+_ oyN dyN)))
      ryN = trans (h-lt a₁ _ _ _) (cong₄ E₂.lt an (h-fromℕ 5)
              (trans (h-+ _ _) (cong₂ O₂._+_ oyN dyN)) (trans (h-- _ _) (cong₂ O₂._-_ oyN dyN)))

  dot-natural : ∀ name cls r x y → mapDia h (F₁.dot name cls r x y) ≡ F₂.dot name cls r (h x) (h y)
  dot-natural name cls r x y
    rewrite h-- (O₁.fromℕ W) (x O₁.+ O₁.fromℕ (2 * r)) | h-+ x (O₁.fromℕ (2 * r)) | h-fromℕ W | h-fromℕ (r ℕ.+ (r ℕ.+ 0))
          | h-- (O₁.fromℕ H) (y O₁.+ O₁.fromℕ (2 * r)) | h-+ y (O₁.fromℕ (2 * r)) | h-fromℕ H | h-0 | h-fromℕ r
          | h-fromℕ (r ℕ.+ (r ℕ.+ 0)) = refl

  pair-natural : ∀ t i p → mapDia h (F₁.pairAt t i p) ≡ F₂.pairAt (h t) i p
  pair-natural t i p = trans (cong₂ G eqA eqB) refl
    where
      n = at-natural p t
      si = show i
      col = if Pair.blue p then "hero-b" else "hero-r"
      v₁ = F₁.at p t
      G : Dia T → Dia T → Dia T
      G a b = connect ("a" ++ˢ si) east ("b" ++ˢ si) west (withClass "hero-link" defaultStyle) (atop a b)
      eqA : mapDia h (F₁.dot ("a" ++ˢ si) col 5 (F₁.At.lx v₁ O₁.- O₁.fromℕ 5) (F₁.At.ly v₁ O₁.- O₁.fromℕ 5))
            ≡ F₂.dot ("a" ++ˢ si) col 5 (F₂.At.lx (F₂.at p (h t)) O₂.- O₂.fromℕ 5) (F₂.At.ly (F₂.at p (h t)) O₂.- O₂.fromℕ 5)
      eqA = trans (dot-natural _ _ 5 _ _)
              (cong₂ (F₂.dot ("a" ++ˢ si) col 5)
                (trans (h-- _ _) (cong₂ O₂._-_ (AtNat.lxN n) (h-fromℕ 5)))
                (trans (h-- _ _) (cong₂ O₂._-_ (AtNat.lyN n) (h-fromℕ 5))))
      eqB : mapDia h (F₁.dot ("b" ++ˢ si) col 5 (F₁.At.rx v₁ O₁.- O₁.fromℕ 5) (F₁.At.ry v₁ O₁.- O₁.fromℕ 5))
            ≡ F₂.dot ("b" ++ˢ si) col 5 (F₂.At.rx (F₂.at p (h t)) O₂.- O₂.fromℕ 5) (F₂.At.ry (F₂.at p (h t)) O₂.- O₂.fromℕ 5)
      eqB = trans (dot-natural _ _ 5 _ _)
              (cong₂ (F₂.dot ("b" ++ˢ si) col 5)
                (trans (h-- _ _) (cong₂ O₂._-_ (AtNat.rxN n) (h-fromℕ 5)))
                (trans (h-- _ _) (cong₂ O₂._-_ (AtNat.ryN n) (h-fromℕ 5))))

  frame-natural : ∀ n seed t → mapDia h (F₁.heroFrame n seed t) ≡ F₂.heroFrame n seed (h t)
  frame-natural n seed t = go (upTo n) (pairs n seed)
    where
      go : ∀ is ps → mapDia h (foldr atop (spacer (O₁.fromℕ W) (O₁.fromℕ H)) (zipWith (F₁.pairAt t) is ps))
                     ≡ foldr atop (spacer (O₂.fromℕ W) (O₂.fromℕ H)) (zipWith (F₂.pairAt (h t)) is ps)
      go []       ps       = cong₂ spacer (h-fromℕ W) (h-fromℕ H)
      go (i ∷ is) []       = cong₂ spacer (h-fromℕ W) (h-fromℕ H)
      go (i ∷ is) (p ∷ ps) = cong₂ atop (pair-natural t i p) (go is ps)

-- the template at the tick variable, evaluated at the tick `t`, is the flipbook frame
heroT-correct : ∀ n seed t → mapDia (evalD natD (λ _ → t)) (heroT n seed) ≡ Frame.heroFrame natD n seed t
heroT-correct n seed t =
  Natural.frame-natural dexprD natD (evalD natD (λ _ → t)) (evalD-hom natD _) (evalD-euclid-hom natD _) n seed tickD
