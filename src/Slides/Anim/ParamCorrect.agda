{-# OPTIONS --safe --without-K #-}

-- The assembly of whole frames, discrete reading: the symbolic frames of `Slides.Anim.Param`
-- are the frames of the animation.
--
-- Statement (A).  Let `a` be an animation of templates (every segment `template`, so that
-- `Slides.Anim.Param.leaves` succeeds: `leaves 0 0 a ≡ just (n , l)`).  `l` is the same
-- animation with each segment replaced by a `Leaf` (its variable `idx`, its start tick, its
-- track, its template), and `symbolicFrames l` the list of symbolic frames, one per tick.
-- For every tick `k < dur a`:
--
--     layout_ℕ (frame k of  timeline atop (frames natOps) a)
--       ≡  mapLayout (eval ρ) (layout_Expr (symbolic frame k))
--
-- for every assignment `ρ` such that, for every leaf running at tick `k`
-- (`start + m ≡ k`, `m < dur (track)`), `ρ (idx) ≡ units (sample of its track at m)`
-- (`GoodL l k ρ`).  The right-hand side is exactly what the page computes (evaluate the
-- symbolic layout at the parameters), and the left is the existing discrete frame.
--
--   * `discrete-assembly`: the statement, tick by tick.
--   * `leaves-agree`: the same for all ticks at once, as `Agree`, a relation between the list of
--     frames and the list of symbolic frames, which is what the induction carries.
--   * `paramOf-assembly`: for the animation `render` ships (`paramOf acts`), against the frames
--     `render` shows (`concat (map (timeline atop (frames natOps)) acts)`).
--
-- The hypothesis `GoodL l k ρ` is *only* about the leaves running at tick `k`, and says nothing
-- about the others: segments that are not running at `k` do not occur in the frame.  It is
-- satisfiable (the leaves are numbered apart: `leaves-idx`, `canonical-good`); it is a hypothesis
-- on `ρ`, not on the animation, so nothing is assumed about templates besides being templates.
--
-- The proof is the induction the module header of `Slides.Anim.Param` promised.  Lists of frames
-- are read as partial functions of the tick (`nth`): `nth` sends `++` to "first, then the second
-- with the tick shifted" (`nth-++`) and `merge` to the pointwise `mergeM` (`nth-merge`), the
-- same algebra the continuous semantics uses (`Slides.Anim.Continuous.parAt`).  Layout commutes
-- with evaluation (`Slides.Diagram.LayoutNatural.layout-natural`, in particular its `atop` case),
-- and one segment is `leaf-agrees`.

module Slides.Anim.ParamCorrect where

open import Data.Bool using (Bool; true; false; if_then_else_)
import Data.Bool
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map; applyUpTo; concat)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_; _≤_)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (zero; suc)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Slides.Diagram.Draw using (Layout; mapLayout)
open import Slides.Diagram.Syntax using (Dia; atop; mapDia)
open import Slides.Diagram.Expr using (Expr; exprOps; eval; eval-hom)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (Ops; natOps)
open import Slides.Diagram.LayoutNatural using (layout-natural; layout-eval; atop-natural)
import Slides.Diagram.Place natOps as PN
import Slides.Anim.Track as T
open import Slides.Anim.Syntax
open import Slides.Anim.Timeline using (timeline; merge; frames; length-dur)
open import Slides.Anim.Param
open import Slides.Anim.Continuous using (mergeM)

private
  layoutℕ : Dia ℕ → Layout ℕ
  layoutℕ = LayoutWith.layout natOps

  layoutE : Dia (Expr ℕ) → Layout (Expr ℕ)
  layoutE = LayoutWith.layout exprOps

------------------------------------------------------------------------
-- Lists of frames as partial functions of the tick

nth : ∀ {A : Set} → List A → ℕ → Maybe A
nth []       _       = nothing
nth (x ∷ xs) zero    = just x
nth (x ∷ xs) (suc j) = nth xs j

nth-++ : ∀ {A : Set} (xs ys : List A) j →
         nth (xs ++ ys) j ≡ (if j <ᵇ length xs then nth xs j else nth ys (j ∸ length xs))
nth-++ []       ys j       = refl
nth-++ (x ∷ xs) ys zero    = refl
nth-++ (x ∷ xs) ys (suc j) = nth-++ xs ys j

private
  mergeM-nothingʳ : ∀ {F : Set} (_⊙_ : F → F → F) m → mergeM _⊙_ m nothing ≡ m
  mergeM-nothingʳ _⊙_ nothing  = refl
  mergeM-nothingʳ _⊙_ (just x) = refl

nth-merge : ∀ {F : Set} (_⊙_ : F → F → F) (xs ys : List F) j →
            nth (merge _⊙_ xs ys) j ≡ mergeM _⊙_ (nth xs j) (nth ys j)
nth-merge _⊙_ []       ys       j       = refl
nth-merge _⊙_ (x ∷ xs) []       j       = sym (mergeM-nothingʳ _⊙_ (nth (x ∷ xs) j))
nth-merge _⊙_ (x ∷ xs) (y ∷ ys) zero    = refl
nth-merge _⊙_ (x ∷ xs) (y ∷ ys) (suc j) = nth-merge _⊙_ xs ys j

nth-replicate : ∀ {A : Set} n (y : A) j → nth (replicate n y) j ≡ (if j <ᵇ n then just y else nothing)
nth-replicate zero    y j       = refl
nth-replicate (suc n) y zero    = refl
nth-replicate (suc n) y (suc j) = nth-replicate n y j

nth-applyUpTo : ∀ {A : Set} (f : ℕ → A) n j →
                nth (applyUpTo f n) j ≡ (if j <ᵇ n then just (f j) else nothing)
nth-applyUpTo f zero    j       = refl
nth-applyUpTo f (suc n) zero    = refl
nth-applyUpTo f (suc n) (suc j) = nth-applyUpTo (λ i → f (suc i)) n j

nth-map : ∀ {A B : Set} (g : A → B) xs j → nth (map g xs) j ≡ Maybe.map g (nth xs j)
nth-map g []       j       = refl
nth-map g (x ∷ xs) zero    = refl
nth-map g (x ∷ xs) (suc j) = nth-map g xs j

private
  map-if : ∀ {A B : Set} (g : A → B) b (x : A) →
           Maybe.map g (if b then just x else nothing) ≡ (if b then just (g x) else nothing)
  map-if g true  x = refl
  map-if g false x = refl

-- the frames of a segment, tick by tick
nth-frames : ∀ {S} (O : Ops S) (s : Seg S) j →
             nth (frames O s) j
             ≡ (if j <ᵇ proj₁ (T.sample T.ℚLerp (track s))
                then just (body O s (proj₂ (T.sample T.ℚLerp (track s)) j)) else nothing)
nth-frames O s j =
  trans (nth-map (λ t → body O s (proj₂ (T.sample T.ℚLerp (track s)) t))
                 (applyUpTo (λ i → i) (proj₁ (T.sample T.ℚLerp (track s)))) j)
  (trans (cong (Maybe.map (λ t → body O s (proj₂ (T.sample T.ℚLerp (track s)) t)))
               (nth-applyUpTo (λ i → i) (proj₁ (T.sample T.ℚLerp (track s))) j))
         (map-if (λ t → body O s (proj₂ (T.sample T.ℚLerp (track s)) t)) (j <ᵇ proj₁ (T.sample T.ℚLerp (track s))) j))

------------------------------------------------------------------------
-- Agreement of a list of frames with a list of symbolic frames

-- one frame against one symbolic frame, at the assignments satisfying `G`; a frame that is
-- there on one side is there on the other
data Rel (G : (ℕ → ℕ) → Set) : Maybe (Dia ℕ) → Maybe (Dia (Expr ℕ)) → Set where
  noFrame : Rel G nothing nothing
  bothFrames : ∀ {x y} → (∀ ρ → G ρ → layoutℕ x ≡ mapLayout (eval ρ) (layoutE y)) → Rel G (just x) (just y)

Rel-⇒ : ∀ {G G′ : (ℕ → ℕ) → Set} → (∀ ρ → G ρ → G′ ρ) → ∀ {a b} → Rel G′ a b → Rel G a b
Rel-⇒ f noFrame     = noFrame
Rel-⇒ f (bothFrames r) = bothFrames (λ ρ g → r ρ (f ρ g))

-- the frames of `xs` (from tick `t` on) are the symbolic frames `ys` evaluated at the
-- assignments in `G k`; `G` says which assignments are meant at the absolute tick `k`
record Agree (G : ℕ → (ℕ → ℕ) → Set) (t : ℕ) (xs : List (Dia ℕ)) (ys : List (Dia (Expr ℕ))) : Set where
  constructor agree
  field at : ∀ j → Rel (G (t + j)) (nth xs j) (nth ys j)
open Agree

Agree-≡ : ∀ {G t t′ xs ys} → t ≡ t′ → Agree G t xs ys → Agree G t′ xs ys
Agree-≡ refl a = a

-- `atop` of the frames is `atop` of the symbolic frames: layout is natural along evaluation
Rel-mergeM : ∀ {G₁ G₂ : (ℕ → ℕ) → Set} {a b a′ b′} → Rel G₁ a a′ → Rel G₂ b b′ →
             Rel (λ ρ → G₁ ρ × G₂ ρ) (mergeM atop a b) (mergeM atop a′ b′)
Rel-mergeM noFrame         rb         = Rel-⇒ (λ ρ → proj₂) rb
Rel-mergeM (bothFrames ra)    noFrame       = Rel-⇒ (λ ρ → proj₁) (bothFrames ra)
Rel-mergeM (bothFrames {x} {x′} ra) (bothFrames {y} {y′} rb) = bothFrames λ ρ (g₁ , g₂) →
  trans (cong₂ PN.atop (ra ρ g₁) (rb ρ g₂))
        (sym (atop-natural exprOps natOps (eval ρ) (eval-hom ρ) (layoutE x′) (layoutE y′)))

-- `merge` of lists is `atop` frame by frame
Agree-merge : ∀ {G₁ G₂ t xs xs′ ys ys′} → Agree G₁ t xs xs′ → Agree G₂ t ys ys′ →
              Agree (λ k ρ → G₁ k ρ × G₂ k ρ) t (merge atop xs ys) (merge atop xs′ ys′)
Agree-merge {G₁} {G₂} {t} {xs} {xs′} {ys} {ys′} a₁ a₂ = agree go
  where
    go : ∀ j → Rel (λ ρ → G₁ (t + j) ρ × G₂ (t + j) ρ) (nth (merge atop xs ys) j) (nth (merge atop xs′ ys′) j)
    go j rewrite nth-merge atop xs ys j | nth-merge atop xs′ ys′ j = Rel-mergeM (at a₁ j) (at a₂ j)

-- lists in agreement are as long as each other
private
  len≤ : ∀ {A B : Set} (xs : List A) (ys : List B) →
         (∀ j → nth ys j ≡ nothing → nth xs j ≡ nothing) → length xs ≤ length ys
  len≤ []       ys       h = ℕ.z≤n
  len≤ (x ∷ xs) []       h with h 0 refl
  ... | ()
  len≤ (x ∷ xs) (y ∷ ys) h = ℕ.s≤s (len≤ xs ys (λ j → h (suc j)))

  Rel-nothingˡ : ∀ {G a b} → Rel G a b → a ≡ nothing → b ≡ nothing
  Rel-nothingˡ noFrame     refl = refl
  Rel-nothingˡ (bothFrames _) ()

  Rel-nothingʳ : ∀ {G a b} → Rel G a b → b ≡ nothing → a ≡ nothing
  Rel-nothingʳ noFrame     refl = refl
  Rel-nothingʳ (bothFrames _) ()

Agree-length : ∀ {G t xs ys} → Agree G t xs ys → length xs ≡ length ys
Agree-length {G} {t} {xs} {ys} ag =
  ℕP.≤-antisym (len≤ xs ys (λ j e → Rel-nothingʳ (at ag j) e))
               (len≤ ys xs (λ j e → Rel-nothingˡ (at ag j) e))

-- `++` of lists is `++`, with the tick of the second part shifted by the length of the first
private
  nth-++′ : ∀ {A : Set} (xs ys : List A) j n → length xs ≡ n →
            nth (xs ++ ys) j ≡ (if j <ᵇ n then nth xs j else nth ys (j ∸ n))
  nth-++′ xs ys j n refl = nth-++ xs ys j

  lt-false : ∀ {m n} → (m <ᵇ n) ≡ false → n ≤ m
  lt-false {m} {n} e = ℕP.≮⇒≥ (λ h → subst Data.Bool.T e (ℕP.<⇒<ᵇ h))

Agree-++ : ∀ {G₁ G₂ t xs xs′ ys ys′} → Agree G₁ t xs xs′ → Agree G₂ (t + length xs) ys ys′ →
           Agree (λ k ρ → G₁ k ρ × G₂ k ρ) t (xs ++ ys) (xs′ ++ ys′)
Agree-++ {G₁} {G₂} {t} {xs} {xs′} {ys} {ys′} a₁ a₂ = agree λ j →
  go j (length xs) refl (sym (Agree-length a₁))
  where
    go : ∀ j n → length xs ≡ n → length xs′ ≡ n →
         Rel (λ ρ → G₁ (t + j) ρ × G₂ (t + j) ρ) (nth (xs ++ ys) j) (nth (xs′ ++ ys′) j)
    go j n e e′ rewrite nth-++′ xs ys j n e | nth-++′ xs′ ys′ j n e′ with j <ᵇ n in eq
    ... | true  = Rel-⇒ (λ ρ → proj₁) (at a₁ j)
    ... | false = Rel-⇒ (λ ρ → proj₂)
                    (subst (λ k → Rel (G₂ k) (nth ys (j ∸ n)) (nth ys′ (j ∸ n)))
                           (trans (ℕP.+-assoc t n (j ∸ n)) (cong (t +_) (ℕP.m+[n∸m]≡n {n} {j} (lt-false eq))))
                           (subst (λ m → Rel (G₂ (t + m + (j ∸ n))) (nth ys (j ∸ n)) (nth ys′ (j ∸ n))) e (at a₂ (j ∸ n))))

------------------------------------------------------------------------
-- One segment

-- `ρ` gives the leaf's variable the parameter its track has at the tick `m` that falls on `k`
LeafGood : Leaf → ℕ → (ℕ → ℕ) → Set
LeafGood l k ρ = ∀ m → (m <ᵇ T.dur (Leaf.track l)) ≡ true → Leaf.start l + m ≡ k →
                 ρ (Leaf.idx l) ≡ units (proj₂ (T.sample T.ℚLerp (Leaf.track l)) m)

-- the leaves of a tree, each with its own condition: the assignments for the tick `k` that
-- agree with the parameter of every leaf running at `k` (and say nothing of the others)
GoodL : AnimC ⋆ Leaf → ℕ → (ℕ → ℕ) → Set
GoodL (pure l)              k ρ = LeafGood l k ρ
GoodL (impure (Seq , c))    k ρ = GoodL (c zero) k ρ × GoodL (c (suc zero)) k ρ
GoodL (impure (Par , c))    k ρ = GoodL (c zero) k ρ × GoodL (c (suc zero)) k ρ

leaf-Agree : ∀ tr d i t₀ →
  Agree (LeafGood (leaf i t₀ tr d)) t₀ (frames natOps (seg tr (template d)))
        (replicate (T.dur tr) (instantiate (leaf i t₀ tr d)))
leaf-Agree tr d i t₀ = agree go
  where
  l = leaf i t₀ tr d
  go : ∀ j → Rel (LeafGood l (t₀ + j)) (nth (frames natOps (seg tr (template d))) j)
                                       (nth (replicate (T.dur tr) (instantiate l)) j)
  go j rewrite nth-frames natOps (seg tr (template d)) j
             | nth-replicate (T.dur tr) (instantiate l) j
             | T.sample-dur T.ℚLerp tr
    with j <ᵇ T.dur tr in eq
  ... | false = noFrame
  ... | true  = bothFrames λ ρ g →
    let q = proj₂ (T.sample T.ℚLerp tr) j
        idx≡ : units q ≡ ρ i
        idx≡ = sym (g j eq refl)
    in trans (cong (λ r → layoutℕ (mapDia (eval (λ _ → r)) d)) idx≡)
      (trans (sym (leaf-agrees l ρ))
             (sym (layout-eval ρ (instantiate l))))

------------------------------------------------------------------------
-- Inverting `leaves`

private
  bind-just : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {y} → (m Maybe.>>= f) ≡ just y →
              ∃ λ x → m ≡ just x × f x ≡ just y
  bind-just (just x) f eq = x , refl , eq
  bind-just nothing  f ()

-- The whole animation: the frames agree with the symbolic frames at every tick.
leaves-agree : ∀ (a : Anim ℕ (Seg ℕ)) i t₀ i′ l → leaves i t₀ a ≡ just (i′ , l) →
               Agree (GoodL l) t₀ (timeline atop (frames natOps) a) (symbolicFrames l)
leaves-agree (pure (seg tr (template d))) i t₀ _ _ refl = leaf-Agree tr d i t₀
leaves-agree (pure (seg tr (blackBox f))) i t₀ _ _ ()
leaves-agree (impure (Seq , k)) i t₀ i′ l eq with bind-just (leaves i t₀ (k zero)) _ eq
... | (i₁ , a′) , e₁ , r₁ with bind-just (leaves i₁ _ (k (suc zero))) _ r₁
... | (i₂ , b′) , e₂ , refl =
  Agree-++ (leaves-agree (k zero) i t₀ i₁ a′ e₁)
           (Agree-≡ (cong (t₀ +_) (sym (length-dur natOps (k zero))))
                    (leaves-agree (k (suc zero)) i₁ (t₀ + dur (k zero)) i₂ b′ e₂))
leaves-agree (impure (Par , k)) i t₀ i′ l eq with bind-just (leaves i t₀ (k zero)) _ eq
... | (i₁ , a′) , e₁ , r₁ with bind-just (leaves i₁ _ (k (suc zero))) _ r₁
... | (i₂ , b′) , e₂ , refl =
  Agree-merge (leaves-agree (k zero) i t₀ i₁ a′ e₁) (leaves-agree (k (suc zero)) i₁ t₀ i₂ b′ e₂)
