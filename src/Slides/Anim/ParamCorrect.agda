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

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map; applyUpTo; concat)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_; _≤_)
import Data.Nat.Properties as ℕP
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
import Data.List.Properties as LP
open import Data.Unit using (⊤; tt)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary using (yes; no)
open import Data.Fin using (zero; suc)
open import Data.Container.FreeMonad using (_⋆_; pure; impure)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)

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
import Slides.Diagram.Param as DP

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
nth-++′ : ∀ {A : Set} (xs ys : List A) j n → length xs ≡ n →
          nth (xs ++ ys) j ≡ (if j <ᵇ n then nth xs j else nth ys (j ∸ n))
nth-++′ xs ys j n refl = nth-++ xs ys j

private
  lt-false : ∀ {m n} → (m <ᵇ n) ≡ false → n ≤ m
  lt-false {m} {n} e = ℕP.≮⇒≥ (λ h → subst T e (ℕP.<⇒<ᵇ h))

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

------------------------------------------------------------------------
-- Tick by tick

nth-in : ∀ {A : Set} (xs : List A) j → (j <ᵇ length xs) ≡ true → ∃ λ x → nth xs j ≡ just x
nth-in []       j       ()
nth-in (x ∷ xs) zero    h = x , refl
nth-in (x ∷ xs) (suc j) h = nth-in xs j h

private
  Rel-just : ∀ {G F m} → Rel G (just F) m →
             ∃ λ S → m ≡ just S × (∀ ρ → G ρ → layoutℕ F ≡ mapLayout (eval ρ) (layoutE S))
  Rel-just (bothFrames {y = y} r) = y , refl , r

-- Statement (A).  For an animation of templates (`leaves 0 0 a ≡ just (i′ , l)`), at every tick
-- `k < dur a` the frame of `timeline atop (frames natOps) a` is the layout of the symbolic
-- frame evaluated at any assignment `ρ` that gives each leaf running at `k` the (floored)
-- parameter of its track at that tick (`GoodL l k ρ`).
discrete-assembly :
  ∀ (a : Anim ℕ (Seg ℕ)) i′ l → leaves 0 0 a ≡ just (i′ , l) → ∀ k → (k <ᵇ dur a) ≡ true →
  ∀ ρ → GoodL l k ρ →
  ∃₂ λ F S → nth (timeline atop (frames natOps) a) k ≡ just F
           × nth (symbolicFrames l) k ≡ just S
           × layoutℕ F ≡ mapLayout (eval ρ) (layoutE S)
discrete-assembly a i′ l eq k hk ρ g with nth-in (timeline atop (frames natOps) a) k
                                            (subst (λ n → (k <ᵇ n) ≡ true) (sym (length-dur natOps a)) hk)
... | F , eF with Rel-just (subst (λ m → Rel (GoodL l k) m (nth (symbolicFrames l) k)) eF (at (leaves-agree a 0 0 i′ l eq) k))
... | S , eS , r = F , S , eF , eS , r ρ g

------------------------------------------------------------------------
-- The assignment `i ↦ (parameter of segment i at tick k)`
--
-- `GoodL` says what an assignment must do; this is one that does it.  The leaves of `leaves`
-- are numbered apart (`numbered`: the variables of a tree lie in `[i, i′)`, a `Seq` or `Par`
-- splitting the range at `i₁`), and `assignAt` gives variable `j` the floored parameter of the
-- leaf numbered `j` at tick `k` if that leaf is running, and 0 otherwise.

numbered : ℕ → ℕ → AnimC ⋆ Leaf → Set
numbered i i′ (pure l)           = Leaf.idx l ≡ i × i′ ≡ suc i
numbered i i′ (impure (Seq , c)) = ∃ λ i₁ → numbered i i₁ (c zero) × numbered i₁ i′ (c (suc zero))
numbered i i′ (impure (Par , c)) = ∃ λ i₁ → numbered i i₁ (c zero) × numbered i₁ i′ (c (suc zero))

leaves-numbered : ∀ (a : Anim ℕ (Seg ℕ)) i t₀ i′ l → leaves i t₀ a ≡ just (i′ , l) → numbered i i′ l
leaves-numbered (pure (seg tr (template d))) i t₀ _ _ refl = refl , refl
leaves-numbered (pure (seg tr (blackBox f))) i t₀ _ _ ()
leaves-numbered (impure (Seq , k)) i t₀ i′ l eq with bind-just (leaves i t₀ (k zero)) _ eq
... | (i₁ , a′) , e₁ , r₁ with bind-just (leaves i₁ _ (k (suc zero))) _ r₁
... | (i₂ , b′) , e₂ , refl = i₁ , leaves-numbered (k zero) i t₀ i₁ a′ e₁ , leaves-numbered (k (suc zero)) i₁ _ i₂ b′ e₂
leaves-numbered (impure (Par , k)) i t₀ i′ l eq with bind-just (leaves i t₀ (k zero)) _ eq
... | (i₁ , a′) , e₁ , r₁ with bind-just (leaves i₁ _ (k (suc zero))) _ r₁
... | (i₂ , b′) , e₂ , refl = i₁ , leaves-numbered (k zero) i t₀ i₁ a′ e₁ , leaves-numbered (k (suc zero)) i₁ t₀ i₂ b′ e₂

numbered-≤ : ∀ t i i′ → numbered i i′ t → i ≤ i′
numbered-≤ (pure l)           i i′ (refl , refl) = ℕP.n≤1+n i
numbered-≤ (impure (Seq , c)) i i′ (i₁ , n₁ , n₂) = ℕP.≤-trans (numbered-≤ (c zero) i i₁ n₁) (numbered-≤ (c (suc zero)) i₁ i′ n₂)
numbered-≤ (impure (Par , c)) i i′ (i₁ , n₁ , n₂) = ℕP.≤-trans (numbered-≤ (c zero) i i₁ n₁) (numbered-≤ (c (suc zero)) i₁ i′ n₂)

-- the parameter of a leaf at tick `k` if it is running there
activeVal : Leaf → ℕ → ℕ
activeVal l k =
  if (Leaf.start l ℕ.≤ᵇ k) ∧ (k <ᵇ Leaf.start l + T.dur (Leaf.track l))
  then units (proj₂ (T.sample T.ℚLerp (Leaf.track l)) (k ∸ Leaf.start l)) else 0

assignAt : AnimC ⋆ Leaf → ℕ → ℕ → ℕ
assignAt (pure l)           k j = if ⌊ j ℕP.≟ Leaf.idx l ⌋ then activeVal l k else 0
assignAt (impure (Seq , c)) k j = assignAt (c zero) k j + assignAt (c (suc zero)) k j
assignAt (impure (Par , c)) k j = assignAt (c zero) k j + assignAt (c (suc zero)) k j

private
  T⇒≡ : ∀ {b} → T b → b ≡ true
  T⇒≡ {true} _ = refl

  <ᵇ-true : ∀ {m n} → m ℕ.< n → (m <ᵇ n) ≡ true
  <ᵇ-true h = T⇒≡ (ℕP.<⇒<ᵇ h)

  ≤ᵇ-true : ∀ {m n} → m ≤ n → (m ℕ.≤ᵇ n) ≡ true
  ≤ᵇ-true h = T⇒≡ (ℕP.≤⇒≤ᵇ h)

  <ᵇ-lt : ∀ {m n} → (m <ᵇ n) ≡ true → m ℕ.< n
  <ᵇ-lt {m} {n} h = ℕP.<ᵇ⇒< m n (subst T (sym h) tt)

  true≢false : true ≡ false → ⊥
  true≢false ()

  <ᵇ-irrefl : ∀ i → (i <ᵇ i) ≡ false
  <ᵇ-irrefl zero    = refl
  <ᵇ-irrefl (suc i) = <ᵇ-irrefl i

  ⌊≟⌋-diag : ∀ i → ⌊ i ℕP.≟ i ⌋ ≡ true
  ⌊≟⌋-diag i rewrite ℕP.≟-diag {i} {i} refl = refl

activeVal-on : ∀ l m → (m <ᵇ T.dur (Leaf.track l)) ≡ true →
               activeVal l (Leaf.start l + m) ≡ units (proj₂ (T.sample T.ℚLerp (Leaf.track l)) m)
activeVal-on l m h =
  trans (cong (λ b → if b then units (proj₂ (T.sample T.ℚLerp (Leaf.track l)) (Leaf.start l + m ∸ Leaf.start l)) else 0)
              (cong₂ _∧_ (≤ᵇ-true (ℕP.m≤m+n (Leaf.start l) m))
                         (<ᵇ-true (ℕP.+-monoʳ-< (Leaf.start l) (<ᵇ-lt h)))))
        (cong (λ x → units (proj₂ (T.sample T.ℚLerp (Leaf.track l)) x)) (ℕP.m+n∸m≡n (Leaf.start l) m))

assignAt-out : ∀ t i i′ → numbered i i′ t → ∀ k j → ((j <ᵇ i) ≡ true) ⊎ (i′ ≤ j) → assignAt t k j ≡ 0
assignAt-out (pure l) i i′ (refl , refl) k j out with j ℕP.≟ Leaf.idx l
... | no  _    = refl
... | yes refl with out
...   | inj₁ h = ⊥-elim (true≢false (trans (sym h) (<ᵇ-irrefl (Leaf.idx l))))
...   | inj₂ h = ⊥-elim (ℕP.1+n≰n h)
assignAt-out (impure (Seq , c)) i i′ (i₁ , n₁ , n₂) k j out =
  cong₂ _+_ (assignAt-out (c zero) i i₁ n₁ k j (outˡ n₂ out))
            (assignAt-out (c (suc zero)) i₁ i′ n₂ k j (outʳ n₁ out))
  where
    outˡ : numbered i₁ i′ (c (suc zero)) → _ → _
    outˡ n₂ (inj₁ h) = inj₁ h
    outˡ n₂ (inj₂ h) = inj₂ (ℕP.≤-trans (numbered-≤ _ i₁ i′ n₂) h)
    outʳ : numbered i i₁ (c zero) → _ → _
    outʳ n₁ (inj₁ h) = inj₁ (<ᵇ-true (ℕP.<-≤-trans (<ᵇ-lt h) (numbered-≤ _ i i₁ n₁)))
    outʳ n₁ (inj₂ h) = inj₂ h
assignAt-out (impure (Par , c)) i i′ (i₁ , n₁ , n₂) k j out =
  cong₂ _+_ (assignAt-out (c zero) i i₁ n₁ k j (outˡ n₂ out))
            (assignAt-out (c (suc zero)) i₁ i′ n₂ k j (outʳ n₁ out))
  where
    outˡ : numbered i₁ i′ (c (suc zero)) → _ → _
    outˡ n₂ (inj₁ h) = inj₁ h
    outˡ n₂ (inj₂ h) = inj₂ (ℕP.≤-trans (numbered-≤ _ i₁ i′ n₂) h)
    outʳ : numbered i i₁ (c zero) → _ → _
    outʳ n₁ (inj₁ h) = inj₁ (<ᵇ-true (ℕP.<-≤-trans (<ᵇ-lt h) (numbered-≤ _ i i₁ n₁)))
    outʳ n₁ (inj₂ h) = inj₂ h

-- `assignAt` is good, and so is anything that agrees with it on the variables of the tree
canonical-good : ∀ t i i′ → numbered i i′ t → ∀ k ρ →
                 (∀ j → i ≤ j → j ℕ.< i′ → ρ j ≡ assignAt t k j) → GoodL t k ρ
canonical-good (pure l) i i′ (refl , refl) k ρ h m hm refl =
  trans (h (Leaf.idx l) ℕP.≤-refl (ℕP.n<1+n (Leaf.idx l)))
        (trans (cong (λ b → if b then activeVal l (Leaf.start l + m) else 0) (⌊≟⌋-diag (Leaf.idx l)))
               (activeVal-on l m hm))
canonical-good (impure (Seq , c)) i i′ (i₁ , n₁ , n₂) k ρ h =
  canonical-good (c zero) i i₁ n₁ k ρ
    (λ j lo hi → trans (h j lo (ℕP.<-≤-trans hi (numbered-≤ _ i₁ i′ n₂)))
                       (trans (cong (assignAt (c zero) k j +_) (assignAt-out _ i₁ i′ n₂ k j (inj₁ (<ᵇ-true hi))))
                              (ℕP.+-identityʳ _)))
  , canonical-good (c (suc zero)) i₁ i′ n₂ k ρ
    (λ j lo hi → trans (h j (ℕP.≤-trans (numbered-≤ _ i i₁ n₁) lo) hi)
                       (cong (_+ assignAt (c (suc zero)) k j) (assignAt-out _ i i₁ n₁ k j (inj₂ lo))))
canonical-good (impure (Par , c)) i i′ (i₁ , n₁ , n₂) k ρ h =
  canonical-good (c zero) i i₁ n₁ k ρ
    (λ j lo hi → trans (h j lo (ℕP.<-≤-trans hi (numbered-≤ _ i₁ i′ n₂)))
                       (trans (cong (assignAt (c zero) k j +_) (assignAt-out _ i₁ i′ n₂ k j (inj₁ (<ᵇ-true hi))))
                              (ℕP.+-identityʳ _)))
  , canonical-good (c (suc zero)) i₁ i′ n₂ k ρ
    (λ j lo hi → trans (h j (ℕP.≤-trans (numbered-≤ _ i i₁ n₁) lo) hi)
                       (cong (_+ assignAt (c (suc zero)) k j) (assignAt-out _ i i₁ n₁ k j (inj₂ lo))))

-- Statement (A), with the assignment named: variable `j` is the floored parameter, at tick `k`, of
-- the segment numbered `j` (0 when it is not running).  No hypothesis beyond `a` being made of
-- templates.
discrete-assembly-canonical :
  ∀ (a : Anim ℕ (Seg ℕ)) i′ l → leaves 0 0 a ≡ just (i′ , l) → ∀ k → (k <ᵇ dur a) ≡ true →
  ∃₂ λ F S → nth (timeline atop (frames natOps) a) k ≡ just F
           × nth (symbolicFrames l) k ≡ just S
           × layoutℕ F ≡ mapLayout (eval (assignAt l k)) (layoutE S)
discrete-assembly-canonical a i′ l eq k hk =
  discrete-assembly a i′ l eq k hk (assignAt l k)
    (canonical-good l 0 i′ (leaves-numbered a 0 0 i′ l eq) k (assignAt l k) (λ j _ _ → refl))

------------------------------------------------------------------------
-- The shipped segments are the leaves, in order of their variable

-- `lf` is a leaf of the tree
InTree : Leaf → AnimC ⋆ Leaf → Set
InTree lf (pure l)           = lf ≡ l
InTree lf (impure (Seq , c)) = InTree lf (c zero) ⊎ InTree lf (c (suc zero))
InTree lf (impure (Par , c)) = InTree lf (c zero) ⊎ InTree lf (c (suc zero))

InTree-range : ∀ t i i′ lf → numbered i i′ t → InTree lf t → i ≤ Leaf.idx lf × Leaf.idx lf ℕ.< i′
InTree-range (pure l) i i′ lf (refl , refl) refl = ℕP.≤-refl , ℕP.n<1+n _
InTree-range (impure (Seq , c)) i i′ lf (i₁ , n₁ , n₂) (inj₁ h) with InTree-range (c zero) i i₁ lf n₁ h
... | lo , hi = lo , ℕP.<-≤-trans hi (numbered-≤ _ i₁ i′ n₂)
InTree-range (impure (Seq , c)) i i′ lf (i₁ , n₁ , n₂) (inj₂ h) with InTree-range (c (suc zero)) i₁ i′ lf n₂ h
... | lo , hi = ℕP.≤-trans (numbered-≤ _ i i₁ n₁) lo , hi
InTree-range (impure (Par , c)) i i′ lf (i₁ , n₁ , n₂) (inj₁ h) with InTree-range (c zero) i i₁ lf n₁ h
... | lo , hi = lo , ℕP.<-≤-trans hi (numbered-≤ _ i₁ i′ n₂)
InTree-range (impure (Par , c)) i i′ lf (i₁ , n₁ , n₂) (inj₂ h) with InTree-range (c (suc zero)) i₁ i′ lf n₂ h
... | lo , hi = ℕP.≤-trans (numbered-≤ _ i i₁ n₁) lo , hi

length-segmentsOf : ∀ t i i′ → numbered i i′ t → i + length (segmentsOf t) ≡ i′
length-segmentsOf (pure l) i i′ (refl , refl) = ℕP.+-comm i 1
length-segmentsOf (impure (Seq , c)) i i′ (i₁ , n₁ , n₂) =
  trans (cong (i +_) (LP.length-++ (segmentsOf (c zero))))
  (trans (sym (ℕP.+-assoc i (length (segmentsOf (c zero))) (length (segmentsOf (c (suc zero))))))
  (trans (cong (_+ length (segmentsOf (c (suc zero)))) (length-segmentsOf (c zero) i i₁ n₁))
         (length-segmentsOf (c (suc zero)) i₁ i′ n₂)))
length-segmentsOf (impure (Par , c)) i i′ (i₁ , n₁ , n₂) =
  trans (cong (i +_) (LP.length-++ (segmentsOf (c zero))))
  (trans (sym (ℕP.+-assoc i (length (segmentsOf (c zero))) (length (segmentsOf (c (suc zero))))))
  (trans (cong (_+ length (segmentsOf (c (suc zero)))) (length-segmentsOf (c zero) i i₁ n₁))
         (length-segmentsOf (c (suc zero)) i₁ i′ n₂)))

private
  lt-or-ge : ∀ x y → x ℕ.< y ⊎ y ≤ x
  lt-or-ge x y with ℕP.<-cmp x y
  ... | tri< a _ _ = inj₁ a
  ... | tri≈ _ b _ = inj₂ (ℕP.≤-reflexive (sym b))
  ... | tri> _ _ c = inj₂ (ℕP.<⇒≤ c)

  <ᵇ-false : ∀ {m n} → n ≤ m → (m <ᵇ n) ≡ false
  <ᵇ-false {m} {zero}  ℕ.z≤n       = refl
  <ᵇ-false {suc m} {suc n} (ℕ.s≤s h) = <ᵇ-false h

  -- reading the `d`-th element of `xs ++ ys` when `xs` and `ys` cover consecutive ranges of
  -- positions `[i, i₁)`, `[i₁, …)`
  nth-join : ∀ {A : Set} (xs ys : List A) i i₁ x (r : A) d → i + length xs ≡ i₁ → i + d ≡ x →
             (x ℕ.< i₁ → nth xs d ≡ just r) →
             (i₁ ≤ x → ∀ d′ → i₁ + d′ ≡ x → nth ys d′ ≡ just r) →
             nth (xs ++ ys) d ≡ just r
  nth-join xs ys i i₁ x r d len e h₁ h₂ with lt-or-ge x i₁
  ... | inj₁ lt = trans (trans (nth-++ xs ys d) (cong (λ b → if b then nth xs d else nth ys (d ∸ length xs)) d<))
                        (h₁ lt)
    where d< = <ᵇ-true (ℕP.+-cancelˡ-< i d (length xs) (subst₂ ℕ._<_ (sym e) (sym len) lt))
  ... | inj₂ ge = trans (trans (nth-++ xs ys d) (cong (λ b → if b then nth xs d else nth ys (d ∸ length xs)) d≮))
                        (h₂ ge (d ∸ length xs) off)
    where d≥ : length xs ≤ d
          d≥ = ℕP.+-cancelˡ-≤ i _ d (subst₂ ℕ._≤_ (sym len) (sym e) ge)
          d≮ = <ᵇ-false d≥
          off = trans (cong (_+ (d ∸ length xs)) (sym len))
                 (trans (ℕP.+-assoc i (length xs) (d ∸ length xs))
                 (trans (cong (i +_) (ℕP.m+[n∸m]≡n d≥)) e))

-- the `d`-th shipped segment, counting from the first variable `i`, is the leaf numbered `i + d`
segmentsOf-nth : ∀ t i i′ lf → numbered i i′ t → InTree lf t → ∀ d → i + d ≡ Leaf.idx lf →
                 nth (segmentsOf t) d ≡ just (Leaf.start lf , pieces (Leaf.track lf))
segmentsOf-nth (pure l) i i′ lf (refl , refl) refl d h
  with ℕP.+-cancelˡ-≡ (Leaf.idx l) d 0 (trans h (sym (ℕP.+-identityʳ _)))
... | refl = refl
segmentsOf-nth (impure (Seq , c)) i i′ lf (i₁ , n₁ , n₂) (inj₁ h) d e =
  nth-join (segmentsOf (c zero)) (segmentsOf (c (suc zero))) i i₁ (Leaf.idx lf) _ d
    (length-segmentsOf (c zero) i i₁ n₁) e
    (λ _ → segmentsOf-nth (c zero) i i₁ lf n₁ h d e)
    (λ ge → ⊥-elim (ℕP.<⇒≱ (proj₂ (InTree-range (c zero) i i₁ lf n₁ h)) ge))
segmentsOf-nth (impure (Seq , c)) i i′ lf (i₁ , n₁ , n₂) (inj₂ h) d e =
  nth-join (segmentsOf (c zero)) (segmentsOf (c (suc zero))) i i₁ (Leaf.idx lf) _ d
    (length-segmentsOf (c zero) i i₁ n₁) e
    (λ lt → ⊥-elim (ℕP.<⇒≱ lt (proj₁ (InTree-range (c (suc zero)) i₁ i′ lf n₂ h))))
    (λ _ d′ e′ → segmentsOf-nth (c (suc zero)) i₁ i′ lf n₂ h d′ e′)
segmentsOf-nth (impure (Par , c)) i i′ lf (i₁ , n₁ , n₂) (inj₁ h) d e =
  nth-join (segmentsOf (c zero)) (segmentsOf (c (suc zero))) i i₁ (Leaf.idx lf) _ d
    (length-segmentsOf (c zero) i i₁ n₁) e
    (λ _ → segmentsOf-nth (c zero) i i₁ lf n₁ h d e)
    (λ ge → ⊥-elim (ℕP.<⇒≱ (proj₂ (InTree-range (c zero) i i₁ lf n₁ h)) ge))
segmentsOf-nth (impure (Par , c)) i i′ lf (i₁ , n₁ , n₂) (inj₂ h) d e =
  nth-join (segmentsOf (c zero)) (segmentsOf (c (suc zero))) i i₁ (Leaf.idx lf) _ d
    (length-segmentsOf (c zero) i i₁ n₁) e
    (λ lt → ⊥-elim (ℕP.<⇒≱ lt (proj₁ (InTree-range (c (suc zero)) i₁ i′ lf n₂ h))))
    (λ _ d′ e′ → segmentsOf-nth (c (suc zero)) i₁ i′ lf n₂ h d′ e′)

------------------------------------------------------------------------
-- What `render` ships

private
  map-just : ∀ {A B : Set} (f : A → B) (m : Maybe A) {y} → Maybe.map f m ≡ just y →
             ∃ λ x → m ≡ just x × f x ≡ y
  map-just f (just x) refl = x , refl , refl
  map-just f nothing  ()

-- the acts, one after the other, play their frames one after the other
seqAll-timeline : ∀ acts {a} → seqAll acts ≡ just a →
                  timeline atop (frames natOps) a ≡ concat (map (timeline atop (frames natOps)) acts)
seqAll-timeline []             ()
seqAll-timeline (a ∷ [])       refl = sym (LP.++-identityʳ (timeline atop (frames natOps) a))
seqAll-timeline (a ∷ b ∷ as)   eq =
  let r = map-just (a ⨾_) (seqAll (b ∷ as)) eq in
  trans (cong (timeline atop (frames natOps)) (sym (proj₂ (proj₂ r))))
        (cong (timeline atop (frames natOps) a ++_) (seqAll-timeline (b ∷ as) (proj₁ (proj₂ r))))

-- what `paramOf` is made of
paramOf-inv : ∀ acts {p} → paramOf acts ≡ just p →
              ∃₂ λ a l → seqAll acts ≡ just a × (∃ λ i′ → leaves 0 0 a ≡ just (i′ , l)) × mkParam l ≡ p
paramOf-inv acts eq with bind-just (seqAll acts) _ eq
... | a , e₁ , r₁ with bind-just (leaves 0 0 a) _ r₁
... | (i′ , l) , e₂ , r₂ = a , l , e₁ , (i′ , e₂) , ne (mkParam l) r₂
  where
    ne : ∀ q {p} → nonEmptyParam q ≡ just p → q ≡ p
    ne q eq with DP.Param.ticks q
    ne q refl | _ ∷ _ = refl

private
  shipped : ∀ acts a l i′ → seqAll acts ≡ just a → leaves 0 0 a ≡ just (i′ , l) →
            ∀ k → (k <ᵇ length (concat (map (timeline atop (frames natOps)) acts))) ≡ true →
            ∀ ρ → GoodL l k ρ →
            ∃₂ λ F L → nth (concat (map (timeline atop (frames natOps)) acts)) k ≡ just F
                     × nth (DP.Param.ticks (mkParam l)) k ≡ just L
                     × layoutℕ F ≡ mapLayout (eval ρ) L
  shipped acts a l i′ ea el k hk ρ g =
    let hk′ = subst (λ xs → (k <ᵇ length xs) ≡ true) (sym (seqAll-timeline acts ea)) hk
        hk″ = subst (λ n → (k <ᵇ n) ≡ true) (length-dur natOps a) hk′
    in go (seqAll-timeline acts ea) (discrete-assembly a i′ l el k hk″ ρ g)
    where
      go : timeline atop (frames natOps) a ≡ concat (map (timeline atop (frames natOps)) acts) →
           (∃₂ λ F S → nth (timeline atop (frames natOps) a) k ≡ just F
                     × nth (symbolicFrames l) k ≡ just S
                     × layoutℕ F ≡ mapLayout (eval ρ) (layoutE S)) → _
      go e (F , S , eF , eS , r) = F , layoutE S , subst (λ xs → nth xs k ≡ just F) e eF
                                  , trans (nth-map layoutE (symbolicFrames l) k) (cong (Maybe.map layoutE) eS) , r

-- Statement (A) for what `render` ships.  If `paramOf acts ≡ just p`, there are leaves `l`
-- (the numbered segments, with their tracks) whose `segmentsOf` are the shipped `segments`, and
-- for every tick `k` of the frames `render` shows (`concat (map (timeline atop (frames natOps))
-- acts)`) and every assignment `ρ` that is right for the leaves running at `k`, the shipped
-- layout of tick `k`, evaluated at `ρ`, is the layout of the shown frame.
paramOf-assembly :
  ∀ acts {p} → paramOf acts ≡ just p →
  ∃ λ l → DP.Param.segments p ≡ segmentsOf l
        × ∀ k → (k <ᵇ length (concat (map (timeline atop (frames natOps)) acts))) ≡ true →
          ∀ ρ → GoodL l k ρ →
          ∃₂ λ F L → nth (concat (map (timeline atop (frames natOps)) acts)) k ≡ just F
                   × nth (DP.Param.ticks p) k ≡ just L
                   × layoutℕ F ≡ mapLayout (eval ρ) L
paramOf-assembly acts eq with paramOf-inv acts eq
... | a , l , ea , (i′ , el) , refl = l , refl , shipped acts a l i′ ea el

-- The same with the assignment named, and the shipped segments identified: variable `j` is the
-- `j`-th entry of `segments` (the leaf `lf` with `idx lf ≡ j`: `(start lf , pieces (track lf))`),
-- and its value at tick `k` is the floored parameter of that segment's track there.
paramOf-assembly-canonical :
  ∀ acts {p} → paramOf acts ≡ just p →
  ∃ λ l → DP.Param.segments p ≡ segmentsOf l
        × (∀ lf → InTree lf l → nth (DP.Param.segments p) (Leaf.idx lf) ≡ just (Leaf.start lf , pieces (Leaf.track lf)))
        × ∀ k → (k <ᵇ length (concat (map (timeline atop (frames natOps)) acts))) ≡ true →
          ∃₂ λ F L → nth (concat (map (timeline atop (frames natOps)) acts)) k ≡ just F
                   × nth (DP.Param.ticks p) k ≡ just L
                   × layoutℕ F ≡ mapLayout (eval (assignAt l k)) L
paramOf-assembly-canonical acts eq with paramOf-inv acts eq
... | a , l , ea , (i′ , el) , refl = l , refl , segs , λ k hk →
  shipped acts a l i′ ea el k hk (assignAt l k) (canonical-good l 0 i′ (leaves-numbered a 0 0 i′ l el) k (assignAt l k) (λ j _ _ → refl))
  where
    segs : ∀ lf → InTree lf l → nth (segmentsOf l) (Leaf.idx lf) ≡ just (Leaf.start lf , pieces (Leaf.track lf))
    segs lf h = segmentsOf-nth l 0 i′ lf (leaves-numbered a 0 0 i′ l el) h (Leaf.idx lf) refl
