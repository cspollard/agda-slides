{-# OPTIONS --safe --without-K #-}

-- Laws of scenes.
--
--   nesting      a substitution of scenes for leaves is bind, and both meanings respect it:
--                `events-bind`, `sample-bind`, `reading-bind`; `nest-window`: a scene put in a
--                windowed, delayed leaf is clipped and shifted (one law for nested clocks);
--   shift        `delay-delay`: delays add (events act by `shiftE`, `shift-zero`, `shift-shift`);
--   Par          events concatenate, so `Par` is associative on the nose and commutative up to
--                permutation of the events (`par-comm-events`); the readings agree when `⊙` is
--                commutative (`read-perm`);
--   Seq          associative as a reading, for non-negative durations (`seq-assoc`).
--
-- Not claimed: the swap law `(a ⨾ b) ∥ (c ⨾ d) = (a ∥ c) ⨾ (b ∥ d)` (false: leaves are
-- eternal, so the operands need a `Windowed` hypothesis); a tick law for `Repeat` beyond ℕ.

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Slides.Scalar.Core using (OrdMon; Sub)

module Slides.Scene.Laws {T D X : Set} (M : OrdMon T) (Sb : Sub M) (val : D → T → T)
       (_⊙_ : X → X → X) (⊙-assoc : ∀ a b c → (a ⊙ b) ⊙ c ≡ a ⊙ (b ⊙ c)) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc)
import Data.Nat as ℕ
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Properties as ListP
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_) renaming (refl to ↭refl; prep to ↭prep; swap to ↭swap; trans to ↭trans)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as ↭P
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Data.Container.FreeMonad using (_⋆_; pure; impure; _>>=_)
open import Relation.Binary.PropositionalEquality using (refl; cong; cong₂; sym; trans)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Container.Interpret.Plain using (pfold; pfold-bind)
open import Slides.Scene.Syntax
open import Slides.Scene.Events {T} {D} M Sb
open import Slides.Scene.Arith M Sb
open import Slides.Scene.Sample {T} {D} {X} M Sb val _⊙_ ⊙-assoc
open OrdMon M
open Sub Sb

------------------------------------------------------------------------
-- Nesting by substitution

events-bind : ∀ {A B L : Set} (f : B → Media L) (h : A → Scene T D B) (s : Scene T D A) →
              media f (s >>= h) ≡ media (λ a → media f (h a)) s
events-bind f h s = pfold-bind (≡P.setoid (Media _)) evCong h (λ a → refl) s

sample-bind : ∀ {A B : Set} (g : B → Timed) (h : A → Scene T D B) (s : Scene T D A) →
              timed g (s >>= h) ≡ timed (λ a → timed g (h a)) s
sample-bind g h s = pfold-bind (≡P.setoid Timed) dirCong h (λ a → refl) s

-- the events of a substituted scene, read, are the outer scene read with each leaf read as
-- the scene substituted for it
reading-bind : ∀ {A B : Set} (ℓ : B → T → X) (h : A → Scene T D B) (s : Scene T D A) → ∀ t q →
               readE ℓ (events (s >>= h)) t q ≡ proj₂ (timed (λ a → sample ℓ (h a)) s) t q
reading-bind ℓ h s t q =
  trans (proj₂ (proj₂ (events-sample ℓ (s >>= h))) t q)
        (cong (λ x → proj₂ x t q) (sample-bind (leafT ℓ) h s))

-- a scene in a windowed, delayed leaf is clipped and shifted
nest-window : ∀ {A B : Set} δ d (a : A) (h : A → Scene T D B) →
              mediaOf (delay δ (hold d (pure a)) >>= h) ≡ delayM δ (holdM d (mediaOf (h a)))
nest-window δ d a h = events-bind leafM h (delay δ (hold d (pure a)))

------------------------------------------------------------------------
-- Shifts add

map-shift : ∀ {L : Set} δ ε (es : List (Event L)) →
            map (shiftE δ) (map (shiftE ε) es) ≡ map (shiftE (δ + ε)) es
map-shift δ ε []       = refl
map-shift δ ε (e ∷ es) = cong₂ _∷_ (shift-shift δ ε e) (map-shift δ ε es)

delay-delay : ∀ {δ ε} → 0# ≤ δ → 0# ≤ ε → ∀ {L} (x : Media L) →
              delayM δ (delayM ε x) ≡ delayM (δ + ε) x
delay-delay {δ} {ε} 0≤δ 0≤ε (d , es)
  rewrite pos-≤ 0≤δ | pos-≤ 0≤ε | pos-≤ (≤-trans (≤-reflexive (sym (+-idˡ 0#))) (+-mono 0≤δ 0≤ε))
  = cong₂ _,_ (sym (+-assoc δ ε d)) (map-shift δ ε es)

delay-zero : ∀ {L} (x : Media L) → delayM 0# x ≡ x
delay-zero {L} (d , es) rewrite pos-≤ (≤-refl {0#}) | +-idˡ d = cong (d ,_) (go es)
  where go : ∀ (es : List (Event L)) → map (shiftE 0#) es ≡ es
        go []       = refl
        go (e ∷ es) = cong₂ _∷_ (shift-zero e) (go es)

------------------------------------------------------------------------
-- Par

duration-par : ∀ {A} (a b : Scene T D A) → duration (a ∥ b) ≡ duration a ⊔ duration b
duration-par a b = refl

events-par : ∀ {A} (a b : Scene T D A) → events (a ∥ b) ≡ events a ++ events b
events-par a b = refl

par-assoc-events : ∀ {A} (a b c : Scene T D A) → events ((a ∥ b) ∥ c) ≡ events (a ∥ (b ∥ c))
par-assoc-events a b c = ListP.++-assoc (events a) (events b) (events c)

par-comm-events : ∀ {A} (a b : Scene T D A) → events (a ∥ b) ↭ events (b ∥ a)
par-comm-events a b = ↭P.++-comm (events a) (events b)

module _ (⊙-comm : ∀ a b → a ⊙ b ≡ b ⊙ a) where

  merge-comm : ∀ x y → merge x y ≡ merge y x
  merge-comm nothing  nothing  = refl
  merge-comm nothing  (just _) = refl
  merge-comm (just _) nothing  = refl
  merge-comm (just a) (just b) = cong just (⊙-comm a b)

  merge-swap : ∀ x y z → merge x (merge y z) ≡ merge y (merge x z)
  merge-swap x y z = trans (sym (merge-assoc x y z))
    (trans (cong (λ u → merge u z) (merge-comm x y)) (merge-assoc y x z))

  -- reading does not see the order of the events
  read-perm : ∀ {L} (ℓ : L → T → X) {es fs : List (Event L)} → es ↭ fs → ∀ t q →
              readE ℓ es t q ≡ readE ℓ fs t q
  read-perm ℓ ↭refl          t q = refl
  read-perm ℓ (↭prep e p)    t q = cong (merge (readEv ℓ e t q)) (read-perm ℓ p t q)
  read-perm ℓ (↭swap {xs} {ys} e f p)  t q =
    trans (cong (merge (readEv ℓ e t q)) (cong (merge (readEv ℓ f t q)) (read-perm ℓ p t q)))
          (merge-swap (readEv ℓ e t q) (readEv ℓ f t q) (readE ℓ ys t q))
  read-perm ℓ (↭trans p p′)  t q = trans (read-perm ℓ p t q) (read-perm ℓ p′ t q)

  par-comm : ∀ {A} (ℓ : A → T → X) (a b : Scene T D A) → ∀ t q →
             readE ℓ (events (a ∥ b)) t q ≡ readE ℓ (events (b ∥ a)) t q
  par-comm ℓ a b t q = read-perm ℓ (par-comm-events a b) t q

------------------------------------------------------------------------
-- Seq is associative (non-negative durations)

private
  nn+ : ∀ {a b} → 0# ≤ a → 0# ≤ b → 0# ≤ a + b
  nn+ 0≤a 0≤b = ≤-trans (≤-reflexive (sym (+-idˡ 0#))) (+-mono 0≤a 0≤b)

  -- facts about the position of `t` against the three cut points
  ge0 : ∀ {a t} → a ≤ t → 0# ≤ t - a
  ge0 {a} a≤t = unshift-≤ a≤t (≤-trans (≤-reflexive (+-idʳ a)) a≤t)

seq-assoc-pt : ∀ {a b c} → 0# ≤ a → 0# ≤ b → 0# ≤ c → ∀ t (ra rb rc : T → Maybe X) →
  merge (win (pos (a + b)) t (merge (win (pos a) t (ra t)) (back (pos a) t (λ u → win (pos b) u (rb u)))))
        (back (pos (a + b)) t (λ u → win (pos c) u (rc u)))
  ≡ merge (win (pos a) t (ra t))
          (back (pos a) t (λ u → win (pos (b + c)) u
                 (merge (win (pos b) u (rb u)) (back (pos b) u (λ v → win (pos c) v (rc v))))))
seq-assoc-pt {a} {b} {c} 0≤a 0≤b 0≤c t ra rb rc
  rewrite pos-≤ 0≤a | pos-≤ 0≤b | pos-≤ 0≤c | pos-≤ (nn+ 0≤a 0≤b) | pos-≤ (nn+ 0≤b 0≤c)
  with 0# ≤? t
... | no 0≰t with (a + b) ≤? t | a ≤? t
...   | no _ | no _    = refl
...   | yes h | _      = ⊥-elim (0≰t (≤-trans (nn+ 0≤a 0≤b) h))
...   | no _ | yes h   = ⊥-elim (0≰t (≤-trans 0≤a h))
seq-assoc-pt {a} {b} {c} 0≤a 0≤b 0≤c t ra rb rc | yes 0≤t with a ≤? t
... | no a≰t with (a + b) ≤? t
...   | yes h = ⊥-elim (a≰t (≤-trans (≤-+ 0≤b) h))
...   | no _  = merge-nothing (merge (ra t) nothing)
seq-assoc-pt {a} {b} {c} 0≤a 0≤b 0≤c t ra rb rc | yes 0≤t | yes a≤t with b ≤? (t - a) | (a + b) ≤? t
... | yes h₁ | no ¬h₂ = ⊥-elim (¬h₂ (shift-≤ a≤t h₁))
... | no ¬h₁ | yes h₂ = ⊥-elim (¬h₁ (unshift-≤ a≤t h₂))
seq-assoc-pt {a} {b} {c} 0≤a 0≤b 0≤c t ra rb rc | yes 0≤t | yes a≤t | no b≰ | no ab≰ with 0# ≤? (t - a) | (b + c) ≤? (t - a)
... | yes _ | no _  = refl
... | no ¬0 | _     = ⊥-elim (¬0 (ge0 a≤t))
... | yes _ | yes h = ⊥-elim (b≰ (≤-trans (≤-+ 0≤c) h))
seq-assoc-pt {a} {b} {c} 0≤a 0≤b 0≤c t ra rb rc | yes 0≤t | yes a≤t | yes b≤ | yes ab≤
  rewrite sub-sub a≤t b≤ with 0# ≤? (t - a) | 0# ≤? (t - (a + b)) | c ≤? (t - (a + b)) | (b + c) ≤? (t - a)
... | yes _ | yes _ | yes _ | yes _ = refl
... | yes _ | yes _ | no _  | no _  = refl
... | yes _ | yes _ | yes c≤ | no ¬bc =
  ⊥-elim (¬bc (unshift-≤ a≤t (≤-trans (≤-reflexive (sym (+-assoc a b c))) (shift-≤ ab≤ c≤))))
... | yes _ | yes _ | no ¬c | yes bc =
  ⊥-elim (¬c (unshift-≤ ab≤ (≤-trans (≤-reflexive (+-assoc a b c)) (shift-≤ a≤t bc))))
... | no ¬0 | _ | _ | _ = ⊥-elim (¬0 (ge0 a≤t))
... | _ | no ¬0 | _ | _ = ⊥-elim (¬0 (ge0 ab≤))

seq-assoc-timed : ∀ (x y z : Timed) → 0# ≤ proj₁ x → 0# ≤ proj₁ y → 0# ≤ proj₁ z →
  proj₁ (seqT (seqT x y) z) ≡ proj₁ (seqT x (seqT y z)) ×
  (∀ t q → proj₂ (seqT (seqT x y) z) t q ≡ proj₂ (seqT x (seqT y z)) t q)
seq-assoc-timed (a , rx) (b , ry) (c , rz) 0≤a 0≤b 0≤c =
  +-assoc a b c , λ t q → seq-assoc-pt 0≤a 0≤b 0≤c t (λ u → rx u q) (λ u → ry u q) (λ u → rz u q)

-- every scene has a non-negative duration
duration-nonneg : ∀ {A : Set} (g : A → Timed) → (∀ a → 0# ≤ proj₁ (g a)) →
                  ∀ s → 0# ≤ proj₁ (timed g s)
duration-nonneg g ok (pure a)               = ok a
duration-nonneg g ok (impure (Seq , k))     = nn+ (duration-nonneg g ok (k zero)) (duration-nonneg g ok (k (suc zero)))
duration-nonneg g ok (impure (Par , k))     = ≤-trans (duration-nonneg g ok (k zero)) (⊔-ub₁ _ _)
duration-nonneg g ok (impure (Hold d , k))  = pos-nonneg d
duration-nonneg g ok (impure (Delay d , k)) = nn+ (pos-nonneg d) (duration-nonneg g ok (k tt))
duration-nonneg g ok (impure (Drive c , k)) = duration-nonneg g ok (k tt)
duration-nonneg g ok (impure (Repeat n , k)) = rep n (duration-nonneg g ok (k tt))
  where rep : ∀ n {x : Timed} → 0# ≤ proj₁ x → 0# ≤ proj₁ (repT n x)
        rep ℕ.zero    h = ≤-refl
        rep (ℕ.suc n) h = nn+ h (rep n h)

seq-assoc : ∀ {A : Set} (ℓ : A → T → X) (a b c : Scene T D A) →
            proj₁ (sample ℓ ((a ⨾ b) ⨾ c)) ≡ proj₁ (sample ℓ (a ⨾ (b ⨾ c))) ×
            (∀ t q → proj₂ (sample ℓ ((a ⨾ b) ⨾ c)) t q ≡ proj₂ (sample ℓ (a ⨾ (b ⨾ c))) t q)
seq-assoc ℓ a b c = seq-assoc-timed (sample ℓ a) (sample ℓ b) (sample ℓ c) (nn a) (nn b) (nn c)
  where nn = duration-nonneg (leafT ℓ) (λ _ → ≤-refl)

-- the same on events
seq-assoc-events : ∀ {A : Set} (ℓ : A → T → X) (a b c : Scene T D A) → ∀ t q →
                   readE ℓ (events ((a ⨾ b) ⨾ c)) t q ≡ readE ℓ (events (a ⨾ (b ⨾ c))) t q
seq-assoc-events ℓ a b c t q =
  trans (proj₂ (proj₂ (events-sample ℓ ((a ⨾ b) ⨾ c))) t q)
    (trans (proj₂ (seq-assoc ℓ a b c) t q)
           (sym (proj₂ (proj₂ (events-sample ℓ (a ⨾ (b ⨾ c)))) t q)))

------------------------------------------------------------------------
-- Repeat

repeat-zero : ∀ {A : Set} (a : Scene T D A) → mediaOf (repeat ℕ.zero a) ≡ (0# , [])
repeat-zero a = refl

repeat-suc : ∀ {A : Set} n (a : Scene T D A) → mediaOf (repeat (ℕ.suc n) a) ≡ seqM (mediaOf a) (mediaOf (repeat n a))
repeat-suc n a = refl
