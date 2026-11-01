{-# OPTIONS --safe --without-K #-}

-- The switcher: behaviours of commands as Elliott-style time functions, driven by timed commands.
--
--   Behaviour   `T → P`: a value at every instant (the reading of a scene at local time)
--   Event C     occurrences `(t , c)`: a timed command stream, in any order (sortedness is a
--               hypothesis of nothing proved here; `lastFrom` takes the last occurrence listed)
--   upTo t es   the occurrences at or before `t` (inclusive: a command at `t` is already felt at `t`)
--   switch      `rd` reads an output as a behaviour of local time (`Func O (T ⇉ P)`).  At `t`, feed
--               the commands of `upTo t es` to `b : Beh C O` and read the output at `t − t_last`,
--               `t_last` the time of the last of them (`0#` when none).  A map of setoids
--               `Beh C O → (Event C ⇉ Behaviour)`.
--
--   switch-causal    occurrences agreeing up to `t` give equal readings at `t`
--   switch-future    occurrences strictly after `t` do not affect the reading at `t`
--   switch-natural   the output map commutes with switching, when it commutes with the readers
--
-- `Behaviour`, the signature of §1 of plans/FRP.md, is the discrete `Beh` with the clock replaced
-- by time; `switch` is the bridge from the command-counting clock to it (`Slides.Program.FRP`
-- instantiates it for programs).

open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)
open import Slides.Scalar.Core using (OrdMon; Sub)

module Semantics.FRP {T : Set} (M : OrdMon T) (Sb : Sub M) (C : Set) (P : Setoid 0ℓ 0ℓ) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open import Semantics.Behaviour using (Beh; _⇉_; mapO)
open OrdMon M
open Sub Sb
private module P = Setoid P

Behaviour : Setoid 0ℓ 0ℓ
Behaviour = T ⇉ P

Event : Set
Event = List (T × C)

upTo : T → Event → Event
upTo t []             = []
upTo t ((s , c) ∷ es) with s ≤? t
... | yes _ = (s , c) ∷ upTo t es
... | no _  = upTo t es

lastFrom : T → Event → T
lastFrom d []             = d
lastFrom d ((s , _) ∷ es) = lastFrom s es

-- the reading after the occurrences `us`, at time `t`
reading : ∀ {O : Setoid 0ℓ 0ℓ} → Func O Behaviour → Setoid.Carrier (Beh C O) → Event → T → P.Carrier
reading rd b us t = (rd ⟨$⟩ b (map proj₂ us)) (t - lastFrom 0# us)

module _ {O : Setoid 0ℓ 0ℓ} (rd : Func O Behaviour) where

  switch : Func (Beh C O) (Event ⇉ Behaviour)
  switch = record
    { to = λ b es t → reading rd b (upTo t es) t
    ; cong = λ e es t → Func.cong rd (e _) (t - lastFrom 0# (upTo t es)) }

  -- occurrences that agree up to `t` give equal readings at `t`
  switch-causal : ∀ b {es fs} t → upTo t es ≡ upTo t fs →
                  ((switch ⟨$⟩ b) es t) P.≈ ((switch ⟨$⟩ b) fs t)
  switch-causal b {es} t eq = subst (λ us → reading rd b (upTo t es) t P.≈ reading rd b us t) eq P.refl

  -- occurrences strictly after `t` are not seen at `t`
  switch-future : ∀ b es fs t → All (λ o → ¬ proj₁ o ≤ t) fs →
                  ((switch ⟨$⟩ b) (es ++ fs) t) P.≈ ((switch ⟨$⟩ b) es t)
  switch-future b es fs t late = switch-causal b {es ++ fs} {es} t (upTo-++ es late)
    where
      upTo-late : ∀ {fs} → All (λ o → ¬ proj₁ o ≤ t) fs → upTo t fs ≡ []
      upTo-late []                 = refl
      upTo-late {(s , _) ∷ _} (n ∷ l) with s ≤? t
      ... | yes le = ⊥-elim (n le)
      ... | no _   = upTo-late l
      upTo-++ : ∀ es {fs} → All (λ o → ¬ proj₁ o ≤ t) fs → upTo t (es ++ fs) ≡ upTo t es
      upTo-++ []             l = upTo-late l
      upTo-++ ((s , c) ∷ es) l with s ≤? t
      ... | yes _ = cong ((s , c) ∷_) (upTo-++ es l)
      ... | no _  = upTo-++ es l

-- the output map commutes with switching when it commutes with the readers
module _ {O O′ : Setoid 0ℓ 0ℓ} (rd : Func O Behaviour) (rd′ : Func O′ Behaviour) (f : Func O O′)
         (comm : ∀ x u → (rd′ ⟨$⟩ (f ⟨$⟩ x)) u P.≈ (rd ⟨$⟩ x) u) where

  switch-natural : ∀ b es t → ((switch rd′ ⟨$⟩ (mapO f ⟨$⟩ b)) es t) P.≈ ((switch rd ⟨$⟩ b) es t)
  switch-natural b es t = comm _ _
