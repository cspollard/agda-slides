{-# OPTIONS --safe --without-K #-}

-- Events: the meaning of a scene as a sparse list.
--
-- An `Event` is a leaf with an onset, a span (`nothing`: for ever) and the driver, if any, that
-- feeds the leaf its moving value.  Time inside the leaf is local: the leaf is read at the
-- time since its onset.  Shifting by `δ` moves only the onset, so `shiftE` is an action of the
-- durations (`shift-zero`, `shift-shift`): this is the whole of "nested clocks".  A window
-- keeps the events that start inside it and cuts their spans (`clipE`).
--
--      onset            onset + span
--        |<---- span ---->|           an event, in the time of its enclosing scene
--
-- The scene is read by one fold, `evH`, of the signature into `Media`: the duration and the
-- events.  A substitution of scenes for leaves is a bind, so its meaning is the fold with the
-- leaves' meanings (`events-bind`, from `pfold-bind`).  Durations below zero read as zero
-- (`pos`), so every onset is non-negative (`Pos`).  `Seq` and `Repeat` are not primitive
-- here: `Seq a b` is `a` held for its duration beside `b`, delayed by it and held for its own.

open import Slides.Scalar.Core using (OrdMon; Sub)

module Slides.Scene.Events {T D : Set} (M : OrdMon T) (Sb : Sub M) where

open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Data.Container.FreeMonad using (_⋆_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Container.Interpret.Plain using (Handler; Congruent; pfold)
open import Slides.Scene.Syntax
open OrdMon M
open Sub Sb

record Event (L : Set) : Set where
  constructor event
  field
    onset  : T
    span   : Maybe T
    driver : Maybe D
    leaf   : L
open Event public

Media : Set → Set
Media L = T × List (Event L)

-- durations below zero read as zero
pos : T → T
pos d = 0# ⊔ d

pos-nonneg : ∀ d → 0# ≤ pos d
pos-nonneg d = ⊔-ub₁ 0# d

pos-≤ : ∀ {d} → 0# ≤ d → pos d ≡ d
pos-≤ 0≤d = ⊔-≤ 0≤d

------------------------------------------------------------------------
-- Events: shifting, windowing, driving

shiftE : T → ∀ {L} → Event L → Event L
shiftE δ (event o s c a) = event (δ + o) s c a

-- the span cut at `r` (the room left in the window)
cut : Maybe T → T → T
cut nothing  r = r
cut (just s) r = select (s ≤? r) s r

cut-≤ : ∀ s r → cut s r ≤ r
cut-≤ nothing  r = ≤-refl
cut-≤ (just s) r with s ≤? r
... | yes h = h
... | no _  = ≤-refl

-- an event survives a window `[0, w)` iff it starts inside, and then ends inside
clipEv : T → ∀ {L} → Event L → Maybe (Event L)
clipEv w (event o s c a) = select (w ≤? o) nothing (just (event o (just (cut s (w - o))) c a))

consMb : ∀ {L} → Maybe (Event L) → List (Event L) → List (Event L)
consMb nothing  es = es
consMb (just e) es = e ∷ es

clipE : T → ∀ {L} → List (Event L) → List (Event L)
clipE w []       = []
clipE w (e ∷ es) = consMb (clipEv w e) (clipE w es)

-- the first driver met going outwards wins
driveE : D → ∀ {L} → Event L → Event L
driveE c (event o s nothing a) = event o s (just c) a
driveE c e@(event o s (just _) a) = e

Pos : ∀ {L} → Event L → Set
Pos e = 0# ≤ onset e

-- The shift action: nested clocks are one law.
shift-zero : ∀ {L} (e : Event L) → shiftE 0# e ≡ e
shift-zero (event o s c a) = cong (λ x → event x s c a) (+-idˡ o)

shift-shift : ∀ {L} δ ε (e : Event L) → shiftE δ (shiftE ε e) ≡ shiftE (δ + ε) e
shift-shift δ ε (event o s c a) = cong (λ x → event x s c a) (sym (+-assoc δ ε o))

------------------------------------------------------------------------
-- The meaning of a scene: duration and events

module _ {L : Set} where

  leafM : L → Media L
  leafM a = 0# , event 0# nothing nothing a ∷ []

  parM : Media L → Media L → Media L
  parM (d , es) (d′ , fs) = d ⊔ d′ , es ++ fs

  holdM : T → Media L → Media L
  holdM w (_ , es) = pos w , clipE (pos w) es

  delayM : T → Media L → Media L
  delayM w (d , es) = pos w + d , map (shiftE (pos w)) es

  driveM : D → Media L → Media L
  driveM c (d , es) = d , map (driveE c) es

  -- `a ⨾ b`: `a` for its duration, then `b` for its duration
  seqM : Media L → Media L → Media L
  seqM x y = proj₁ x + proj₁ y , proj₂ (parM (holdM (proj₁ x) x) (delayM (proj₁ x) (holdM (proj₁ y) y)))

  repM : ℕ → Media L → Media L
  repM zero    x = 0# , []
  repM (suc n) x = seqM x (repM n x)

  evH : Handler (SceneC T D) (Media L)
  evH Seq        k = seqM (k zero) (k (suc zero))
  evH Par        k = parM (k zero) (k (suc zero))
  evH (Hold d)   k = holdM d (k tt)
  evH (Delay d)  k = delayM d (k tt)
  evH (Repeat n) k = repM n (k tt)
  evH (Drive c)  k = driveM c (k tt)

  evCong : Congruent (SceneC T D) (≡P.setoid (Media L)) evH
  evCong Seq        e = cong₂ seqM (e zero) (e (suc zero))
  evCong Par        e = cong₂ parM (e zero) (e (suc zero))
  evCong (Hold d)   e = cong (holdM d) (e tt)
  evCong (Delay d)  e = cong (delayM d) (e tt)
  evCong (Repeat n) e = cong (repM n) (e tt)
  evCong (Drive c)  e = cong (driveM c) (e tt)

-- the meaning of a scene whose leaves mean `f a`
media : ∀ {A L : Set} → (A → Media L) → Scene T D A → Media L
media f = pfold (SceneC T D) evH f

-- ... and with the eternal leaf
mediaOf : ∀ {A : Set} → Scene T D A → Media A
mediaOf = media leafM

events : ∀ {A : Set} → Scene T D A → List (Event A)
events s = proj₂ (mediaOf s)

duration : ∀ {A : Set} → Scene T D A → T
duration s = proj₁ (mediaOf s)
