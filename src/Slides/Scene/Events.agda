{-# OPTIONS --safe --without-K #-}

-- Events: a scene as a sparse list, the fold `evH` of the signature into durations and events.
--
-- An `Event` is a leaf with an onset, a span (`nothing`: for ever) and the driver feeding it.
--
--      onset            onset + span
--        |<---- span ---->|        an event, in the time of the enclosing scene
--
-- Time in a leaf is local (time since onset), so a shift moves only onsets: `shiftE` is an
-- action of the durations, which is all of "nested clocks".  A window keeps the events that
-- start inside it and cuts their spans (`clipE`); durations below zero read as zero (`pos`).
--
--   shift-zero, shift-shift   `shiftE` is an action
--   events-bind               meaning of a substitution is the fold with the leaves' meanings
--
-- `Seq` and `Repeat` are derived: `a ⨾ b` is `a` held for its duration beside `b` delayed by it.

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
import Slides.Scene.Algebra
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
open import Slides.Scene.Algebra M public using (pos; pos-nonneg; pos-≤; Payload)

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

-- The meaning of a scene: duration and events

module _ {L : Set} where

  leafM : L → Media L
  leafM a = 0# , event 0# nothing nothing a ∷ []

  evP : Payload D (List (Event L))
  evP = record { none = [] ; par = _++_ ; clip = λ w → clipE w ; shift = λ w → map (shiftE w) ; driveP = λ c → map (driveE c) }

  -- `a ⨾ b` is `a` for its duration, then `b` for its duration (derived: `Slides.Scene.Algebra`)
  open Slides.Scene.Algebra.Temporal M evP public using ()
    renaming (parC to parM; holdC to holdM; delayC to delayM; driveC to driveM; seqC to seqM; repC to repM
             ; handler to evH; handler-≡ to evCong)

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
