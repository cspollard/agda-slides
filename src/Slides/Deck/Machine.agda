{-# OPTIONS --safe --without-K #-}

-- The machine of a deck: the visible slide at a position, with labels.
--
-- DECISION (the machine view at deck level).  The machine's state is a tick position and its
-- output is the *visible slide*, the flat scene read at that tick (`Slides.Deck.Read.visible`):
--
--   deckM d = navM (steps d ∸ 1) (labels d) (visible (flat d))
--
-- The accumulated view (everything shown since the slide began) is derived, not a second
-- machine: on a slide it is the concatenation of the chunks so far, and `accum-step` says each
-- tick only adds a chunk, so the visible slide and the accumulated view coincide for the pause
-- fragment (`chunk-visible`, `accum-step`).  They differ only for content that leaves (a window
-- inside a chunk), which the visible view shows correctly and the accumulated one cannot.  The
-- visible view also makes `prev` and `goto` trivial (no replay), and is the one that agrees with
-- a backend that renders a slide.
--
-- Labels.  A slide carries an optional label; the table maps it to the onset of the slide's
-- event in the deck read with each slide leaf of its own duration (`slideM`).
--
--   slide-starts      the events of a deck of slides are the slides at the running sums of the ticks
--   labelOf-++, labelOf-shift, labelOf-leaf
--                     the table of overlaid scenes is the first's, else the second's; delaying by
--                     `k` shifts every label by `k`; a labelled slide leaf is at its onset
--   start-visible     going to the start of any slide shows its first chunk, nothing else
--   goto-label-visible  `gotoLabel l` shows the first chunk of the slide labelled `l`
--   accum-step        a tick adds exactly the next chunk

module Slides.Deck.Machine where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (++⁺; map⁺)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe; _<∣>_)
import Data.Maybe.Base as Maybe
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_)
import Data.Nat.Properties as ℕP
import Data.Nat.Base as ℕ
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.String.Base using (String)
import Data.String.Properties as Str
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; dec-false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
import Data.List.Properties as ListP
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)

open import Slides.Scalar.Model.Nat using (natMon; natSub)
open import Slides.Scene.Syntax
import Slides.Program.Machine as Machine
open import Slides.Program.Navigation
open import Slides.Deck.Content
open import Slides.Deck.Syntax
open import Slides.Deck.Read

import Slides.Scene.Events {ℕ} {⊥} natMon natSub as E

------------------------------------------------------------------------
-- Slide events: each slide leaf lasts its own ticks

-- a slide as a leaf: it lasts `ticks`, and is present at its onset
slideM : Slide → E.Media Slide
slideM s = ticks s , E.event 0 nothing nothing s ∷ []

slideEvents : Deck → List (E.Event Slide)
slideEvents d = proj₂ (E.media slideM d)

steps : Deck → ℕ
steps d = proj₁ (E.media slideM d)

------------------------------------------------------------------------
-- The label table

matches : Maybe String → String → Bool
matches nothing  l = false
matches (just m) l = ⌊ m Str.≟ l ⌋

-- the onset of the first slide with the label
labelOf : List (E.Event Slide) → String → Maybe ℕ
labelOf []       l = nothing
labelOf (e ∷ es) l = if matches (Slide.label (E.leaf e)) l then just (E.onset e) else labelOf es l

labelOf-++ : ∀ es fs l → labelOf (es ++ fs) l ≡ (labelOf es l <∣> labelOf fs l)
labelOf-++ []       fs l = refl
labelOf-++ (e ∷ es) fs l with matches (Slide.label (E.leaf e)) l
... | true  = refl
... | false = labelOf-++ es fs l

-- delaying a scene by `k` shifts its labels by `k` (the legacy `labelTable-next`)
labelOf-shift : ∀ k es l → labelOf (map (E.shiftE k) es) l ≡ Maybe.map (k +_) (labelOf es l)
labelOf-shift k []       l = refl
labelOf-shift k (e ∷ es) l with matches (Slide.label (E.leaf e)) l
... | true  = refl
... | false = labelOf-shift k es l

-- a labelled slide is at its onset (the legacy `labelTable-label`)
labelOf-leaf : ∀ s l sp → Slide.label s ≡ just l → labelOf (E.event 0 sp nothing s ∷ []) l ≡ just 0
labelOf-leaf s l sp e rewrite e with l Str.≟ l
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

labels : Deck → String → Maybe ℕ
labels d = labelOf (slideEvents d)

------------------------------------------------------------------------
-- The machine

deckM : Deck → Machine.Machine Nav (Maybe Flow)
deckM d = navM (steps d ∸ 1) (labels d) (visible (flat d))

------------------------------------------------------------------------
-- The events of a deck of slides: each slide at the sum of the ticks before it

starts : Slide → List Slide → List (ℕ × Slide)
starts s []       = (0 , s) ∷ []
starts s (t ∷ ts) = (0 , s) ∷ map (λ x → ticks s + proj₁ x , proj₂ x) (starts t ts)

ol′ : E.Event Slide → ℕ × Slide
ol′ e = E.onset e , E.leaf e

-- a window keeps what starts inside it
clipE-keep : ∀ w es → All (λ e → E.onset e < w) es → map ol′ (E.clipE w es) ≡ map ol′ es
clipE-keep w []       _          = refl
clipE-keep w (e ∷ es) (lt ∷ all) rewrite dec-false (w ℕP.≤? E.onset e) (ℕP.<⇒≱ lt) =
  cong (ol′ e ∷_) (clipE-keep w es all)

steps-from : ∀ s ss → steps (deckFrom s ss) ≡ total s ss
steps-from s []       = refl
steps-from s (t ∷ ts) = cong (ticks s +_) (steps-from t ts)

clip-below : ∀ w (es : List (E.Event Slide)) → All (λ e → E.onset e < w) (E.clipE w es)
clip-below w []       = []
clip-below w (e ∷ es) with w ℕ.≤ᵇ E.onset e in eq
... | true  = clip-below w es
... | false = ℕP.≰⇒> (λ le → subst T eq (ℕP.≤⇒≤ᵇ le)) ∷ clip-below w es

shift-ol : ∀ k es → map ol′ (map (E.shiftE k) es) ≡ map (λ x → k + proj₁ x , proj₂ x) (map ol′ es)
shift-ol k es = trans (sym (ListP.map-∘ es)) (ListP.map-∘ es)

-- a slide, then the rest `Y` (which lasts `n`, with its events inside): the slides' starts add
seq-starts : ∀ s (Y : E.Media Slide) n → proj₁ Y ≡ n → All (λ e → E.onset e < n) (proj₂ Y) →
             map ol′ (proj₂ (E.seqM (slideM s) Y)) ≡ (0 , s) ∷ map (λ x → ticks s + proj₁ x , proj₂ x) (map ol′ (proj₂ Y))
seq-starts s Y n refl all = cong ((0 , s) ∷_) (trans (shift-ol (ticks s) _) (cong (map _) (clipE-keep _ _ all)))

seq-below : ∀ s (Y : E.Media Slide) n → proj₁ Y ≡ n → All (λ e → E.onset e < n) (proj₂ Y) →
            All (λ e → E.onset e < ticks s + n) (proj₂ (E.seqM (slideM s) Y))
seq-below s Y n refl all =
  ++⁺ (ℕP.<-≤-trans (ℕP.0<1+n {_}) (ℕP.m≤m+n (ticks s) n) ∷ [])
      (map⁺ (All.map (λ lt → ℕP.+-monoʳ-< (ticks s) lt) (clip-below n (proj₂ Y))))

below : ∀ s ss → All (λ e → E.onset e < total s ss) (slideEvents (deckFrom s ss))
below s []       = ℕP.0<1+n ∷ []
below s (t ∷ ts) = seq-below s (E.media slideM (deckFrom t ts)) (total t ts) (steps-from t ts) (below t ts)

slide-starts : ∀ s ss → map ol′ (slideEvents (deckFrom s ss)) ≡ starts s ss
slide-starts s []       = refl
slide-starts s (t ∷ ts) =
  trans (seq-starts s (E.media slideM (deckFrom t ts)) (total t ts) (steps-from t ts) (below t ts))
        (cong (λ z → (0 , s) ∷ map _ z) (slide-starts t ts))

------------------------------------------------------------------------
-- Labels of a deck of slides

labelIn : List (ℕ × Slide) → String → Maybe ℕ
labelIn []              l = nothing
labelIn ((i , s) ∷ xs)  l = if matches (Slide.label s) l then just i else labelIn xs l

labelOf-ol : ∀ es l → labelOf es l ≡ labelIn (map ol′ es) l
labelOf-ol []       l = refl
labelOf-ol (e ∷ es) l with matches (Slide.label (E.leaf e)) l
... | true  = refl
... | false = labelOf-ol es l

-- the table of a deck of slides is the first match among the running starts
table-deck : ∀ s ss l → labels (deckFrom s ss) l ≡ labelIn (starts s ss) l
table-deck s ss l = trans (labelOf-ol (slideEvents (deckFrom s ss)) l)
                          (cong (λ z → labelIn z l) (slide-starts s ss))

labelIn-∈ : ∀ xs l {i} → labelIn xs l ≡ just i → ∃ λ t → (i , t) ∈ xs × matches (Slide.label t) l ≡ true
labelIn-∈ ((j , t) ∷ xs) l e with matches (Slide.label t) l in m
labelIn-∈ ((j , t) ∷ xs) l refl | true  = t , here refl , m
labelIn-∈ ((j , t) ∷ xs) l e    | false with labelIn-∈ xs l e
... | u , p , m′ = u , there p , m′

-- a slide starts below the total
starts-lt : ∀ s ss {i t} → (i , t) ∈ starts s ss → i < total s ss
starts-lt s ss {i} {t} p with ∈-map⁻ _ (subst ((i , t) ∈_) (sym (slide-starts s ss)) p)
... | e , m , refl = All.lookup (below s ss) m

-- the slide containing the start of a slide is that slide, at its first tick
locate-start : ∀ s ss {i t} → (i , t) ∈ starts s ss → locate s ss i ≡ just (t , 0)
locate-start s [] (here refl) = refl
locate-start s (t′ ∷ ts) (here refl) = refl
locate-start s (t′ ∷ ts) {i} {t} (there p) with ∈-map⁻ (λ x → ticks s + proj₁ x , proj₂ x) p
... | (j , u) , m , refl with (ticks s + j) ℕP.<? ticks s
...   | yes lt = ⊥-elim (ℕP.<⇒≱ lt (ℕP.m≤m+n (ticks s) j))
...   | no _   rewrite ℕP.m+n∸m≡n (ticks s) j = locate-start t′ ts m

-- going to the start of any slide shows its first chunk: a fresh slide
start-visible : ∀ s ss {i t} → (i , t) ∈ starts s ss →
                visible (flat (deckFrom s ss)) i ≡ just (accum (Slide.chunkL t) 0)
start-visible s ss p = trans (deck-visible s ss _) (cong show (locate-start s ss p))

-- `gotoLabel l` shows the first chunk of a slide with that label
goto-label-visible : ∀ s ss l {i} → labels (deckFrom s ss) l ≡ just i → ∀ p →
  ∃ λ t → matches (Slide.label t) l ≡ true ×
          Machine.out (deckM (deckFrom s ss)) (Machine.step (deckM (deckFrom s ss)) p (gotoLabel l))
            ≡ just (accum (Slide.chunkL t) 0)
goto-label-visible s ss l {i} e p with labelIn-∈ (starts s ss) l (trans (sym (table-deck s ss l)) e)
... | t , m , ok = t , ok ,
  trans (cong (visible (flat (deckFrom s ss))) (trans (gotoLabel-goto (steps (deckFrom s ss) ∸ 1) (labels (deckFrom s ss)) (visible (flat (deckFrom s ss))) p l i e)
          (ℕP.m≤n⇒m⊓n≡m (ℕP.<⇒≤pred (subst (i <_) (sym (steps-from s ss)) (starts-lt s ss m))))))
        (start-visible s ss m)

------------------------------------------------------------------------
-- The accumulated view: a tick adds the next chunk

at : List Flow → ℕ → Flow
at []       _       = []
at (d ∷ ds) zero    = d
at (d ∷ ds) (suc k) = at ds k

accum-step : ∀ c cs k → accumL c cs (suc k) ≡ accumL c cs k ++ at cs k
accum-step c []       k       = sym (ListP.++-identityʳ c)
accum-step c (d ∷ [])     zero    = refl
accum-step c (d ∷ e ∷ es) zero    = refl
accum-step c (d ∷ ds) (suc k) =
  trans (cong (c ++_) (accum-step d ds k)) (sym (ListP.++-assoc c (accumL d ds k) (at ds k)))
