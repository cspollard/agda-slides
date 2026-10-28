{-# OPTIONS --safe --without-K #-}

-- Two readings of a scene as "time to maybe-value", and the theorem that they agree.
--
-- A leaf is read by `ℓ : L → T → X` at its parameter: the value of its driver at its local
-- time, or 0 if no `Drive` encloses it.  Values overlay by `_⊙_`, associative; absence
-- (`nothing`) is the unit of `Par` per sample (`merge`).
--
--   direct     the fold of the signature into `Timed`: a duration and a function of time and of
--              the driver of the enclosing `Drive`, with `Hold` a window, `Delay` a shift of the
--              time argument, `Drive` the choice of driver (`sample`);
--   events     the fold of the event list (`readE`), each event active on `[onset, onset+span)`.
--
-- `events-sample`: `readE ℓ (events s) t q ≡ sample ℓ s t q` (the key theorem): the sparse list
-- is the direct pointwise semantics.  It is proved by `pfold-rel`, one lemma per operation of
-- the signature (`rel-par`, `rel-hold`, `rel-delay`, `rel-drive`), with the invariant that
-- onsets are non-negative.  Then: both readings respect bind (`sample-bind`, `events-bind`,
-- `reading-bind`), `Par` is commutative and associative up to permutation of the events,
-- and `Seq` is associative (`seq-assoc`, for non-negative durations).

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Slides.Scalar.Core using (OrdMon; Sub)

module Slides.Scene.Sample {T D X : Set} (M : OrdMon T) (Sb : Sub M) (val : D → T → T)
       (_⊙_ : X → X → X) (⊙-assoc : ∀ a b c → (a ⊙ b) ⊙ c ≡ a ⊙ (b ⊙ c)) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; _++_; map; mapMaybe)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺; map⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Container.FreeMonad using (_>>=_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
import Relation.Binary.PropositionalEquality.Properties as ≡P

open import Container.Interpret.Plain using (Handler; Congruent; pfold; pfold-rel; pfold-bind)
open import Slides.Scene.Syntax
open import Slides.Scene.Events {T} {D} M Sb
open import Slides.Scene.Arith M Sb
open OrdMon M
open Sub Sb

------------------------------------------------------------------------
-- Overlay with absence as unit

merge : Maybe X → Maybe X → Maybe X
merge nothing  y        = y
merge (just a) nothing  = just a
merge (just a) (just b) = just (a ⊙ b)

merge-nothing : ∀ x → merge x nothing ≡ x
merge-nothing nothing  = refl
merge-nothing (just _) = refl

merge-assoc : ∀ x y z → merge (merge x y) z ≡ merge x (merge y z)
merge-assoc nothing  y        z        = refl
merge-assoc (just a) nothing  z        = refl
merge-assoc (just a) (just b) nothing  = refl
merge-assoc (just a) (just b) (just c) = cong just (⊙-assoc a b c)

-- the driver of the leaf, else the driver of the context, read at local time
orElse : Maybe D → Maybe D → Maybe D
orElse (just c) _ = just c
orElse nothing  q = q

param : Maybe D → T → T
param nothing  τ = 0#
param (just c) τ = val c τ

------------------------------------------------------------------------
-- Reading events

-- an event of span `s` is over once `onset + s` is reached
until : Maybe T → T → T → Maybe X → Maybe X
until nothing  o t y = y
until (just s) o t y = select ((o + s) ≤? t) nothing y

module _ {L : Set} (ℓ : L → T → X) where

  readEv : Event L → T → Maybe D → Maybe X
  readEv (event o s c a) t q =
    select (o ≤? t) (until s o t (just (ℓ a (param (orElse c q) (t - o))))) nothing

  readMb : Maybe (Event L) → T → Maybe D → Maybe X
  readMb nothing  t q = nothing
  readMb (just e) t q = readEv e t q

  readE : List (Event L) → T → Maybe D → Maybe X
  readE []       t q = nothing
  readE (e ∷ es) t q = merge (readEv e t q) (readE es t q)

  read-++ : ∀ es fs t q → readE (es ++ fs) t q ≡ merge (readE es t q) (readE fs t q)
  read-++ []       fs t q = refl
  read-++ (e ∷ es) fs t q = trans (cong (merge (readEv e t q)) (read-++ es fs t q))
                                  (sym (merge-assoc (readEv e t q) (readE es t q) (readE fs t q)))

------------------------------------------------------------------------
-- The direct reading

Rd : Set
Rd = T → Maybe D → Maybe X

Timed : Set
Timed = T × Rd

-- present on [0, w)
win : T → T → Maybe X → Maybe X
win w t y = select (0# ≤? t) (select (w ≤? t) nothing y) nothing

-- the time argument shifted by `w`, absent before it
back : T → T → (T → Maybe X) → Maybe X
back w t r = select (w ≤? t) (r (t - w)) nothing

module _ {L : Set} where

  leafT : (L → T → X) → L → Timed
  leafT ℓ a = 0# , λ t q → select (0# ≤? t) (just (ℓ a (param q t))) nothing

parT : Timed → Timed → Timed
parT (d , r) (d′ , r′) = d ⊔ d′ , λ t q → merge (r t q) (r′ t q)

holdT : T → Timed → Timed
holdT w (_ , r) = pos w , λ t q → win (pos w) t (r t q)

delayT : T → Timed → Timed
delayT w (d , r) = pos w + d , λ t q → back (pos w) t (λ u → r u q)

driveT : D → Timed → Timed
driveT c (d , r) = d , λ t _ → r t (just c)

seqT : Timed → Timed → Timed
seqT x y = proj₁ x + proj₁ y , proj₂ (parT (holdT (proj₁ x) x) (delayT (proj₁ x) (holdT (proj₁ y) y)))

repT : ℕ → Timed → Timed
repT zero    x = 0# , λ _ _ → nothing
repT (suc n) x = seqT x (repT n x)

dirH : Handler (SceneC T D) Timed
dirH Seq        k = seqT (k zero) (k (suc zero))
dirH Par        k = parT (k zero) (k (suc zero))
dirH (Hold d)   k = holdT d (k tt)
dirH (Delay d)  k = delayT d (k tt)
dirH (Repeat n) k = repT n (k tt)
dirH (Drive c)  k = driveT c (k tt)

dirCong : Congruent (SceneC T D) (≡P.setoid Timed) dirH
dirCong Seq        e = cong₂ seqT (e zero) (e (suc zero))
dirCong Par        e = cong₂ parT (e zero) (e (suc zero))
dirCong (Hold d)   e = cong (holdT d) (e tt)
dirCong (Delay d)  e = cong (delayT d) (e tt)
dirCong (Repeat n) e = cong (repT n) (e tt)
dirCong (Drive c)  e = cong (driveT c) (e tt)

-- the direct meaning of a scene whose leaves mean `g a`, and with the eternal leaf
timed : ∀ {A : Set} → (A → Timed) → Scene T D A → Timed
timed g = pfold (SceneC T D) dirH g

sample : ∀ {A : Set} → (A → T → X) → Scene T D A → Timed
sample ℓ = timed (leafT ℓ)

------------------------------------------------------------------------
-- Agreement of the two readings

module _ {L : Set} (ℓ : L → T → X) where

  Rel : Media L → Timed → Set
  Rel (d , es) (d′ , r) = d ≡ d′ × All Pos es × (∀ t q → readE ℓ es t q ≡ r t q)

  ---- overlay commutes with the window and the shift
  win-merge : ∀ w t a b → win w t (merge a b) ≡ merge (win w t a) (win w t b)
  win-merge w t a b with 0# ≤? t
  ... | no _  = refl
  ... | yes _ with w ≤? t
  ...   | yes _ = refl
  ...   | no _  = refl

  back-merge : ∀ w t (r r′ : T → Maybe X) →
               back w t (λ u → merge (r u) (r′ u)) ≡ merge (back w t r) (back w t r′)
  back-merge w t r r′ with w ≤? t
  ... | yes _ = refl
  ... | no _  = refl

  back-cong : ∀ w t {r r′ : T → Maybe X} → (∀ u → r u ≡ r′ u) → back w t r ≡ back w t r′
  back-cong w t e with w ≤? t
  ... | yes _ = e _
  ... | no _  = refl

  ---- the leaf
  rel-leaf : ∀ a → Rel (leafM a) (leafT ℓ a)
  rel-leaf a = refl , ≤-refl ∷ [] , λ t q → trans (merge-nothing _) (at t q)
    where
      at : ∀ t q → readEv ℓ (event 0# nothing nothing a) t q ≡ proj₂ (leafT ℓ a) t q
      at t q with 0# ≤? t
      ... | yes 0≤t = cong (λ τ → just (ℓ a (param q τ))) (sub-zero 0≤t)
      ... | no _    = refl

  ---- Par
  rel-par : ∀ {x x′ y y′} → Rel x x′ → Rel y y′ → Rel (parM x y) (parT x′ y′)
  rel-par {_ , es} {_ , r} {_ , fs} {_ , r′} (refl , pa , ra) (refl , pb , rb) =
    refl , ++⁺ pa pb , λ t q → trans (read-++ ℓ es fs t q) (cong₂ merge (ra t q) (rb t q))

  ---- Drive
  read-drive : ∀ c es t q → readE ℓ (map (driveE c) es) t q ≡ readE ℓ es t (just c)
  read-drive c []       t q = refl
  read-drive c (e ∷ es) t q = cong₂ merge (ev e) (read-drive c es t q)
    where
      ev : ∀ (e : Event L) → readEv ℓ (driveE c e) t q ≡ readEv ℓ e t (just c)
      ev (event o nothing nothing a)  = refl
      ev (event o (just s) nothing a) = refl
      ev (event o nothing (just _) a)  = refl
      ev (event o (just s) (just _) a) = refl

  pos-drive : ∀ c {es} → All Pos es → All Pos (map (driveE c) es)
  pos-drive c []        = []
  pos-drive c {e ∷ _} (p ∷ ps) = pd e p ∷ pos-drive c ps
    where pd : ∀ (e : Event L) → Pos e → Pos (driveE c e)
          pd (event o s nothing a)  p = p
          pd (event o s (just _) a) p = p

  rel-drive : ∀ c {x x′} → Rel x x′ → Rel (driveM c x) (driveT c x′)
  rel-drive c {_ , es} {_ , r} (refl , pa , ra) =
    refl , pos-drive c pa , λ t q → trans (read-drive c es t q) (ra t (just c))

  ---- Delay: the shift of events is the shift of the time argument
  until-shift : ∀ {w t} (s : Maybe T) o (y : Maybe X) → w ≤ t → until s (w + o) t y ≡ until s o (t - w) y
  until-shift nothing  o y w≤t = refl
  until-shift {w} {t} (just s) o y w≤t
    rewrite +-assoc w o s with (w + (o + s)) ≤? t | (o + s) ≤? (t - w)
  ... | yes _  | yes _  = refl
  ... | no _   | no _   = refl
  ... | yes h  | no ¬h  = ⊥-elim (¬h (unshift-≤ w≤t h))
  ... | no ¬h  | yes h  = ⊥-elim (¬h (shift-≤ w≤t h))

  read-shift-ev : ∀ w (e : Event L) → Pos e → ∀ t q →
                  readEv ℓ (shiftE w e) t q ≡ back w t (λ u → readEv ℓ e u q)
  read-shift-ev w (event o s c a) 0≤o t q with w ≤? t
  ... | no w≰t with (w + o) ≤? t
  ...   | no _   = refl
  ...   | yes h  = ⊥-elim (w≰t (≤-trans (≤-+ 0≤o) h))
  read-shift-ev w (event o s c a) 0≤o t q | yes w≤t with o ≤? (t - w) | (w + o) ≤? t
  ... | yes o≤ | yes _ rewrite sub-sub w≤t o≤ = until-shift s o _ w≤t
  ... | no _   | no _  = refl
  ... | yes o≤ | no ¬h = ⊥-elim (¬h (shift-≤ w≤t o≤))
  ... | no ¬o  | yes h = ⊥-elim (¬o (unshift-≤ w≤t h))

  read-shift : ∀ w {es} → All Pos es → ∀ t q →
               readE ℓ (map (shiftE w) es) t q ≡ back w t (λ u → readE ℓ es u q)
  read-shift w []           t q with w ≤? t
  ... | yes _ = refl
  ... | no _  = refl
  read-shift w {e ∷ es} (p ∷ ps) t q =
    trans (cong₂ merge (read-shift-ev w e p t q) (read-shift w ps t q))
          (sym (back-merge w t (λ u → readEv ℓ e u q) (λ u → readE ℓ es u q)))

  pos-shift : ∀ {w} → 0# ≤ w → ∀ {es} → All Pos es → All Pos (map (shiftE w) es)
  pos-shift 0≤w []                     = []
  pos-shift 0≤w {e ∷ _} (p ∷ ps) = sh e p ∷ pos-shift 0≤w ps
    where sh : ∀ (e : Event L) → Pos e → Pos (shiftE _ e)
          sh (event o s c a) p = ≤-trans (≤-reflexive (sym (+-idˡ 0#))) (+-mono 0≤w p)

  rel-delay : ∀ w {x x′} → Rel x x′ → Rel (delayM w x) (delayT w x′)
  rel-delay w {_ , es} {_ , r} (refl , pa , ra) =
    refl , pos-shift (pos-nonneg w) pa ,
    λ t q → trans (read-shift (pos w) pa t q) (back-cong (pos w) t (λ u → ra u q))

  ---- Hold: the window keeps the events that start inside it
  read-consMb : ∀ m es t q → readE ℓ (consMb m es) t q ≡ merge (readMb ℓ m t q) (readE ℓ es t q)
  read-consMb nothing  es t q = refl
  read-consMb (just e) es t q = refl

  read-clip-ev : ∀ w (e : Event L) → Pos e → ∀ t q →
                 readMb ℓ (clipEv w e) t q ≡ win w t (readEv ℓ e t q)
  read-clip-ev w (event o s c a) 0≤o t q with w ≤? o
  ... | yes w≤o with 0# ≤? t | w ≤? t
  ...   | yes _ | no w≰t with o ≤? t
  ...     | yes o≤t = ⊥-elim (w≰t (≤-trans w≤o o≤t))
  ...     | no _    = refl
  read-clip-ev w (event o s c a) 0≤o t q | yes w≤o | yes _ | yes _ = refl
  read-clip-ev w (event o s c a) 0≤o t q | yes w≤o | no _  | _     = refl
  read-clip-ev w (event o s c a) 0≤o t q | no w≰o with 0# ≤? t
  ... | no 0≰t with o ≤? t
  ...   | yes o≤t = ⊥-elim (0≰t (≤-trans 0≤o o≤t))
  ...   | no _    = refl
  read-clip-ev w (event o s c a) 0≤o t q | no w≰o | yes 0≤t with w ≤? t
  ... | yes w≤t with o ≤? t
  ...   | no _   = refl
  ...   | yes o≤t with (o + cut s (w - o)) ≤? t
  ...     | yes _ = refl
  ...     | no ¬h = ⊥-elim (¬h (≤-trans (≤-trans (+-mono-r o (cut-≤ s (w - o))) (≤-reflexive (sub-add (≰⇒≥ w≰o)))) w≤t))
  read-clip-ev w (event o s c a) 0≤o t q | no w≰o | yes 0≤t | no w≰t with o ≤? t
  ... | no _ = refl
  ... | yes o≤t = until-clip s
    where
      Y = just (ℓ a (param (orElse c q) (t - o)))
      o≤w = ≰⇒≥ w≰o
      until-clip : ∀ s → select ((o + cut s (w - o)) ≤? t) nothing Y ≡ until s o t Y
      until-clip nothing with (o + (w - o)) ≤? t
      ... | yes h = ⊥-elim (w≰t (≤-trans (≤-reflexive (sym (sub-add o≤w))) h))
      ... | no _  = refl
      until-clip (just s₀) with s₀ ≤? (w - o)
      ... | yes _ = refl
      ... | no s₀≰ with (o + (w - o)) ≤? t
      ...   | yes h = ⊥-elim (w≰t (≤-trans (≤-reflexive (sym (sub-add o≤w))) h))
      ...   | no _ with (o + s₀) ≤? t
      ...     | no _ = refl
      ...     | yes h = ⊥-elim (w≰t (≤-trans (≤-reflexive (sym (sub-add o≤w))) (≤-trans (+-mono-r o (≰⇒≥ s₀≰)) h)))

  read-clip : ∀ w {es} → All Pos es → ∀ t q →
              readE ℓ (clipE w es) t q ≡ win w t (readE ℓ es t q)
  read-clip w []           t q with 0# ≤? t
  ... | no _  = refl
  ... | yes _ with w ≤? t
  ...   | yes _ = refl
  ...   | no _  = refl
  read-clip w {e ∷ es} (p ∷ ps) t q =
    trans (read-consMb (clipEv w e) (clipE w es) t q)
      (trans (cong₂ merge (read-clip-ev w e p t q) (read-clip w ps t q))
             (sym (win-merge w t (readEv ℓ e t q) (readE ℓ es t q))))

  pos-clip : ∀ w {es : List (Event L)} → All Pos es → All Pos (clipE w es)
  pos-clip w []                   = []
  pos-clip w {event o s c a ∷ _} (p ∷ ps) with w ≤? o
  ... | yes _ = pos-clip w ps
  ... | no _  = p ∷ pos-clip w ps

  rel-hold : ∀ w {x x′} → Rel x x′ → Rel (holdM w x) (holdT w x′)
  rel-hold w {_ , es} {_ , r} (refl , pa , ra) =
    refl , pos-clip (pos w) pa ,
    λ t q → trans (read-clip (pos w) pa t q) (cong (win (pos w) t) (ra t q))

  ---- Seq and Repeat are derived
  rel-seq : ∀ {x x′ y y′} → Rel x x′ → Rel y y′ → Rel (seqM x y) (seqT x′ y′)
  rel-seq {d , _} {_ , _} {e , _} {_ , _} rx@(refl , _ , _) ry@(refl , _ , _) =
    refl , proj₂ (rel-par (rel-hold d rx) (rel-delay d (rel-hold e ry)))

  rel-rep : ∀ n {x x′} → Rel x x′ → Rel (repM n x) (repT n x′)
  rel-rep zero    rx = refl , [] , λ t q → refl
  rel-rep (suc n) rx = rel-seq rx (rel-rep n rx)

  rel-hom : ∀ o {k k′} → (∀ p → Rel (k p) (k′ p)) → Rel (evH o k) (dirH o k′)
  rel-hom Seq        e = rel-seq (e zero) (e (suc zero))
  rel-hom Par        e = rel-par (e zero) (e (suc zero))
  rel-hom (Hold d)   e = rel-hold d (e tt)
  rel-hom (Delay d)  e = rel-delay d (e tt)
  rel-hom (Repeat n) e = rel-rep n (e tt)
  rel-hom (Drive c)  e = rel-drive c (e tt)

  -- Leaves with arbitrary meanings agree when their meanings do; the fold preserves it.
  agree : ∀ {A : Set} {f : A → Media L} {g : A → Timed} → (∀ a → Rel (f a) (g a)) →
          ∀ s → Rel (media f s) (timed g s)
  agree e = pfold-rel Rel (λ o k k′ r → rel-hom o r) e

-- The key theorem: the events of a scene read pointwise are its direct pointwise semantics.
events-sample : ∀ {A : Set} (ℓ : A → T → X) (s : Scene T D A) →
                proj₁ (mediaOf s) ≡ proj₁ (sample ℓ s) × All Pos (events s) ×
                ∀ t q → readE ℓ (events s) t q ≡ proj₂ (sample ℓ s) t q
events-sample ℓ s = agree ℓ (rel-leaf ℓ) s
