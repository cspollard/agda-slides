{-# OPTIONS --safe --without-K #-}

-- What a shared program means, for every reading of formulas, and that sharing is sound: the
-- theorems listed in the header of `Slides.Anim.Share` (which defines the program and `share`).

module Slides.Anim.Share.Properties where


open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ; suc; _<_; _≤_)
import Data.Nat.Properties as ℕP
import Data.Sum.Properties as SP
import Data.Product.Properties as PP
import Data.Unit.Properties as UP
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary using ()
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Nullary using (yes; no; ¬_; Dec)
import Data.List.Relation.Binary.Lex.Strict as Lex
import Data.Tree.AVL.Map as AVLMap
import Data.Tree.AVL.Map.Membership.Propositional as AVLMem
import Data.Tree.AVL.Map.Membership.Propositional.Properties as AVLMemP

open import Slides.DecEq using ()
open import Slides.Anim.Formula using (Formula; num; var; add; sub; max; pct; hlf; fdiv; fmod; fmul; flt)

open import Slides.Anim.Share
open St

module MM = AVLMem KeyOrder
module MP = AVLMemP KeyOrder

------------------------------------------------------------------------
-- Readings: what a program means

-- A reading of formulas is an algebra for their signature, into a carrier `A` of values, with an
-- embedding of values into the type `B` of what the page sets (for a discrete template, `A = ℕ`
-- and `B = ℚ`, the position being a real half).  `Semantics R` says that a function `sem`
-- from formulas to values is the fold of `R`: one equation per constructor.  The existing
-- readings `⟦_⟧` (ℚ) and `⟦_⟧ᴺ` (ℕ) are instances (`Slides.Anim.SharePhases`).
record Reading (A B : Set) : Set where
  field
    rnum   : ℕ → A
    app1   : Op1 → A → A
    app2   : Op2 → A → A → A
    app4   : A → A → A → A → A
    out    : A → B
    outHlf : A → B

record Semantics {A B : Set} (R : Reading A B) : Set where
  open Reading R
  field
    sem    : Formula → (ℕ → A) → A
    s-num  : ∀ n ρ → sem (num n) ρ ≡ rnum n
    s-var  : ∀ i ρ → sem (var i) ρ ≡ ρ i
    s-add  : ∀ a b ρ → sem (add a b) ρ ≡ app2 oAdd (sem a ρ) (sem b ρ)
    s-sub  : ∀ a b ρ → sem (sub a b) ρ ≡ app2 oSub (sem a ρ) (sem b ρ)
    s-max  : ∀ a b ρ → sem (max a b) ρ ≡ app2 oMax (sem a ρ) (sem b ρ)
    s-pct  : ∀ p a ρ → sem (pct p a) ρ ≡ app1 (oPct p) (sem a ρ)
    s-hlf  : ∀ a ρ → sem (hlf a) ρ ≡ app1 oHlf (sem a ρ)
    s-fdiv : ∀ d a ρ → sem (fdiv d a) ρ ≡ app1 (oDiv d) (sem a ρ)
    s-fmod : ∀ d a ρ → sem (fmod d a) ρ ≡ app1 (oMod d) (sem a ρ)
    s-fmul : ∀ n a ρ → sem (fmul n a) ρ ≡ app1 (oMul n) (sem a ρ)
    s-flt  : ∀ a b x y ρ → sem (flt a b x y) ρ ≡ app4 (sem a ρ) (sem b ρ) (sem x ρ) (sem y ρ)

  -- what an output should be: the root of a coordinate that is a half is read as a half
  refOut : Formula → (ℕ → A) → B
  refOut (hlf a) ρ = outHlf (sem a ρ)
  refOut g       ρ = out (sem g ρ)

------------------------------------------------------------------------
-- The meaning of a program, and its soundness

module Sound {A B : Set} (R : Reading A B) (S : Semantics R) where
  open Reading R
  open Semantics S

  update : (ℕ → A) → ℕ → A → ℕ → A
  update e i v j with j ℕP.≟ i
  ... | yes _ = v
  ... | no  _ = e j

  -- `ρ` the parameters, `e` the values of the definitions
  evalArg : (ℕ → A) → (ℕ → A) → Arg → A
  evalArg ρ e (anum n) = rnum n
  evalArg ρ e (apar i) = ρ i
  evalArg ρ e (aref i) = e i

  evalNode : (ℕ → A) → (ℕ → A) → Node → A
  evalNode ρ e (atom a)       = evalArg ρ e a
  evalNode ρ e (un o a)       = app1 o (evalArg ρ e a)
  evalNode ρ e (bin o a b)    = app2 o (evalArg ρ e a) (evalArg ρ e b)
  evalNode ρ e (quad a b c d) = app4 (evalArg ρ e a) (evalArg ρ e b) (evalArg ρ e c) (evalArg ρ e d)

  -- an output: a half at the root is a real half
  evalOut : (ℕ → A) → (ℕ → A) → Node → B
  evalOut ρ e (un oHlf a) = outHlf (evalArg ρ e a)
  evalOut ρ e nd          = out (evalNode ρ e nd)

  -- the values of the definitions of a store: each is its node at the values of the older ones.
  -- (`defs` has the newest first, so the head is defined last; its number is the length of the
  -- rest.  The page evaluates `program st`, the same list oldest first, in that order.)
  env : (ℕ → A) → List Node → ℕ → A
  env ρ []       = λ _ → rnum 0
  env ρ (d ∷ ds) = update (env ρ ds) (length ds) (evalNode ρ (env ρ ds) d)

  ----------------------------------------------------------------------
  -- Well-formed programs

  WfArg : ℕ → Arg → Set
  WfArg n (anum _) = ⊤
  WfArg n (apar _) = ⊤
  WfArg n (aref i) = i < n

  WfNode : ℕ → Node → Set
  WfNode n (atom a)       = WfArg n a
  WfNode n (un _ a)       = WfArg n a
  WfNode n (bin _ a b)    = WfArg n a × WfArg n b
  WfNode n (quad a b c d) = WfArg n a × WfArg n b × WfArg n c × WfArg n d

  -- every definition refers only to older ones
  data Wf : List Node → Set where
    wf-[] : Wf []
    wf-∷  : ∀ {d ds} → WfNode (length ds) d → Wf ds → Wf (d ∷ ds)

  -- `Ext ds′ ds`: `ds′` is `ds` with newer definitions added
  data Ext : List Node → List Node → Set where
    ext-refl : ∀ {ds} → Ext ds ds
    ext-∷    : ∀ {d ds′ ds} → Ext ds′ ds → Ext (d ∷ ds′) ds

  -- the definition number `i` is `nd`
  data At : List Node → ℕ → Node → Set where
    here  : ∀ {d ds} → At (d ∷ ds) (length ds) d
    there : ∀ {d ds i nd} → At ds i nd → At (d ∷ ds) i nd

  ext-length : ∀ {ds′ ds} → Ext ds′ ds → length ds ≤ length ds′
  ext-length ext-refl   = ℕP.≤-refl
  ext-length (ext-∷ x)  = ℕP.≤-trans (ext-length x) (ℕP.n≤1+n _)

  ext-trans : ∀ {ds₂ ds₁ ds₀} → Ext ds₂ ds₁ → Ext ds₁ ds₀ → Ext ds₂ ds₀
  ext-trans ext-refl    y = y
  ext-trans (ext-∷ x)   y = ext-∷ (ext-trans x y)

  At-lt : ∀ {ds i nd} → At ds i nd → i < length ds
  At-lt here      = ℕP.n<1+n _
  At-lt (there a) = ℕP.m<n⇒m<1+n (At-lt a)

  At-wf : ∀ {ds i nd} → Wf ds → At ds i nd → WfNode i nd
  At-wf (wf-∷ w ws) here      = w
  At-wf (wf-∷ w ws) (there a) = At-wf ws a

  ----------------------------------------------------------------------
  -- Values of old definitions do not change

  update-same : ∀ e i v → update e i v i ≡ v
  update-same e i v with i ℕP.≟ i
  ... | yes _  = refl
  ... | no ¬p  = ⊥-elim (¬p refl)
    where open import Data.Empty using (⊥-elim)

  update-other : ∀ e i v j → j < i → update e i v j ≡ e j
  update-other e i v j j<i with j ℕP.≟ i
  ... | yes p  = ⊥-elim (ℕP.<-irrefl p j<i)
    where open import Data.Empty using (⊥-elim)
  ... | no _   = refl

  env-old : ∀ ρ d ds {j} → j < length ds → env ρ (d ∷ ds) j ≡ env ρ ds j
  env-old ρ d ds j<n = update-other _ _ _ _ j<n

  env-ext : ∀ ρ {ds′ ds j} → Ext ds′ ds → j < length ds → env ρ ds′ j ≡ env ρ ds j
  env-ext ρ ext-refl     j<n = refl
  env-ext ρ (ext-∷ {d} {ds′} x) j<n =
    trans (env-old ρ d ds′ (ℕP.<-≤-trans j<n (ext-length x))) (env-ext ρ x j<n)

  WfArg-mono : ∀ {n m a} → n ≤ m → WfArg n a → WfArg m a
  WfArg-mono {a = anum _} n≤m w = tt
  WfArg-mono {a = apar _} n≤m w = tt
  WfArg-mono {a = aref _} n≤m w = ℕP.<-≤-trans w n≤m

  WfNode-mono : ∀ {n m nd} → n ≤ m → WfNode n nd → WfNode m nd
  WfNode-mono {nd = atom a}       n≤m w = WfArg-mono {a = a} n≤m w
  WfNode-mono {nd = un _ a}       n≤m w = WfArg-mono {a = a} n≤m w
  WfNode-mono {nd = bin _ a b}    n≤m (wa , wb) = WfArg-mono {a = a} n≤m wa , WfArg-mono {a = b} n≤m wb
  WfNode-mono {nd = quad a b c d} n≤m (wa , wb , wc , wd) =
    WfArg-mono {a = a} n≤m wa , WfArg-mono {a = b} n≤m wb , WfArg-mono {a = c} n≤m wc , WfArg-mono {a = d} n≤m wd

  -- values that agree below `n` give the same value to what refers only below `n`
  evalArg-cong : ∀ ρ {e₁ e₂ n} a → (∀ j → j < n → e₁ j ≡ e₂ j) → WfArg n a →
                 evalArg ρ e₁ a ≡ evalArg ρ e₂ a
  evalArg-cong ρ (anum _) h w = refl
  evalArg-cong ρ (apar _) h w = refl
  evalArg-cong ρ (aref i) h w = h i w

  evalNode-cong : ∀ ρ {e₁ e₂ n} nd → (∀ j → j < n → e₁ j ≡ e₂ j) → WfNode n nd →
                  evalNode ρ e₁ nd ≡ evalNode ρ e₂ nd
  evalNode-cong ρ (atom a) h w = evalArg-cong ρ a h w
  evalNode-cong ρ (un o a) h w = cong (app1 o) (evalArg-cong ρ a h w)
  evalNode-cong ρ (bin o a b) h (wa , wb) =
    cong₂ (app2 o) (evalArg-cong ρ a h wa) (evalArg-cong ρ b h wb)
  evalNode-cong ρ (quad a b c d) h (wa , wb , wc , wd) =
    trans (cong (λ x → app4 x _ _ _) (evalArg-cong ρ a h wa))
   (trans (cong (λ x → app4 _ x _ _) (evalArg-cong ρ b h wb))
   (trans (cong (λ x → app4 _ _ x _) (evalArg-cong ρ c h wc))
          (cong (λ x → app4 _ _ _ x) (evalArg-cong ρ d h wd))))

  evalOut-cong : ∀ ρ {e₁ e₂ n} nd → (∀ j → j < n → e₁ j ≡ e₂ j) → WfNode n nd →
                 evalOut ρ e₁ nd ≡ evalOut ρ e₂ nd
  evalOut-cong ρ (atom a)       h w = cong out (evalArg-cong ρ a h w)
  evalOut-cong ρ (un (oPct n) a) h w = cong out (evalNode-cong ρ (un (oPct n) a) h w)
  evalOut-cong ρ (un (oDiv n) a) h w = cong out (evalNode-cong ρ (un (oDiv n) a) h w)
  evalOut-cong ρ (un (oMod n) a) h w = cong out (evalNode-cong ρ (un (oMod n) a) h w)
  evalOut-cong ρ (un (oMul n) a) h w = cong out (evalNode-cong ρ (un (oMul n) a) h w)
  evalOut-cong ρ (un oHlf a)     h w = cong outHlf (evalArg-cong ρ a h w)
  evalOut-cong ρ (bin o a b)    h w = cong out (evalNode-cong ρ (bin o a b) h w)
  evalOut-cong ρ (quad a b c d) h w = cong out (evalNode-cong ρ (quad a b c d) h w)

  -- the same, along an extension of the store
  evalArg-ext : ∀ ρ {ds′ ds} a → Ext ds′ ds → WfArg (length ds) a →
                evalArg ρ (env ρ ds′) a ≡ evalArg ρ (env ρ ds) a
  evalArg-ext ρ a x w = evalArg-cong ρ a (λ j j<n → env-ext ρ x j<n) w

  evalNode-ext : ∀ ρ {ds′ ds} nd → Ext ds′ ds → WfNode (length ds) nd →
                 evalNode ρ (env ρ ds′) nd ≡ evalNode ρ (env ρ ds) nd
  evalNode-ext ρ nd x w = evalNode-cong ρ nd (λ j j<n → env-ext ρ x j<n) w

  evalOut-ext : ∀ ρ {ds′ ds} nd → Ext ds′ ds → WfNode (length ds) nd →
                evalOut ρ (env ρ ds′) nd ≡ evalOut ρ (env ρ ds) nd
  evalOut-ext ρ nd x w = evalOut-cong ρ nd (λ j j<n → env-ext ρ x j<n) w

  -- the unfolding of the DAG: the value of a definition is its node at the values of the older ones
  env-def : ∀ ρ {ds i nd} → Wf ds → At ds i nd → env ρ ds i ≡ evalNode ρ (env ρ ds) nd
  env-def ρ {d ∷ ds} (wf-∷ w ws) here =
    trans (update-same (env ρ ds) (length ds) (evalNode ρ (env ρ ds) d))
          (sym (evalNode-cong ρ d (λ j j<n → env-old ρ d ds j<n) w))
  env-def ρ {d ∷ ds} {i} {nd} (wf-∷ w ws) (there a) =
    trans (env-old ρ d ds (At-lt a))
   (trans (env-def ρ ws a)
          (sym (evalNode-cong ρ nd (λ j j<i → env-old ρ d ds (ℕP.<-trans j<i (At-lt a))) (At-wf ws a))))

  ----------------------------------------------------------------------
  -- The invariant of the store

  record Inv (st : St) : Set where
    field
      size-ok : size st ≡ length (defs st)
      wf      : Wf (defs st)
      -- every entry of the memo names a true definition (the memo is a hint, the entries are
      -- what the hint is checked against)
      memo-ok : ∀ {k nd i} → (k , (nd , i)) MM.∈ₖᵥ memo st → At (defs st) i nd
  open Inv

  Inv-empty : Inv emptySt
  Inv-empty = record
    { size-ok = refl ; wf = wf-[]
    ; memo-ok = λ p → ⊥-elim (MP.∈ₖᵥ-empty p) }
    where open import Data.Empty using (⊥-elim)

  -- an argument that refers below the size refers below the number of definitions
  wfLen : ∀ {st} → Inv st → ∀ {a} → WfArg (size st) a → WfArg (length (defs st)) a
  wfLen {st} I {a} w = subst (λ n → WfArg n a) (size-ok I) w

  wfLenN : ∀ {st} → Inv st → ∀ {nd} → WfNode (size st) nd → WfNode (length (defs st)) nd
  wfLenN {st} I {nd} w = subst (λ n → WfNode n nd) (size-ok I) w

  -- the size grows with the definitions
  size-mono : ∀ {st st′} → Inv st → Inv st′ → Ext (defs st′) (defs st) → size st ≤ size st′
  size-mono {st} {st′} I I′ x =
    subst₂ _≤_ (sym (size-ok I)) (sym (size-ok I′)) (ext-length x)
    where open import Relation.Binary.PropositionalEquality using (subst₂)

  -- defining a node
  record Interned (ρ : ℕ → A) (st : St) (nd : Node) (r : Arg × St) : Set where
    constructor interned
    field
      inv : Inv (proj₂ r)
      ext : Ext (defs (proj₂ r)) (defs st)
      wfr : WfArg (size (proj₂ r)) (proj₁ r)
      -- the reference reads as the node, evaluated against the new definitions
      val : evalArg ρ (env ρ (defs (proj₂ r))) (proj₁ r) ≡ evalNode ρ (env ρ (defs (proj₂ r))) nd

  fresh-ok : ∀ ρ nd st → Inv st → WfNode (size st) nd → Interned ρ st nd (fresh nd st)
  fresh-ok ρ nd st I w = interned inv′ (ext-∷ ext-refl) (ℕP.n<1+n _) val′
    where
      ds = defs st
      sz : size st ≡ length ds
      sz = size-ok I
      wN : WfNode (length ds) nd
      wN = wfLenN I {nd} w
      inv′ : Inv (proj₂ (fresh nd st))
      inv′ = record
        { size-ok = cong suc sz
        ; wf = wf-∷ wN (wf I)
        ; memo-ok = λ {k} {nd″} {i} p → memo-ok′ p }
        where
          memo-ok′ : ∀ {k nd″ i} → (k , (nd″ , i)) MM.∈ₖᵥ memo (proj₂ (fresh nd st)) → At (nd ∷ ds) i nd″
          memo-ok′ p with MP.∈ₖᵥ-insert⁻ p
          ... | inj₁ (_ , refl) = subst (λ n → At (nd ∷ ds) n nd) (sym sz) here
          ... | inj₂ (_ , q)    = there (memo-ok I q)
      val′ : evalArg ρ (env ρ (nd ∷ ds)) (aref (size st)) ≡ evalNode ρ (env ρ (nd ∷ ds)) nd
      val′ =
        trans (cong (env ρ (nd ∷ ds)) sz)
       (trans (update-same (env ρ ds) (length ds) (evalNode ρ (env ρ ds) nd))
              (sym (evalNode-cong ρ nd (λ j j<n → env-old ρ nd ds j<n) wN)))

  intern-ok : ∀ ρ nd st → Inv st → WfNode (size st) nd → Interned ρ st nd (intern nd st)
  intern-ok ρ nd st I w with M.lookup (memo st) (key nd) in eq
  ... | nothing = fresh-ok ρ nd st I w
  ... | just (nd′ , i) with node≟ nd′ nd
  ...   | no _      = fresh-ok ρ nd st I w
  ...   | yes refl  = interned I ext-refl (subst (λ n → i < n) (sym (size-ok I)) (At-lt a)) (env-def ρ (wf I) a)
    where a = memo-ok I (MP.∈ₖᵥ-lookup⁻ eq)

  ----------------------------------------------------------------------
  -- What a computation in the store achieves

  -- `f st` extends the store, and its result reads as the value `v`
  record Result (ρ : ℕ → A) (st : St) (v : A) (r : Arg × St) : Set where
    constructor result
    field
      inv : Inv (proj₂ r)
      ext : Ext (defs (proj₂ r)) (defs st)
      wfr : WfArg (size (proj₂ r)) (proj₁ r)
      val : evalArg ρ (env ρ (defs (proj₂ r))) (proj₁ r) ≡ v

  Impl : (ℕ → A) → A → Sh Arg → Set
  Impl ρ v f = ∀ st → Inv st → Result ρ st v (f st)

  impl-cong : ∀ {ρ v w f} → v ≡ w → Impl ρ v f → Impl ρ w f
  impl-cong refl H = H

  -- a result stays valid at a later store
  later : ∀ {ρ st₁ st₂ a v} → Inv st₁ → Inv st₂ → Ext (defs st₂) (defs st₁) →
          WfArg (size st₁) a → evalArg ρ (env ρ (defs st₁)) a ≡ v →
          WfArg (size st₂) a × evalArg ρ (env ρ (defs st₂)) a ≡ v
  later {ρ} {st₁} {st₂} {a} I₁ I₂ x w val =
    WfArg-mono {a = a} (size-mono I₁ I₂ x) w ,
    trans (evalArg-ext ρ a x (wfLen I₁ {a} w)) val

  un¹-impl : ∀ ρ o {f v} → Impl ρ v f → Impl ρ (app1 o v) (un¹ o f)
  un¹-impl ρ o {f} H st I with H st I
  ... | result I₁ x₁ w₁ val₁ with intern-ok ρ (un o (proj₁ (f st))) (proj₂ (f st)) I₁ w₁
  ...   | interned I′ x′ w′ val′ =
    result I′ (ext-trans x′ x₁) w′
      (trans val′ (cong (app1 o) (trans (evalArg-ext ρ (proj₁ (f st)) x′ (wfLen I₁ w₁)) val₁)))

  bin²-impl : ∀ ρ o {f g v w} → Impl ρ v f → Impl ρ w g → Impl ρ (app2 o v w) (bin² o f g)
  bin²-impl ρ o {f} {g} Hf Hg st I
    with Hf st I
  ... | result I₁ x₁ w₁ val₁
    with Hg (proj₂ (f st)) I₁
  ... | result I₂ x₂ w₂ val₂
    with intern-ok ρ (bin o (proj₁ (f st)) (proj₁ (g (proj₂ (f st))))) (proj₂ (g (proj₂ (f st)))) I₂
                   (WfArg-mono {a = proj₁ (f st)} (size-mono I₁ I₂ x₂) w₁ , w₂)
  ...   | interned I′ x′ w′ val′ =
    result I′ (ext-trans x′ (ext-trans x₂ x₁)) w′
      (trans val′
        (cong₂ (app2 o)
          (trans (evalArg-ext ρ (proj₁ (f st)) (ext-trans x′ x₂) (wfLen I₁ w₁)) val₁)
          (trans (evalArg-ext ρ (proj₁ (g (proj₂ (f st)))) x′ (wfLen I₂ w₂)) val₂)))

  quad⁴-impl : ∀ ρ {f g h k a b c d} → Impl ρ a f → Impl ρ b g → Impl ρ c h → Impl ρ d k →
               Impl ρ (app4 a b c d) (quad⁴ f g h k)
  quad⁴-impl ρ {f} {g} {h} {k} Hf Hg Hh Hk st I
    with Hf st I
  ... | result I₁ x₁ w₁ val₁
    with Hg (proj₂ (f st)) I₁
  ... | result I₂ x₂ w₂ val₂
    with Hh (proj₂ (g (proj₂ (f st)))) I₂
  ... | result I₃ x₃ w₃ val₃
    with Hk (proj₂ (h (proj₂ (g (proj₂ (f st)))))) I₃
  ... | result I₄ x₄ w₄ val₄
    with intern-ok ρ
           (quad (proj₁ (f st)) (proj₁ (g (proj₂ (f st)))) (proj₁ (h (proj₂ (g (proj₂ (f st))))))
                 (proj₁ (k (proj₂ (h (proj₂ (g (proj₂ (f st)))))))))
           (proj₂ (k (proj₂ (h (proj₂ (g (proj₂ (f st))))))))
           I₄
           ( WfArg-mono {a = proj₁ (f st)} (ℕP.≤-trans (size-mono I₁ I₂ x₂) (ℕP.≤-trans (size-mono I₂ I₃ x₃) (size-mono I₃ I₄ x₄))) w₁
           , WfArg-mono {a = proj₁ (g (proj₂ (f st)))} (ℕP.≤-trans (size-mono I₂ I₃ x₃) (size-mono I₃ I₄ x₄)) w₂
           , WfArg-mono {a = proj₁ (h (proj₂ (g (proj₂ (f st)))))} (size-mono I₃ I₄ x₄) w₃
           , w₄ )
  ...   | interned I′ x′ w′ val′ =
    result I′ (ext-trans x′ (ext-trans x₄ (ext-trans x₃ (ext-trans x₂ x₁)))) w′
      (trans val′
        (trans (cong (λ z → app4 z _ _ _)
                 (trans (evalArg-ext ρ (proj₁ (f st)) (ext-trans x′ (ext-trans x₄ (ext-trans x₃ x₂))) (wfLen I₁ w₁)) val₁))
       (trans (cong (λ z → app4 _ z _ _)
                 (trans (evalArg-ext ρ (proj₁ (g (proj₂ (f st)))) (ext-trans x′ (ext-trans x₄ x₃)) (wfLen I₂ w₂)) val₂))
       (trans (cong (λ z → app4 _ _ z _)
                 (trans (evalArg-ext ρ (proj₁ (h (proj₂ (g (proj₂ (f st)))))) (ext-trans x′ x₄) (wfLen I₃ w₃)) val₃))
              (cong (λ z → app4 _ _ _ z)
                 (trans (evalArg-ext ρ (proj₁ (k (proj₂ (h (proj₂ (g (proj₂ (f st)))))))) x′ (wfLen I₄ w₄)) val₄))))))

  -- Sharing a formula gives a reference that reads as the formula.
  share-impl : ∀ g ρ → Impl ρ (sem g ρ) (share g)
  share-impl (num n) ρ st I = result I ext-refl tt (sym (s-num n ρ))
  share-impl (var i) ρ st I = result I ext-refl tt (sym (s-var i ρ))
  share-impl (add a b) ρ =
    impl-cong (sym (s-add a b ρ)) (bin²-impl ρ oAdd (share-impl a ρ) (share-impl b ρ))
  share-impl (sub a b) ρ =
    impl-cong (sym (s-sub a b ρ)) (bin²-impl ρ oSub (share-impl a ρ) (share-impl b ρ))
  share-impl (max a b) ρ =
    impl-cong (sym (s-max a b ρ)) (bin²-impl ρ oMax (share-impl a ρ) (share-impl b ρ))
  share-impl (pct p a) ρ =
    impl-cong (sym (s-pct p a ρ)) (un¹-impl ρ (oPct p) (share-impl a ρ))
  share-impl (hlf a) ρ =
    impl-cong (sym (s-hlf a ρ)) (un¹-impl ρ oHlf (share-impl a ρ))
  share-impl (fdiv d a) ρ =
    impl-cong (sym (s-fdiv d a ρ)) (un¹-impl ρ (oDiv d) (share-impl a ρ))
  share-impl (fmod d a) ρ =
    impl-cong (sym (s-fmod d a ρ)) (un¹-impl ρ (oMod d) (share-impl a ρ))
  share-impl (fmul n a) ρ =
    impl-cong (sym (s-fmul n a ρ)) (un¹-impl ρ (oMul n) (share-impl a ρ))
  share-impl (flt a b x y) ρ =
    impl-cong (sym (s-flt a b x y ρ))
      (quad⁴-impl ρ (share-impl a ρ) (share-impl b ρ) (share-impl x ρ) (share-impl y ρ))

  ----------------------------------------------------------------------
  -- Outputs, and sharing through one store across a structure

  -- the node `nd` is the output of `g`, against the definitions `ds`
  record OutQ (ρ : ℕ → A) (ds : List Node) (g : Formula) (nd : Node) : Set where
    constructor outq
    field
      wfn : WfNode (length ds) nd
      val : evalOut ρ (env ρ ds) nd ≡ refOut g ρ
  open OutQ

  -- A computation `f` *realises* a relation `Q` (between its argument and its result, relative to
  -- the definitions) when it keeps the invariant, extends the store and the relation holds at
  -- the final definitions.  A relation that is `Stable` along extensions chains through a
  -- traversal: the results of the earlier parts stay valid when later ones add definitions.
  Realises : ∀ {X Y : Set} → (List Node → X → Y → Set) → (X → Sh Y) → Set
  Realises Q f = ∀ x st → Inv st →
    Inv (proj₂ (f x st)) × Ext (defs (proj₂ (f x st))) (defs st) × Q (defs (proj₂ (f x st))) x (proj₁ (f x st))

  Stable : ∀ {X Y : Set} → (List Node → X → Y → Set) → Set
  Stable Q = ∀ {ds′ ds x y} → Ext ds′ ds → Q ds x y → Q ds′ x y

  OutQ-stable : ∀ ρ → Stable (OutQ ρ)
  OutQ-stable ρ {ds′} {ds} {g} {nd} x (outq w val) =
    outq (WfNode-mono {nd = nd} (ext-length x) w) (trans (evalOut-ext ρ nd x w) val)

  private
    out-other : ∀ g ρ → refOut g ρ ≡ out (sem g ρ) → ∀ st → Inv st →
      Inv (proj₂ (share g st)) × Ext (defs (proj₂ (share g st))) (defs st)
      × OutQ ρ (defs (proj₂ (share g st))) g (atom (proj₁ (share g st)))
    out-other g ρ rg st I with share-impl g ρ st I
    ... | result I′ x w val =
      I′ , x , outq (wfLen I′ {proj₁ (share g st)} w) (trans (cong out val) (sym rg))

  output-realises : ∀ ρ → Realises (OutQ ρ) output
  output-realises ρ (hlf a) st I with share-impl a ρ st I
  ... | result I′ x w val = I′ , x , outq (wfLen I′ {proj₁ (share a st)} w) (cong outHlf val)
  output-realises ρ (num n)       st I = out-other (num n) ρ refl st I
  output-realises ρ (var i)       st I = out-other (var i) ρ refl st I
  output-realises ρ (add a b)     st I = out-other (add a b) ρ refl st I
  output-realises ρ (sub a b)     st I = out-other (sub a b) ρ refl st I
  output-realises ρ (max a b)     st I = out-other (max a b) ρ refl st I
  output-realises ρ (pct p a)     st I = out-other (pct p a) ρ refl st I
  output-realises ρ (fdiv d a)    st I = out-other (fdiv d a) ρ refl st I
  output-realises ρ (fmod d a)    st I = out-other (fmod d a) ρ refl st I
  output-realises ρ (fmul n a)    st I = out-other (fmul n a) ρ refl st I
  output-realises ρ (flt a b x y) st I = out-other (flt a b x y) ρ refl st I

  -- pointwise, for lists
  data AllQ {X Y : Set} (Q : List Node → X → Y → Set) (ds : List Node) : List X → List Y → Set where
    []  : AllQ Q ds [] []
    _∷_ : ∀ {x y xs ys} → Q ds x y → AllQ Q ds xs ys → AllQ Q ds (x ∷ xs) (y ∷ ys)

  AllQ-stable : ∀ {X Y : Set} {Q : List Node → X → Y → Set} → Stable Q → Stable (AllQ Q)
  AllQ-stable st x []       = []
  AllQ-stable st x (q ∷ qs) = st x q ∷ AllQ-stable st x qs

  traverseL-realises : ∀ {X Y : Set} {Q : List Node → X → Y → Set} {f : X → Sh Y} →
                       Stable Q → Realises Q f → Realises (AllQ Q) (traverseL f)
  traverseL-realises {Q = Q} {f} stb H []       st I = I , ext-refl , []
  traverseL-realises {Q = Q} {f} stb H (x ∷ xs) st I
    with H x st I
  ... | I₁ , x₁ , q₁
    with traverseL-realises stb H xs (proj₂ (f x st)) I₁
  ... | I₂ , x₂ , qs₂ = I₂ , ext-trans x₂ x₁ , stb x₂ q₁ ∷ qs₂

  -- for options
  data MaybeQ {X Y : Set} (Q : List Node → X → Y → Set) (ds : List Node) : Maybe X → Maybe Y → Set where
    nothingQ : MaybeQ Q ds nothing nothing
    justQ    : ∀ {x y} → Q ds x y → MaybeQ Q ds (just x) (just y)

  MaybeQ-stable : ∀ {X Y : Set} {Q : List Node → X → Y → Set} → Stable Q → Stable (MaybeQ Q)
  MaybeQ-stable st x nothingQ  = nothingQ
  MaybeQ-stable st x (justQ q) = justQ (st x q)

  traverseM-realises : ∀ {X Y : Set} {Q : List Node → X → Y → Set} {f : X → Sh Y} →
                       Realises Q f → Realises (MaybeQ Q) (traverseM f)
  traverseM-realises H nothing  st I = I , ext-refl , nothingQ
  traverseM-realises H (just x) st I with H x st I
  ... | I₁ , x₁ , q₁ = I₁ , x₁ , justQ q₁

  ----------------------------------------------------------------------
  -- The unfolding: the tree a program stands for

  -- Substituting the definitions into a reference gives a tree again (`>>=` of the formulas'
  -- free monad: a variable, here a reference, is replaced by the formula it names).  Evaluating
  -- the program is evaluating that tree: `unfold-sound`, the law "evaluation after substitution
  -- is evaluation at the evaluated substitution" (`Slides.Diagram.Expr.evalWith-subst`,
  -- `Slides.Diagram.Euclid.evalD-substD`) for the shipped syntax, proved by `env-def`'s
  -- induction on the store.
  argF : (ℕ → Formula) → Arg → Formula
  argF e (anum n) = num n
  argF e (apar i) = var i
  argF e (aref i) = e i

  nodeF : (ℕ → Formula) → Node → Formula
  nodeF e (atom a)        = argF e a
  nodeF e (un (oPct p) a) = pct p (argF e a)
  nodeF e (un (oDiv d) a) = fdiv d (argF e a)
  nodeF e (un (oMod d) a) = fmod d (argF e a)
  nodeF e (un (oMul n) a) = fmul n (argF e a)
  nodeF e (un oHlf a)     = hlf (argF e a)
  nodeF e (bin oAdd a b)  = add (argF e a) (argF e b)
  nodeF e (bin oSub a b)  = sub (argF e a) (argF e b)
  nodeF e (bin oMax a b)  = max (argF e a) (argF e b)
  nodeF e (quad a b c d)  = flt (argF e a) (argF e b) (argF e c) (argF e d)

  -- the tree of definition `i` of a store (newest first)
  unfold : List Node → ℕ → Formula
  unfold []       i = num 0
  unfold (d ∷ ds) i with i ℕP.≟ length ds
  ... | yes _ = nodeF (unfold ds) d
  ... | no  _ = unfold ds i

  sem-argF : ∀ ρ {e : ℕ → Formula} {e′ : ℕ → A} a → (∀ j → sem (e j) ρ ≡ e′ j) →
             sem (argF e a) ρ ≡ evalArg ρ e′ a
  sem-argF ρ (anum n) h = s-num n ρ
  sem-argF ρ (apar i) h = s-var i ρ
  sem-argF ρ (aref i) h = h i

  sem-nodeF : ∀ ρ {e : ℕ → Formula} {e′ : ℕ → A} nd → (∀ j → sem (e j) ρ ≡ e′ j) →
              sem (nodeF e nd) ρ ≡ evalNode ρ e′ nd
  sem-nodeF ρ (atom a)        h = sem-argF ρ a h
  sem-nodeF ρ (un (oPct p) a) h = trans (s-pct p _ ρ) (cong (app1 (oPct p)) (sem-argF ρ a h))
  sem-nodeF ρ (un (oDiv d) a) h = trans (s-fdiv d _ ρ) (cong (app1 (oDiv d)) (sem-argF ρ a h))
  sem-nodeF ρ (un (oMod d) a) h = trans (s-fmod d _ ρ) (cong (app1 (oMod d)) (sem-argF ρ a h))
  sem-nodeF ρ (un (oMul n) a) h = trans (s-fmul n _ ρ) (cong (app1 (oMul n)) (sem-argF ρ a h))
  sem-nodeF ρ (un oHlf a)     h = trans (s-hlf _ ρ) (cong (app1 oHlf) (sem-argF ρ a h))
  sem-nodeF ρ (bin oAdd a b)  h = trans (s-add _ _ ρ) (cong₂ (app2 oAdd) (sem-argF ρ a h) (sem-argF ρ b h))
  sem-nodeF ρ (bin oSub a b)  h = trans (s-sub _ _ ρ) (cong₂ (app2 oSub) (sem-argF ρ a h) (sem-argF ρ b h))
  sem-nodeF ρ (bin oMax a b)  h = trans (s-max _ _ ρ) (cong₂ (app2 oMax) (sem-argF ρ a h) (sem-argF ρ b h))
  sem-nodeF ρ (quad a b c d)  h =
    trans (s-flt _ _ _ _ ρ)
   (trans (cong (λ z → app4 z _ _ _) (sem-argF ρ a h))
   (trans (cong (λ z → app4 _ z _ _) (sem-argF ρ b h))
   (trans (cong (λ z → app4 _ _ z _) (sem-argF ρ c h))
          (cong (λ z → app4 _ _ _ z) (sem-argF ρ d h)))))

  env-here : ∀ ρ d ds → env ρ (d ∷ ds) (length ds) ≡ evalNode ρ (env ρ ds) d
  env-here ρ d ds = update-same (env ρ ds) (length ds) (evalNode ρ (env ρ ds) d)

  env-there : ∀ ρ d ds i → ¬ (i ≡ length ds) → env ρ (d ∷ ds) i ≡ env ρ ds i
  env-there ρ d ds i ¬p with i ℕP.≟ length ds
  ... | yes q = ⊥-elim (¬p q)
    where open import Data.Empty using (⊥-elim)
  ... | no _  = refl

  unfold-here : ∀ d ds → unfold (d ∷ ds) (length ds) ≡ nodeF (unfold ds) d
  unfold-here d ds with length ds ℕP.≟ length ds
  ... | yes _  = refl
  ... | no ¬p  = ⊥-elim (¬p refl)
    where open import Data.Empty using (⊥-elim)

  unfold-there : ∀ d ds i → ¬ (i ≡ length ds) → unfold (d ∷ ds) i ≡ unfold ds i
  unfold-there d ds i ¬p with i ℕP.≟ length ds
  ... | yes q = ⊥-elim (¬p q)
    where open import Data.Empty using (⊥-elim)
  ... | no _  = refl

  -- the tree of a definition evaluates to the definition's value
  unfold-sound : ∀ ρ ds i → sem (unfold ds i) ρ ≡ env ρ ds i
  unfold-sound ρ []       i = s-num 0 ρ
  unfold-sound ρ (d ∷ ds) i = go (i ℕP.≟ length ds)
    where
      go : Dec (i ≡ length ds) → sem (unfold (d ∷ ds) i) ρ ≡ env ρ (d ∷ ds) i
      go (yes refl) = trans (cong (λ f → sem f ρ) (unfold-here d ds))
                            (trans (sem-nodeF ρ d (unfold-sound ρ ds)) (sym (env-here ρ d ds)))
      go (no ¬p)    = trans (cong (λ f → sem f ρ) (unfold-there d ds i ¬p))
                            (trans (unfold-sound ρ ds i) (sym (env-there ρ d ds i ¬p)))

  -- Sharing a formula and then unfolding the reference gives a tree that means the formula, at
  -- every assignment: the compact form and the tree form evaluate equal.
  share-unfold : ∀ g ρ st → Inv st →
    sem (argF (unfold (defs (proj₂ (share g st)))) (proj₁ (share g st))) ρ ≡ sem g ρ
  share-unfold g ρ st I with share-impl g ρ st I
  ... | result I′ x w val =
    trans (sem-argF ρ (proj₁ (share g st)) (λ j → unfold-sound ρ (defs (proj₂ (share g st))) j)) val
