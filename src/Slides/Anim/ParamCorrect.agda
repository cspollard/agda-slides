{-# OPTIONS --safe --without-K #-}

-- The assembly of whole frames, continuous templates: the symbolic frames of `Slides.Anim.Param`
-- are the frames of the animation (the discrete frames, `layout_ℕ`, of `timeline atop (frames
-- natOps) a`).  `Slides.Anim.LeafAssembly` proves it for any language of template numbers; this
-- module is the instance for `Expr` (`Slides.Anim.DParamCorrect` is the one for `DExpr`):
--
--     layout_ℕ (frame k of  timeline atop (frames natOps) a)
--       ≡  mapLayout (eval ρ) (layout_Expr (symbolic frame k))
--
-- for every tick `k < dur a` of an animation of templates (every segment `template`, so that
-- `Slides.Anim.Param.leaves` succeeds) and every assignment `ρ` such that every leaf running at
-- tick `k` has `ρ (idx) ≡ units (sample of its track at that tick)` (`GoodL l k ρ`).  The right-hand
-- side is exactly what the page computes (evaluate the symbolic layout at the parameters), and the
-- left is the existing discrete frame.
--
--   * `discrete-assembly` (`assembly`): the statement, tick by tick; `leaves-agree` for all ticks
--     at once; `discrete-assembly-canonical` with the assignment named.
--   * `paramOf-assembly`: for the animation `render` ships (`paramOf acts`), against the frames
--     `render` shows (`concat (map (timeline atop (frames natOps)) acts)`).
--
-- What is specific to continuous templates is one segment (`leaf-agrees`: laying the renamed
-- template out symbolically and evaluating it is laying out the template at the segment's own
-- parameter, `Slides.Diagram.LayoutNatural.layout-subst`), that `atop` is natural along `eval`
-- (`atop-natural`), and the statement for what `render` ships.

module Slides.Anim.ParamCorrect where

open import Data.Bool using (true; if_then_else_; _∧_; T)
open import Data.List using ([]; _∷_; _++_; length; replicate; map; concat)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat as ℕ using (ℕ; _+_; _∸_; _<ᵇ_; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
import Data.List.Properties as LP
open import Data.Unit using ()
open import Data.Fin using ()
open import Data.Container.FreeMonad using (_⋆_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Slides.Diagram.Draw using (Layout; mapLayout)
open import Slides.Diagram.Syntax using (Dia; atop; mapDia)
open import Slides.Diagram.Expr using (Expr; exprOps; eval; eval-hom; var)
open import Slides.Diagram.Layout using (module LayoutWith)
open import Slides.Diagram.Scalar using (natOps)
open import Slides.Diagram.LayoutNatural using (layout-subst; layout-eval; atop-natural)
import Slides.Anim.Track as T
open import Slides.Anim.Syntax
open import Slides.Anim.Timeline using (timeline; frames; length-dur)
open import Slides.Anim.Param
import Slides.Diagram.Param as DP
open import Slides.Anim.Nth public
import Slides.Anim.LeafAssembly as LA

private
  layoutℕ : Dia ℕ → Layout ℕ
  layoutℕ = LayoutWith.layout natOps

  layoutE : Dia (Expr ℕ) → Layout (Expr ℕ)
  layoutE = LayoutWith.layout exprOps

------------------------------------------------------------------------
-- One segment

-- Laying a segment's renamed template out symbolically and evaluating it at an assignment
-- is laying out the template at the segment's own parameter there.
leaf-agrees : ∀ (l : Leaf Expr) (ρ : ℕ → ℕ) →
  LayoutWith.layout natOps (mapDia (eval ρ) (instantiate l))
  ≡ LayoutWith.layout natOps (mapDia (eval (λ _ → ρ (Leaf.idx l))) (Leaf.tmpl l))
leaf-agrees l ρ = layout-subst (λ _ → var (Leaf.idx l)) ρ (Leaf.tmpl l)

-- the symbolic frames are over `Expr`: a frame is interpreted by evaluating its layout, and
-- `atop` is interpreted as `atop` because layout is natural along evaluation
open LA.Over Expr (λ y ρ → mapLayout (eval ρ) (layoutE y))
  (λ x y ρ → sym (atop-natural exprOps natOps (eval ρ) (eval-hom ρ) (layoutE x) (layoutE y)))
  (λ r d → mapDia (eval (λ _ → r)) d) instantiate
  (λ l ρ → trans (layout-eval ρ (instantiate l)) (leaf-agrees l ρ))
  public

------------------------------------------------------------------------
-- The whole animation

-- only `template` segments are leaves (`discrete` ones are `Slides.Anim.DParam`'s)
private
  leafOf-idx : ∀ i t₀ s l → leafOf i t₀ s ≡ just l → Leaf.idx l ≡ i
  leafOf-idx i t₀ (seg tr (template d)) _ refl = refl
  leafOf-idx i t₀ (seg tr (blackBox f)) _ ()
  leafOf-idx i t₀ (seg tr (discrete d)) _ ()

  leafAgree : ∀ i t₀ s l → leafOf i t₀ s ≡ just l →
              Agree (LeafGood l) t₀ (frames natOps s) (replicate (T.dur (Leaf.track l)) (instantiate l))
  leafAgree i t₀ (seg tr (template d)) _ refl = leaf-Agree (template d) i t₀ tr d (λ q → refl)
  leafAgree i t₀ (seg tr (blackBox f)) _ ()
  leafAgree i t₀ (seg tr (discrete d)) _ ()

open Induction leafOf leafOf-idx leafAgree public

-- Statement (A) of the header, under its old name.
discrete-assembly = assembly
discrete-assembly-canonical = assembly-canonical

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
    in go (seqAll-timeline acts ea) (assembly a i′ l el k hk″ ρ g)
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
