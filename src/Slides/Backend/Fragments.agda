{-# OPTIONS --safe --without-K #-}

-- Counting fragments on the markup.
--
-- The pages step through every element whose class has the token `fragment`.  `fragCount` counts
-- them as a fold of the XML tree (`foldXMLM`): an element counts for its own class, then its
-- children.  The counts of the smart constructors of `Slides.Backend.HTML` follow from one lemma
-- on `node` (`node-count`): an element is its own class attribute (after the sanitiser has repaired
-- it, `attrHit`) plus its children.
--
--   `classSeen c`   the fragment tokens the page sees in a class string `c`: the sanitiser
--                   (`fixText`) may repair characters, which can join or split words
--   `Quiet attrs`   no attribute of the list contributes a fragment (no class, or one without the token)
--
-- Nothing here depends on the renderer: `Slides.Backend.Render.Properties` applies it.

module Slides.Backend.Fragments where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Char.Base using (Char)
open import Data.List.Base using (List; []; _∷_; _++_; map; length; zip)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.ListAction using (sum)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String; toList; fromList)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
import Data.List.Properties as ListP
import Data.Nat.Properties as ℕP
open import Function.Base using (_∘_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
import Data.Char.Properties as Char

open import Data.XML.Valid using (hasKey)
open import Data.XML.AST using (textSlots; XMLDoc; foldXMLM; node; Attributes; parentList; mixed; fromContent; leaf)
open import Data.XML.Sanitize using (fixAttrs; fixAttribute; insertAttr; fixName; element; textElement)
open import Data.Sanitize using (fixText)
import Data.Container.Table as Tbl
open import Data.Container.Pos using (noPos; Pos; castP; castP-id)
open import Data.Container.List using (tabulate; length-tabulate; tabulate-map; tabulate-table; tabulate-cong)

open import Slides.Deck.Steps using (fragClass)
open import Slides.Backend.HTML using (Attrs; hText; hElement; hMixed; padText; isVoid)

-- Fragments on the tree

classKey : List Char → Bool
classKey k = ⌊ ListP.≡-dec Char._≟_ k (toList "class") ⌋

-- the fragment tokens of the class attribute, the first `class` winning
classHit : Attributes → ℕ
classHit []             = 0
classHit ((k , v) ∷ as) = if classKey k then fragClass (fromList v) else classHit as

fragCount : XMLDoc → ℕ
fragCount = foldXMLM (λ ()) (λ _ attrs cs → classHit attrs + sum (map proj₁ (proj₂ cs)))

forestCount : List XMLDoc → ℕ
forestCount = sum ∘ map fragCount

forestCount-++ : ∀ xs ys → forestCount (xs ++ ys) ≡ forestCount xs + forestCount ys
forestCount-++ []       ys = refl
forestCount-++ (x ∷ xs) ys = trans (cong (fragCount x +_) (forestCount-++ xs ys)) (sym (ℕP.+-assoc (fragCount x) _ _))

forestCount-map₀ : ∀ {A : Set} (f : A → XMLDoc) (xs : List A) → (∀ x → fragCount (f x) ≡ 0) → forestCount (map f xs) ≡ 0
forestCount-map₀ f []       h = refl
forestCount-map₀ f (x ∷ xs) h = trans (cong₂ _+_ (h x) (forestCount-map₀ f xs h)) refl

-- Nodes: the children of a node, listed in order, with the text slots dropped
private
  zip-sum : ∀ (L : List ℕ) {T : List (List Char)} → length L ≡ length T → sum (map proj₁ (zip L T)) ≡ sum L
  zip-sum []       {[]}    e = refl
  zip-sum (x ∷ L)  {_ ∷ T} e = cong (x +_) (zip-sum L (ℕP.suc-injective e))

  mixed-sum : ∀ n (texts : Vec (List Char) (suc n)) (f : Pos n → ℕ) → sum (map proj₁ (proj₂ (mixed n texts f))) ≡ sum (tabulate n f)
  mixed-sum n texts f = zip-sum (tabulate n f) (trans (length-tabulate n f) (sym (VecP.length-toList (Vec.tail texts))))

  -- reading the positions through a cast is reading them
  tabulate-cast : ∀ {A : Set} {n m} (e : n ≡ m) (f : Pos m → A) → tabulate n (f ∘ castP e) ≡ tabulate m f
  tabulate-cast {n = n} refl f = tabulate-cong n _ f (λ p → cong f (castP-id refl p))

-- stated of any document `d` that is the node, so that its validity proofs are found by unification
node-count : ∀ {d tag attrs n} {texts : Vec (List Char) (suc n)} {f : Pos n → XMLDoc} {pt pa px} →
             d ≡ node tag attrs texts f {pt} {pa} {px} →
             fragCount d ≡ classHit attrs + sum (tabulate n (fragCount ∘ f))
node-count {attrs = attrs} {n} {texts} {f} refl = cong (classHit attrs +_) (mixed-sum n texts (fragCount ∘ f))

-- the children listed from a table are the list
table-count : ∀ {A : Set} (g : A → ℕ) (xs : List A) {n} (e : n ≡ length xs) →
              sum (tabulate n (g ∘ Tbl.table xs ∘ castP e)) ≡ sum (map g xs)
table-count g xs {n} e =
  cong sum (trans (tabulate-cong n _ (g ∘ Tbl.table xs ∘ castP e) (λ p → refl))
            (trans (tabulate-cast e (g ∘ Tbl.table xs))
              (trans (tabulate-map _ (Tbl.table xs) g) (cong (map g) (tabulate-table xs)))))

-- Attributes: the page sees the sanitised list
chars : Attrs → Attributes
chars = map (λ { (k , v) → toList k , toList v })

attrHit : Attrs → ℕ
attrHit as = classHit (fixAttrs (chars as))

-- the fragment tokens of a class string, as the page sees it
classSeen : String → ℕ
classSeen c = attrHit (("class" , c) ∷ [])

classSeen-def : ∀ c → classSeen c ≡ fragClass (fromList (fixText (toList c)))
classSeen-def c = refl

-- an attribute list whose class (if any) has no fragment token
Quiet : Attrs → Set
Quiet = All (λ a → attrHit (a ∷ []) ≡ 0)

-- an attribute inserted into a list with no fragment adds none
private
  pick : ∀ b {x y} → (if b then x else 0) ≡ 0 → y ≡ 0 → (if b then x else y) ≡ 0
  pick true  h _ = h
  pick false _ a = a

  insert-hit : ∀ k v acc → classHit ((k , v) ∷ []) ≡ 0 → classHit acc ≡ 0 → classHit (insertAttr (k , v) acc) ≡ 0
  insert-hit k v acc h a = go (hasKey k acc)
    where go : ∀ b → classHit (if b then acc else (k , v) ∷ acc) ≡ 0
          go true  = a
          go false = pick (classKey k) h a

quiet-hit : ∀ as → Quiet as → attrHit as ≡ 0
quiet-hit []       []       = refl
quiet-hit (a ∷ as) (h ∷ hs) = insert-hit _ _ (fixAttrs (chars as)) h (quiet-hit as hs)

-- the constructors of `Slides.Backend.HTML`: an element is its class plus its children
element-count : ∀ tag attrs cs → fragCount (element tag attrs cs) ≡ attrHit attrs + forestCount cs
element-count tag attrs cs =
  trans (cong (attrHit attrs +_) (mixed-sum (length cs) (Vec.replicate (suc (length cs)) []) (fragCount ∘ Tbl.table cs)))
        (cong (attrHit attrs +_) (table-count fragCount cs refl))

textElement-count : ∀ tag attrs t → fragCount (textElement tag attrs t) ≡ attrHit attrs
textElement-count tag attrs t =
  trans (node-count {d = textElement tag attrs t} refl) (ℕP.+-identityʳ _)

hText-count : ∀ tag attrs t → fragCount (hText tag attrs t) ≡ attrHit attrs
hText-count tag attrs t = textElement-count tag attrs (padText t)

hElement-count : ∀ tag attrs cs → fragCount (hElement tag attrs cs) ≡ attrHit attrs + forestCount cs
hElement-count tag attrs []       with isVoid tag
... | true  = element-count tag attrs []
... | false = trans (textElement-count tag attrs " ") (sym (ℕP.+-identityʳ _))
hElement-count tag attrs (c ∷ cs) = element-count tag attrs (c ∷ cs)

-- mixed content: the children are the elements between the text slots
hMixed-count : ∀ tag attrs t (cs : List (XMLDoc × String)) →
               fragCount (hMixed tag attrs (t , cs)) ≡ attrHit attrs + forestCount (map proj₁ cs)
hMixed-count tag attrs t []          = trans (hText-count tag attrs t) (sym (ℕP.+-identityʳ _))
hMixed-count tag attrs t (c ∷ cs)    =
  trans (node-count {d = hMixed tag attrs (t , c ∷ cs)} refl)
        (cong (attrHit attrs +_) (trans (table-count fragCount (map proj₁ cs′) (sym (ListP.length-map proj₁ cs′)))
                                        (cong sum (cong (map fragCount) (sym (ListP.map-∘ (c ∷ cs)))))))
  where cs′ = map (λ { (x , s) → x , toList s }) (c ∷ cs)
