# Review: categorical semantics, containers over Setoids, consolidation

Reviewed on 2026-10-31 at `e457b30` (about 15 700 lines in `src/`).  The `Container.*` layer was
read in full.  The other layers were read with module-level evidence, and the findings that
matter most were spot-checked.  Line references are to that commit.  Deletion estimates are rough.

Design and rules: `docs/Objects.md`, `docs/Contributing.md`.  This file says where the code
falls short of them and proposes an order of work.  Nothing here has been typechecked yet.


## 1. Verdict

The design in `Objects.md` is the right one: signatures as containers, meanings as folds,
relations as lowerings and homomorphisms.  The code does not yet follow it.

**There are two `Container` layers, and the languages use only the weaker one.**

- The **categorical layer** is clean and correct.  It contains:
  - `Poly` (a functor on Setoids)
  - `Free` / `FreeMonad` (a monad on Setoids)
  - `Alg.fold` with `fold-unique` (the free algebra)
  - `Free⊣Forget` and its monadicity
  - `Containers` / `Lowerings` (categories) and `PolyFunctor` / `EmbedFunctor`
  - `Initiality` with Lambek's lemma

  No module under `Slides.*` imports any of it.  `Container.Category`,
  `Container.FreeMonad.Properties.Monadic`, `Container.Interpret.Properties` and
  `Container.Lowering.Translate` are imported by nothing at all.

- The **working layer** is `Container.Interpret.Plain`.  It has:
  - curried `Handler`s on plain `Set`s, with a separate `Congruent` side condition
  - `pfold`, with its own induction for every law (`pfold-ext`, `pfold-cong`, `pfold-bind`,
    `pfold-hom`, `pfold-rel`, `pfold-translate`)

  It meets the categorical layer once, in `pfold-agrees`.  Almost every handler in `Slides` is
  congruent for `≡P.setoid`, so the Setoid structure does no work.

- **Beyond the containers, most of the code is ad hoc.**
  - **Data types.** `Block`, `Inline`, `Math`, `Mark`, `Draw` and `Share.Tree` are plain
    `data`.
  - **Recursion.** Most backends and plot functions are hand-written recursion; nothing under
    `Backend/**` or `Plot/**` calls `pfold`.
  - **Proofs.** Several laws are proved again by induction in each language, when they are
    instances of `translate-*`, `lower-*` or `pfold-*`.  Examples: `mapDia-id/∘`,
    `mapScene-id/∘`, `skip-inject`, `lower-inject`, `lowerFlow-id/fuse`, `duration-nonneg`,
    `lower-supported/sound`.

**The direction of this review:** make the Setoid / F-algebra layer the only API, and derive
every law from one universal property.  The universal properties needed are the free algebra
(`fold-unique`), the free monad on a container, and the coproduct of containers.  Then move
each language onto it.

The three layer reviews together found **≈1100 deletable lines**.  Moving `Block`, `Inline`,
`Math` and `Mark` to containers, and stating the missing structure, adds about 150.


## 2. The `Container` core: one spine instead of two

### 2.1 Duplicates inside `Container.*`

**Folds and translations defined more than once:**

| What | Copies | Keep |
|---|---|---|
| fold | `Alg.fold` (`FreeMonad/Algebraic.agda:78`), `pfold` (`Interpret/Plain.agda:41`), stdlib `Data.Container.FreeMonad.foldr` | one fold, defined via stdlib `foldr`; see 2.2 |
| translate | `Container.Lowering.translate` (`Lowering.agda:60`) and `Container.Interpret.Translate.translate` (`Interpret.agda:26`) | one, *defined* as `lower ∘ embed`; delete `Container.Interpret` |
| pullback | `Interpret/Properties.agda:91` (along `⇒`) and `Lowering/Properties.agda:139` (along a lowering) | the lowering one; the morphism case is `embed` |
| fusion | `Interpret.Properties.Translate.fusion`, `Lowering.Properties.Fusion.lower-fusion`, `Plain.pfold-translate`, `Plain.pfold-hom` | one fusion law (2.2) |
| fold-ext | `Lowering.Properties.FoldLemmas.fold-ext`, `Plain.pfold-ext` | follows from `fold-cong` with a `Func` on leaves |
| copair | `Container.Sum.copair` (on `Func` algebras) and `Slides.Scalar.Core._⊕_` (on handlers), with no lemma relating them | one copair (2.4) |
| fmap | `Container.FreeMonad.fmap` and stdlib `_<$>_` | stdlib |

**Equalities that are wrappers or near-duplicates:**

- The relations themselves: `Eq` (`FreeMonad.agda:34`), `_≈⋆_` (`Lowering.agda:34`),
  `_≈ˡ_` (`Lowering/Properties.agda:73`) and `_≈ᶜ_` (`Category.agda:37`).
- The lemmas over them: `refl≈`, `sym≈`, `trans≈`, `bind-cong≈`, `bind-pure≈` and
  `bind-assoc≈` only re-export the `Eq` lemmas at `≡.setoid`.
- **Recommendation:** keep `Eq`.  Write `t ≈⋆ u` as `Setoid._≈_ (Free₀ C (≡.setoid X))`, and
  use `Relation.Binary.Reasoning.Setoid` instead of the wrappers.

**Hand-rolled copies of stdlib:**

- `Poly₀` / `poly-isEquivalence` (`Polynomial.agda:32-53`) is
  `Data.Container.Relation.Binary.Equality.Setoid.setoid`.  That module's `Eq`, `refl`, `sym`
  and `trans` come from `Data.Container.Relation.Binary.Pointwise.Properties`.  Delete about 25
  lines.
- `Container.Pick` (`pick2`, `pick4`) is `Data.Vec.lookup (a ∷ b ∷ [])`.  Alternatively, use
  `Data.Fin` patterns at each use.

### 2.2 Derive the laws from initiality, not from five inductions

Every law in `Lowering.Properties`, `Lowering.Translate`, `Interpret.Plain`,
`Interpret.Properties` and `FreeMonad.Algebraic.Properties` is an instance of one of these
three:

1. **`fold-unique`** (already proved).  An algebra map out of the free algebra is determined by
   its restriction along `pure`.
2. **Fusion** (Malcolm 1990; Bird and de Moor, *Algebra of Programming*, ch. 3; Hinze, *Adjoint
   folds and unfolds*, 2013).  Let `h : A → B` be an algebra morphism.  Then
   `h ∘ fold A f ≈ fold B (h ∘ f)`.  This is `fold-unique` applied to the composite.  The
   `fold-hom` (`Interpret/Properties.agda:73`) is this law, proved by induction.
3. **Precomposition with a lowering.**  `fold B f ∘ lower l ≈ fold (l^* B) f`, where
   `l^* B` is the pulled-back algebra.  This is fusion with the algebra morphism
   `lower l : FreeAlg_C X → l^* (FreeAlg_D X)`.

Then:

- `bind` is `fold (FreeAlg Y) f`, so the monad laws become instances of fusion.
- `lower l` is `fold (l^* (FreeAlg_D X)) pure`, and `translate m` is `lower (embed m)`.
- `lower-bind`, `lower-ret`, `lower-⋙`, `lower-embed` and `translate-id/∘` follow from
  uniqueness.
- `fold-bind`, `fold-pure` and `fold-action` (in `Algebraic.Properties` and `Monadic`) follow
  in the same way.

**Proposed module layout:**

```
Container.Core         Poly (stdlib setoid), Free₀, Eq, fold, fold-cong, fold-unique, fusion
Container.Monad        Free, FreeMonad, defined as adjoint⇒monad Free⊣Forget; bind := fold
Container.Lowering     Lowering, lower := fold, ret, ⋙, embed, translate := lower ∘ embed, copairL
Container.Sum          copair (one), universal property, Alg(C₁ ⊎ C₂) ≅ Alg C₁ ×_A Alg C₂
Container.Category     Containers, Lowerings ≅ Kleisli (theory only)
```

What this changes:

- **The tree monad is built once.**  `FreeMonad` (direct) and `AdjMonad` (via the adjunction)
  are the same monad built twice, and `Algebraic.Properties` (101 lines) exists only to prove
  that.  Keep the adjunction version (it comes from agda-categories), or keep the direct one
  and delete `Agreement`.  Either way, delete one of the two.
- **`Interpret.Plain` stays only as a thin interface.**  A `Handler` with a `Congruent` proof
  *is* an F-algebra on a setoid: `toAlgebra` already says so.  Let `pfold` be `fold ∘ toAlgebra`
  and keep the curried syntax for authors.  Derive `pfold-rel` (a logical relation) from fold
  on the algebra of relations, i.e. the algebra on `Σ A B R`: the "banana split" product of
  algebras.
- **Estimate:** −350 to −450 lines in `Container.*`, about 40 % of it.

### 2.3 Lowerings are the Kleisli category of the free monad *on containers*

The current `Lowerings` category (`Lowering/Category.agda`) is built by hand.  The standard
structure is as follows:

- **Lowerings are container morphisms.**  The free monad of a container is itself a container,
  `D* = (D ⋆ ⊤) ▷ Leaves` (Abbott, Altenkirch and Ghani, *Containers*, §6; Gambino and Kock,
  *Polynomial functors and polynomial monads*).  So `Lowering C D ≅ C ⇒ D*`.
- **`(−)*` is a monad on `Containers`**, and `Lowerings` is its Kleisli category.  This can use
  `Categories.Category.Construction.Kleisli`.
- **`EmbedFunctor` is the Kleisli inclusion.**  `ret` is the unit and `_⋙_` is Kleisli
  composition.
- **By Yoneda, a lowering is the same data as two other things.**  A natural transformation
  `⟦C⟧ ⇒ D⋆`, and a *monad* morphism `C⋆ ⇒ D⋆`.  The second is the universal property of the
  free monad, and `lower-bind` is half of it.  Stating this one theorem replaces
  `lower-bind`, `lower-ret` and `lower-⋙` as separate facts.
- **Missing classical theorem:** `PolyFunctor` is full and faithful (Abbott et al., Thm 3.4).
  It would justify the definition of `_≈ᶜ_` by quantifying over all setoids, the trick
  `embed-resp` uses.  Otherwise, define `_≈ᶜ_` directly (equal shapes, transported positions)
  and drop the `Set₁` level.

### 2.4 Sums

- **Container sums give coproducts of free monads.**  Free monads of a sum are coproducts of
  free monads (Hyland, Plotkin and Power, *Combining effects: sum and tensor*, 2006; Swierstra,
  *Data types à la carte*).  `Alg (C₁ ⊎ C₂)` on a carrier `A` is the product of
  `Alg C₁` and `Alg C₂` on `A`.  State that as an equivalence of categories.  `copair-unique`
  is half of it today.
- **Add `copairL : Lowering C₁ E → Lowering C₂ E → Lowering (C₁ ⊎ C₂) E`.**  Four places
  hand-write `inj₁ a ↦ impure (a , pure)`, which is `ret`:
  - `Diagram/Curve.agda:114` (`lowerCurve`)
  - `Program/Syntax.agda:50` (`skipOp`)
  - `Program/Supports.agda:62-71` (`lowerOp`, `skipUOp`)
- **Keep one copair.**  `_⊕_` (`Scalar/Core.agda:113`) belongs here, as the handler form of
  `copair`.  Use it for the backends' command sets as well: `RCmd = Nav ⊎ Aux` with a hand
  copair `method` (`Backend/Input.agda:128`, `Reveal.agda:126`).

### 2.5 Levels

Universe levels are handled inconsistently across `Container.*`:

| Module | Levels |
|---|---|
| `Polynomial`, `FreeMonad` | polymorphic |
| `Alg c ℓ C` | absorbs the container's levels, `c′ = c ⊔ s ⊔ p` |
| `Category`, `Lowering.Category`, `Fusion` | fixed at `0ℓ` |
| `pfold-agrees` | `Alg 0ℓ 0ℓ` with a setoid at `s ⊔ p` |

Every client is at `0ℓ`, and so are both `Slides` setoids (`Program/Sem.agda` and
`Program/Machine.agda`).  Pick one of these:

- **Recommended:** fix `0ℓ` everywhere, with one `Container₀`.  This removes most of the
  `{c′ ℓ′}` plumbing.
- Keep the levels polymorphic everywhere.

### 2.6 What to keep

**Keep shapes as `Set` and compare them with `≡`.**  Setoid-shaped ("quotient") containers
(Abbott, Altenkirch, Ghani and McBride, *Constructing polymorphic programs with quotient
types*) would cost a lot, and no signature here needs a quotient on shapes.  Say this in
`Polynomial.agda` so the choice reads as deliberate.

**Keep `Eq` defined by recursion.**  The level argument is sound.


## 3. Theories (Scalar): one presentation, not two

### 3.1 Each theory is stated twice

Each theory is given once as a record of operations and laws (`OrdMon`, `Sub`, `Space`,
`Scale`, the Time and Coupling records).  It is given again as a signature with a handler:
`SpaceC` / `spaceH`, `TimeC`, `CouplingC`.

Categorically, a model is an algebra of the signature that satisfies the equations.  That is,
it is an Eilenberg–Moore algebra of the monad of the theory (Hyland and Power, *The
category-theoretic understanding of universal algebra*, 2007).  agda-categories has
`LawvereTheories` if this is ever wanted.

**Recommendation:** derive the handler from the record (`spaceH M = λ { Plus k → k 0 + k 1 ; … }`),
as is done today.  But state once that a record *is* an algebra of `SpaceC` whose equations hold,
and state `IsOrdMonHom` as "an algebra morphism that reflects order".

### 3.2 Use stdlib structures

Replace the record fields of `OrdMon` (`Scalar/Core.agda:16-40`) with stdlib structures:

- **Monoid part:** `Algebra.Structures.IsCommutativeMonoid`, plus a cancellativity field.
- **Order:** `Relation.Binary.Structures.IsDecTotalOrder`.
- **Join:** `Algebra.Lattice.Structures.IsSemilattice` for `_⊔_`.  Alternatively, derive `_⊔_`
  from decidability.
- **`IsOrdMonHom`** (`:74`): `Algebra.Morphism.Structures.IsMonoidHomomorphism` together with
  `Relation.Binary.Morphism.Structures.IsOrderMonomorphism`.

What this gains:

- **Lemmas come from the library.**  `+-idʳ`, `⊔-≤`, `⊔-≥` and `sub-unique` come from
  `Algebra.Properties.CommutativeMonoid` and `Relation.Binary.Lattice` / `Algebra.Lattice`
  properties.
- **Scattered duplicates disappear.**  `⊔-comm`/`⊔-assoc` (`Diagram/Laws.agda:95-101`),
  `dbl-+`/`sub-trans` (`Diagram/Assoc.agda:32-42`), and the two `≤-reflexive` (`Valid.agda:48`,
  `Scene/Arith.agda:18`) go away.
- **It is the natural step to the planned setoid equality** (`plans/Rationals.md`).  The stdlib
  structures are already relative to an `_≈_`.  Do this first, so the setoid change is a change
  of `_≈_` rather than a rewrite.


## 4. Diagram: scalar-parametric signature as a functor

### 4.1 The signature is a functor `Set → Containers`

`DiagramC : Set → Container` (`Diagram/Syntax.agda:91`) puts the scalar in the shapes, and
`mapC` is a functor `Sets → Containers`.  But `arity` matches on whole constructors.  As a
result, `mapC`'s `position` takes 17 clauses (`:126-143`).  The same 17-way split is repeated
in:

- `layoutCong`, `usageCong` / `same`, `okOp`, `clean` and `soundness`
- `mapDia-id/∘` (`Functoriality.agda:34-72`)
- `usage-mapDia` (`Names.agda:70-112`)

**Recommendation:**

- **Split the tag from the payload.**  Write `Op S = Σ Tag (λ t → Payload t S)` with
  `arity : Tag → Set`.
- **Translation becomes generic.**  `mapC f` then has `position = id`, `mapDia f` is
  `translate (mapC f)`, and `mapDia-id/∘` are `translate-id/∘` plus a one-line `Payload`
  functor law.
- **State the functor itself:** `DiagramC` as a `Functor (Sets 0ℓ) Containers`, and `Dia` as
  `PolyFunctor ∘ DiagramC` (initial algebras).
- **Usage drops the scalar.**  `usage` should be defined on `DiagramC ⊤`, and every scalar
  instance reaches it by `translate` with `pfold-translate`.
- **Estimate:** about −120 lines.

### 4.2 Layout naturality as a natural transformation

`layout-natural` (`Natural.agda:335`) says "`layout` is natural in the scalar", but it is not
stated as a natural transformation.

- **The category:** ordered monoids and order embeddings (from §3.2).
- **The functors:** `Dia, Layout : OrdMonEmb ⟶ Setoids`.
- **The statement:** `layout : NaturalTransformation Dia Layout`, using
  `Categories.NaturalTransformation`.  `mapLayout-id/∘` (`Functoriality.agda:98-123`) become the
  `Functor` fields.
- **`layout-natural-ok`** (`:299-307`) should be `pfold-rel-translate`, as `layout-natural`
  already is.  To get there, define `OkDia` as a fold into `Set`, as `Valid` is.

### 4.3 Size, layout and the monoids behind them (Yorgey)

**Size is a fold into an envelope monoid.**

- `sizeH` (`Laws.agda:47-64`) is a homomorphism into product monoids, which
  `Algebra.Construct.DirectProduct` provides:
  - for `beside`, from `(Dia, beside)` into `(S,+) × (S,⊔)`
  - for `above`, into `(S,⊔) × (S,+)`
- From that, `size-*-assoc/comm` (`:114-125`) follow from the monoid laws.
- `size-layout` (`:70`) is fusion: `frame` is an algebra morphism from the layout algebra to
  the size algebra.

**Layout is a monoid with an action of translations.**

- `Layout` is acted on by `(S×S, +)`.  `shift-zero` / `shift-shift` (`Laws.agda:166-211`) are
  the action laws, and `combine` is "act, then concatenate", a semidirect product.
- State this as an action record once.  `Assoc.Shapes` (`Assoc.agda:62-79`) and about 60 lines
  of `assoc-shape` plumbing then become one lemma about `combine`.
- `names-*` (`Names/Soundness.agda:69-97`), the per-connective geometry in
  `Natural.agda:197-220`, and `Laws.agda:83-87` respell the offsets of `combine` per
  connective.  Factor every binary connective as `combine ∘ placement op`.

**Package the composition laws as stdlib structures.**

- **Unit and associativity:** `IsSemigroup` per alignment (`besideA` / `aboveA`,
  `Assoc.agda:96-132`), and `IsMonoid` on valid diagrams (`Valid.agda:135-160`).
  `Convenience.Properties` (`hcat-++` and `vcat-++` are the same proof twice, `:38-55`) then
  uses `Algebra.Properties.Monoid`.
- **Commutativity:** `_≈ᵖ_` (`Commute.agda:32`) should be a `Setoid` via
  `Data.List.Relation.Binary.Permutation.Setoid`, with `atop` an `IsCommutativeSemigroup` over
  it.
- **Overlay** (`Diagram/Overlay.agda:18-51`):
  - **Semigroup:** `Overlays` is `Algebra.Bundles.Semigroup`.
  - **Homomorphism:** `IsOverlayHom` is `Algebra.Morphism.Structures.IsMagmaHomomorphism`.
  - **Unit:** `Absent` is `Algebra.Construct.Add.Identity.isMonoid`.
  - **Location:** Scene uses this module, so move it out of `Diagram`.

### 4.4 Dead code and ad-hoc data

**Dead code: `Draw.group`** (`Draw.agda:41`) is matched in seven places and constructed
nowhere (verified by grep).  Deleting it:

- makes `mapDraws` equal to `map ∘ mapDraw`;
- removes the mutual blocks in `Draw.agda:59-73` and `Functoriality.agda:82-123`;
- lets `Data.List.Properties.map-*` replace `mapDraws-++`, `pts-nat`, `anchors-*` and
  `names-++`.

Estimate: about −60 lines.

**Ad-hoc `data` and hand recursion:**

- **`Inline`** (`Text.agda:69`) has four hand-written consumers: `runsI`/`runsT`, `markup`,
  `TextMetrics.go` and `Print.tspans`.  `Objects.md` says "every consumer is a fold", so make
  it `InlineC ⋆ String` with one handler per consumer.
- **`Math`** (`Math.agda:28`): make it `MathC ⋆ String`.  Then variables are `pure`,
  substitution is `>>=`, and `toLaTeX` is a handler.
- **`Names/Soundness.agda:153-235`:** `Draws` / `soundness` / `clean` should be a tupled
  ("banana split") fold into `Layout × Set`, with `soundness` derived from `pfold-rel`.
- **`lower-inject`** (`Curve/Properties.agda:17`) is `lower-embed` + `lower-⋙` + `lower-ret`.
- **`Three/Render.agda:38` (`insert`)** is `Data.List.Sort.InsertionSort`.  Check that ties
  keep their order.
- **List lemmas restated by hand:**
  - `Laws.agda:194-204` restates `map-cong`, `map-id` and `map-∘`.
  - `Text.agda:51-57` (`or-*`) restates `<∣>-identityʳ` and `<∣>-assoc`.
  - `TextMetrics.nth` is a lookup with a default.
  - `Valid.shift0` duplicates `Laws.shift-zero`.


## 5. Scene: one temporal algebra, a scene setoid, Hudak's axioms

### 5.1 One temporal algebra

`Events.agda:109-146` (`evH`) and `Sample.agda:102-138` (`dirH`) each derive `seq` and `rep`
from par / hold / delay in the same way.  `rel-seq` / `rel-rep` are then proved twice more
(`Tick.agda:118-129`, `Sample.agda:317-323`).

**Recommendation:**

- **Define one algebra record.**  A record of temporal-algebra operations (`dur`, `par`, `hold`,
  `delay`, `drive`) yields the `seq` and `rep` derivation, the handler, and its `Congruent`
  proof.
- **Prove relation preservation once.**  A relation preserved by the five operations is
  preserved by the fold.  This is the logical-relations lemma, once.
- **Estimate:** about −70 lines.
- **`duration-nonneg`** (`Laws.agda:182-193`) is `pfold-rel` with a unary relation.

### 5.2 Meaning as a monoid homomorphism (Elliott, *Denotational design with type class morphisms*)

- **The event reading.**  `read-++` (`Sample.agda:79`) says
  `readE : (List Event, ++, []) → (T → Maybe X, merge, nothing)` is a monoid homomorphism.
  - State it with `IsMonoidHomomorphism`.
  - Take the Maybe monoid from `Algebra.Construct.Add.Identity` instead of `Absent` +
    `merge-comm`/`merge-swap` (`Laws.agda:104-114`).
  - `readE` itself is `foldr merge nothing ∘ map readEv`.
- **Naturality in the leaves is missing.**  The two equations are
  `sample ℓ (fmap f s) ≈ sample (ℓ ∘ f) s` and `events (fmap f s) ≡ map (mapEvent f) (events s)`.
  `Event` needs a `map`.  Naturality in the clock is already there (`tick-hom`).

### 5.3 A scene equivalence and Hudak's axioms

There is no equivalence relation on scenes:

- The laws are stated pointwise (`∀ t q → …`, `Laws.agda:140-207`, `Duration.agda`).
- The `Timed` carrier uses `≡P.setoid` on a function type (`Sample.agda:132`,
  `Deck/Program.agda:49`).

**Recommendation:**

- **Define `_≈ₛ_` as a Setoid.**  Two scenes are equal when they have equal durations and
  pointwise equal readings.  Use it as `O` and in `dirCong`.  `Media` takes permutation
  `_↭_` as its equality.
- **Prove congruence.**  Show the signature is congruent for `_≈ₛ_`; this is `Congruent` at
  that setoid.
- **Restate Hudak's axioms as equations in `_≈ₛ_`** (Hudak, *An algebraic theory of
  polymorphic temporal media*, 2004).

| Status | Axioms |
|---|---|
| Present | `∥` associative and commutative; `⨾` associative; `delay-delay` and `delay-zero`; a one-sided `∥` unit |
| Missing | the `⨾` unit; `hold-hold = min`; `delay` / `hold` / `drive` distributing over `∥` |

Hudak's normal-form completeness result is then a target for later.

### 5.4 Smaller items

- `chunkFrom`, `deckFrom` and `sequence` (`Deck/Syntax.agda:94-113`, `Deck/Anim.agda:81`) are
  three hand-written non-empty folds.  Replace them with one `seq⁺` via
  `Data.List.NonEmpty.foldr₁`.
- `mapScene-id/∘` (`Scene/Functoriality.agda:22-39`) are `translate-id/∘` (same fix as §4.1).
- In `Scene/Digital.agda`, `Dn = Sc` is an alias and `evN` duplicates `valN`.  "Evaluate at
  the variable" is written three more times: `Animation.agda:58`, `Moving.agda:37` and
  `Digital.agda:68`.  Use one `evalAt`.
- `nn+` (`Laws.agda:133`) appears again inline at `Laws:81` and `Sample:244`.
- `Laws.agda:73-88` is `map-∘` / `map-cong` / `map-id`.


## 6. Program: Moore machines as coalgebras of a polynomial

### 6.1 The coalgebra reading

`Machine` (`Program/Machine.agda:19`) is a pointed coalgebra of `X ↦ O × (C → X)`.  In
polynomial terms it is a lens `Sy^S → Oy^C` (Spivak and Niu, *Polynomial Functors: A
Mathematical Theory of Interaction*, 2024, ch. 4; Rutten, *Universal coalgebra*, 2000).  The
code does not use this reading:

- **Existential state.**  `Machine` has an existential `State`, which puts it in `Set₁`.
- **Bisimulation by hand.**  Equality is a hand-built `Bisim` setoid.
- **The final coalgebra goes unused.**  `List C → O` is already there as `feed` (`:32`), but
  nothing uses it as the semantics.

**Recommendation:**

1. **Prove the behaviour theorem.**  `Bisim M N ⇔ ∀ cs → feed M cs ≈ feed N cs`.  For finite
   traces this needs only induction on lists.
2. **Change the setoid.**  Take the semantic setoid to be `List C → O` with pointwise
   equality, at level 0, rather than `Machine` up to `Bisim`.  This changes how the
   following are stated:
   - `Via` (`Supports.agda:113-129`) becomes `feed M cs ≈ feed N (mapMaybe dec cs)`.
   - `bisim-*` and `via-bisim` disappear.
   - `lower-sound` becomes a `mapMaybe` lemma.
3. **Keep `Machine` for execution only.**  Optionally, give the coalgebra category via
   `Categories.Category.Construction.F-Coalgebras` and state that `feed` is the map into the
   final coalgebra.

### 6.2 Name the structure that is already there

- **`prodM`** (`Sem.agda:58`) lifts a scene algebra to machines.  This is a
  distributive-law / bialgebra situation (Turi and Plotkin, *Towards a mathematical operational
  semantics*, 1997).  The "synchronous product" is the product of lenses precomposed with the
  diagonal wiring `C → C × C`.
- **`inject-const`** says `constM` is an algebra morphism.  State it as such.
- **`sem-bind`** says the fold is a monad morphism.  It follows from fusion (§2.2) and need not
  be its own induction.

### 6.3 Other items

- `skip-inject`, `lower-supported` and `lower-sound` (`Program/Syntax.agda:57`,
  `Supports.agda:99-191`) should be derived from the `lower-*` laws and `pfold-hom` /
  `pfold-rel`.  About −60 lines.
- `AllSup` (`Supports.agda:77`) and `SidesDia` (`Scene/Digital.agda:100`) should be one
  generic `All⋆ P : C ⋆ X → Set`, a fold into `Set`, in `Container`.
- `par-runs` / `wait-runs` (`Deck/Program.agda:83-97`) are facts about `prodM` / `awaitM`.
  Move them to `Program/Sem`.
- `Deck.Program.after` (`:80`) is `feed` word for word (verified).  Delete it.


## 7. Deck: content as containers, decks as `join`

- **`Block` is a rose tree in disguise** (`Deck/Content.agda:39`).  Five constructors only hold
  sub-flows.  Split it into a container `BlockC` with leaves.  Then `plain*` (`:80-126`),
  `lowerBlock` / `lowerFlow`, and `Backend.Render` (§8) become handlers.
- **Deck lowerings re-prove the Kleisli laws.**  `lowerFlow-id` / `lowerFlow-fuse`
  (`Deck/Lower.agda:62-130`, about 70 lines) re-prove the Kleisli laws, and become `lower-ret` /
  `lower-⋙`.  Even without the container, these hold:
  - `lowerFlow l = concatMap (lowerBlock l)`, and `lowerFlow-++` is `concatMap-++`.
  - `Lower.Lowering` and `Lower._⋙_` clash by name with `Container.Lowering`.  Rename them,
    or better, make them the same thing.
- **"A deck is a scene of scenes" is the monad multiplication.**  `flat d = d >>= slideScene`
  (`Deck/Syntax.agda:115`), i.e. `join ∘ fmap`.  State once that `timed` is a morphism of monad
  algebras.  `flat-visible` then follows.
- **`chunks-++` is a monoid homomorphism** (`Deck/Syntax.agda:56-76`) into the "glue" monoid on
  `List⁺ Flow`.  That also closes `Dropped.md` §6 ("`glue` is a monoid").
- **Duplicates:**
  - `Deck/Read.agda:107-125` and `Deck/Machine.agda:57-64, 119-121` are the same duration
    lemma, once via `Timed` and once via `Media`.  `ol` and `ol′` are the same function.  Merge
    the events and labels part of `Deck/Machine` into `Deck/Read` (about −40 lines).
  - `labelOf` should be `labelIn ∘ map ol′`.  `labelOf-shift` and `labelOf-leaf` are unused.
- **Instantiated more than once:** `Sample {ℕ}{⊥}{Flow} … listOverlay` (three times) and
  `Events {ℕ}{⊥}` (twice).  Add one `Slides.Deck.Clock` that opens them once.
- **`Deck/Digital.agda`** (53 lines) is a special case of `Scene/Digital`.  Its `map-id` is
  `Data.Maybe.Properties.map-id`.  Merge or drop.

Note: `Scene/Functoriality`, `Scene/Duration`, `Program/Embed` and `Deck/Digital` are imported
by nothing.  That is by design for theory modules (`tests/check_closure.py`).  But
`Program/Embed` (34 lines) only restates `leafT`; fold it into `Animation`.


## 8. Backends and plots: algebras, as `Objects.md` promises

### 8.1 Backends

`Objects.md`, item 4 of "The maps that carry the weight", says "backends are algebras of the
deck signature".  In the code they are not:

- **Rendering is hand recursion.**  `Backend/Render.agda:59-178` (`renderBlock`, `renderFlow`,
  `bulletList`, …) is hand-written mutual recursion over `Block` / `Inline`.  After §7 it is
  one handler.
- **"Restyling is a homomorphism" holds only for the thin `Part` layer**
  (`Render.agda:212-229`).  After §7 it is an instance of `pfold-rel` with
  `R x y = map f x ≡ y`.
- **Animation shipping hand-recurses over existing signatures.**  `scI`, `drvI`, `diaT` and
  `pointsT` (`Backend/Animation.agda:109-126, 179-196`) recurse by hand over
  `(SpaceC ⊎ TimeC) ⋆ _`, `CouplingC ⋆ _` and `DiagramC`.  Handlers and `_⊕_` already exist,
  so these become `pfold (spaceJ ⊕ timeJ) leafJ`, and so on (about −30 lines).

### 8.2 Sharing

- **`Share.Tree` is a rose tree** (`Share.agda:37`), and `share` is a hand-written fold into a
  state monad.
  - Do hash-consing generically for `C ⋆ ⊥` with decidable shapes, as `pfold` into
    `Effect.Monad.State`.
  - Then animation terms can be shared without being stringified to `Tree` first.
- **`readBack ∘ shareTop ≡ id` is a section/retraction.**  State it as
  `Function.Bundles.RightInverse`.
- **Library replacements:**
  - `_⊑_` with `⊑-trans` and `⊑-length` (`Share/Properties.agda:51-60`) is
    `Data.List.Relation.Binary.Suffix`.
  - Storing the table oldest-first removes `reverse`, `at-cons` and `at-top`.
  - Estimate: −60 to −80 lines.

### 8.3 Plot

- **`Mark` is flat data** (`Plot/Mark.agda:25`) and `renderMark` an ad hoc function.
  - Make `MarkC` a signature and `renderMark` a `Lowering MarkC DiagramC`.  Plot content is
    then `(DiagramC ⊎ MarkC) ⋆ ⊥`, lowered by `copairL ret renderMark`.
  - With `Mark` functorial in its point type, `logMark` is `map` and `lerpMark` is `zipWith`
    (`Plot/Log.agda:61`, `Plot/Anim.agda:54`).
- **`exact` gets the same treatment.**  `Plot/Exact.agda:50` builds a one-node `Dia⁺` and lowers
  it at once.  Make `exact` a `MarkC` command lowered through `lowerCurve`.  Otherwise, drop
  `Dia⁺` / `inject` and call `curve` directly.

### 8.4 Duplicated helpers

Total about −90 lines; move the helpers into `Backend/HTML`:

| Helper | Copies |
|---|---|
| `pow10` | `Plot/Data.agda:19` and `Plot/Ticks/Rat.agda:36` (verified); use `ℕ._^_` |
| `lt` | `Plot/Log.agda:29` and `Plot/Clip.agda:28` (verified) |
| `lerp`, `lerp-0`, `lerp-1` | `Plot/Anim.agda:31-38` duplicates `Scalar/Coupling` |
| `natⱼ` | twice |
| `opt*` | four times |
| `div` | twice |
| `showQ` | duplicates `Plot/Format.trimmed` |
| `maybe′`, `cat` | local copies of stdlib |
| `lineH` | twice in `Render.agda` |
| `revealHash`, `plainHash` | unused |


## 9. Order of work

Each phase follows `Contributing.md`: a line budget, a clean `make check`, and byte-identical
goldens.  Phases 1–2 change no output.  The line budgets are a tripwire: clarity and robustness justify
overshoot (the author's stated position).

| Phase | Work | Net lines | Status |
|---|---|---|---|
| 1 | **Container spine** (§2): stdlib setoid for `Poly`; one fold with `fold-unique` + fusion; `bind`, `lower`, `translate` defined as folds; laws derived; one monad (adjunction); `copairL`; one `_≈⋆_`; one level discipline; `pfold` as a thin view of `fold`. | −350 | **Done**, b05e69d..763437f, −297. |
| 2 | **Theories on stdlib structures** (§3).  Prerequisite for the planned setoid equality. | −60 | **Done**, 78f3403, +23. |
| 3 | **Diagram tag/payload split** and `Draw.group` removal (§4.1, §4.4); derive `mapDia`/`mapScene` functoriality; `layout` as a `NaturalTransformation`. | −250 | **Done**, e9bf14d..67a4c31, −2.  Skipped: layout as a `NaturalTransformation` (§4.2) and collapsing the 17-way handler splits (`layoutCong`, `okOp`, `clean`, `soundness`, `digit`), which are genuine per-operation handlers. |
| 4 | **Temporal algebra record**, scene setoid `_≈ₛ_`, monoid-homomorphism statements, Hudak axioms (§5). | −100 | Open. |
| 5 | **Program behaviours** `List C → O`, bisimulation ⇔ trace equality, `Via` via `mapMaybe` (§6). | −110 | Open. |
| 6 | **Content as containers** (`BlockC`, `InlineC`, `MathC`, `MarkC`); backends and plots as handlers; generic sharing (§7, §8). | −300 | Open. |
| 7 | **Small duplicates** (§4.4, §5.4, §8.4).  Can run in parallel with any phase, on disjoint files. | −150 | Open. |

Phase 1 comes first because every later phase uses its lemmas.  Phases 3, 4 and 6 touch
disjoint layers and can run in parallel after it.  Update `docs/Objects.md` with each phase,
especially the one-paragraph categorical statements: Lowerings as Kleisli of `(−)*`, machines
as coalgebras, size and layout as monoid homomorphisms.


## 10. Literature (to add to `Objects.md`)

Already cited there: Abbott, Altenkirch and Ghani; Swierstra; Hyland, Plotkin and Power;
Plotkin and Power; Hudak; Elliott; Yorgey; Rutten.  Add:

- **Fold laws.** Malcolm, *Data structures and program transformation* (1990), and Bird and
  de Moor, *Algebra of Programming* (1997): fusion and banana split.  Hinze, *Adjoint folds and
  unfolds* (2013).
- **Polynomial monads.** Gambino and Kock, *Polynomial functors and polynomial monads* (2013):
  the free monad on a polynomial is polynomial.
- **Monads on containers.** Uustalu, *Container combinatorics: monads and lax monoidal
  functors* (2017).
- **Quotients.** Abbott, Altenkirch, Ghani and McBride, *Constructing polymorphic programs with
  quotient types* (2004): why shapes stay `Set`.
- **Machines.** Spivak and Niu, *Polynomial Functors: A Mathematical Theory of Interaction*
  (2024): Moore machines as lenses, wiring.
- **Operational semantics.** Turi and Plotkin, *Towards a mathematical operational semantics*
  (1997): `prodM` as a distributive law.
- **Universal algebra.** Hyland and Power, *The category-theoretic understanding of universal
  algebra: Lawvere theories and monads* (2007): theories as signature plus equations.
- **Handlers.** Plotkin and Pretnar, *Handlers of algebraic effects* (2009): handlers are
  algebras.
- **Denotational design.** Elliott, *Denotational design with type class morphisms* (2009):
  meanings as homomorphisms.
