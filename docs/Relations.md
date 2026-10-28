# How the DSLs relate: arrows, laws, gaps

Read-only audit of `origin/main` (53c5ad6; `docs/Map.md` calls it a427adf+) and branch `deck-scene` (5cb48b0,
read with `git show deck-scene:...`, cited as `[ds]`).  Nothing under `src/` or `tests/` was changed or typechecked
here: every citation is from reading the code.  **(V)** = verified in the cited code; **(I)** = inferred, not
checked by Agda.  "MISSING" = I searched for a theorem and found none.  Line numbers are for the file on main
unless marked `[ds]`.

## 1. Inventory

| name | what | file:line | carrier / parameters |
|---|---|---|---|
| `CoreC, SubC` ; `OrdC, FloorC` ; `EaseC` | scalar signatures (core `0 + ⊔ fromℕ %`, sub, ordered/`lt min`, floor `divBy modBy mulLit`, ease) | `Diagram/Expr.agda:57,67`; `Diagram/Ordered.agda:94,103,112` | `Sig = Container 0ℓ 0ℓ` |
| `ExprC = Core ⊎ Sub`, `OC = ExprC ⊎ (OrdC ⊎ FloorC)`, `QC = OC ⊎ EaseC` | the layered scalar signature; `OExpr V = Term OC V = OC ⋆ V` | `Expr.agda:71`, `Ordered.agda:115-121` | variables `V`; `Handler Σ S` = algebra (`Signature.agda:46`) |
| `DiagramC S = Op S ▷ arity` | diagram signature; `Dia S = DiagramC S ⋆ ⊥` (closed) | `Diagram/Syntax.agda:215,219` | scalar parameter `S` (ℕ, ℚ, `OExpr ⊤`) |
| `Tmpl = Dia (OExpr ⊤)` | a template: sizes are formulas in one variable; free monad *inside* a free monad | `Anim/Syntax.agda:63` | |
| `TimeC = TOp ▷ tarity` (Seq Par Hold Delay Repeat Drive) ; `Scene A = TimeC ⋆ A` ; `Anim = Scene Tmpl` | the one temporal container | `Anim/Syntax.agda:56,60,66` | leaf type `A`; `Clock` `T` of the reading |
| `ContentC, LayoutC, BlockC = ContentC ⊎ LayoutC` | slide vocabulary; `Content = ContentC ⋆ ⊤`, `Body = BlockC ⋆ ⊤`; nesting is by *shape* fields (`columns : List Content`), not by sum | `Core.agda:98,125,129,133` | positions all `⊤` |
| `DeckC = DeckShape ▷ ⊤` ; `Deck = DeckC ⋆ ⊤` | `slide o Body`, `stack o (List Body)` | `Core.agda:154,157` | |
| `SceneC V, AwaitC C, LabelC, ProgC C = SceneC ⊎ AwaitC C ⊎ LabelC` ; `Prog C A` | the input-parametric program; `Deck C A = Prog (Nav ⊎ C) A` | `Input.agda:29-42` | `V` (take `Shape BlockC`), awaited commands `C` |
| `BlockAwaitC X = BlockC ⊎ AwaitC X ⊎ LabelC`, `DeckBlockC C`, `Body⁺ X` | on main, a *second copy* of `ProgC` over `BlockC` | `Input/Deck.agda:33-40` | `[ds]` replaces by `BlockAwaitC = ProgC` |
| `Supports C` (`S, inj, dec`, mutually inverse) | a backend's command vocabulary, partial embedding of `Nav ⊎ C` | `Input/Supports.agda:38` | |

Backends and other algebras / folds (all `fold`s of the container named):

| name | container -> carrier | file:line |
|---|---|---|
| `layoutAlgebra`, `layout`, `compile` | `DiagramC S -> Layout S`; `compile : Dia S -> Diagram` (data, the SVG record) | `Diagram/Layout.agda:54,70,74` |
| `namesAlgebra`, `dangling` | `DiagramC S -> Usage` | `Diagram/Names.agda:53,57` |
| `evalO O ρ`, `foldT H ρ` | `OC -> S` (`Handler`) | `Ordered.agda:203`, `Signature.agda:62` |
| `durAlg`, `footprintAlg` | `TimeC -> ℕ`, `TimeC -> List String` | `Anim/Syntax.agda:134`, `Anim/Footprint.agda:35` |
| `timeAlg ⊙ bnd val`, `sample`, `frames` | `TimeC -> TM X = ℕ × (T -> Maybe X)`, any `Clock`; `timeline` is ℕ-clock tabulation | `Anim/Sample.agda:~60,~66,~100`, `Anim/Timeline.agda:40` |
| `perform`, `Param.place` | `TimeC -> ℕ × List (ℕ × A)` `[ds]`; `TimeC ->` symbolic scene | `[ds] Anim/Perform.agda:45`, `Anim/Param.agda` |
| `contentAlg`, `blockAlg = copair contentα layoutα`, `renderBody` | `ContentC / BlockC -> Forest` | `Backend/Common.agda:188,236,240` |
| `deckAlgBy f` (Reveal), `deckAlgBy f` (Plain) | `DeckC -> Forest`; `f : Body -> Body` is the per-slide pass | `Backend/Reveal.agda:67`, `Backend/Plain.agda:52` |
| `restyledContentAlg` | `ContentC -> Forest`, markup post-processed | `Backend/Restyle.agda:46` |
| `sem l`, `machine` | `ProgC C -> Machine C` (Moore machine), Kleisli in the leaf | `Input/Machine.agda:~50-60` |
| `navM`, `nextCount`, `labelTable` | recursive folds of `Deck C A` | `Input/Navigation.agda` |
| `sceneBy step?`, `deckS` | `Prog X ⊤ -> Scene (Maybe Leaf)`; `List Slide -> Scene (Scene …)` | `[ds] Steps.agda`, `[ds] Input/Slides/Properties/Scene.agda:45` |

## 2. The arrows

Kinds: **CM** container morphism `C ⇒ D` (`Container.Polynomial.Morphism`: natural transformation, `Poly-id`, `Poly-∘`);
**K** Kleisli lowering `Lowering C D = Shape C -> D ⋆ Position C` (a monad morphism `C ⋆ -> D ⋆` by `lower-bind`,
`Container/Lowering/Properties.agda:73`; identity `lower-ret :91`; composition `lower-⋙ :95`; the category of lowerings is
`Container/Lowering/Category.agda`); **F** fold into an algebra; **D** data embedding (no container structure).
Generic laws available for free (V): `lower-bind`, `lower-ret`, `lower-⋙`, `lower-embed`, `lower-fusion`
(`Properties.agda:73-165`), `Fusion.fusion` for `translate` (`Interpret/Properties.agda`/`Algebraic/Properties.agda`),
`Fusion.fold-hom` (algebra homomorphisms commute with folds, `Interpret/Properties.agda:68`), `copair-unique`
(`Sum/Properties.agda:86`), `fold-bind` (`Algebraic/Properties.agda:42`).

```
 CoreC SubC OrdC FloorC --CM(coreO..floorO)--> OC --CM(inl)--> QC <--CM(inr)-- EaseC          [scalars]
                                                 |  \--K lowerO (OC->OC)  = lowerQ
                                                 |
 OExpr V = OC⋆V --F evalO O ρ--> S ;  mapDia/scalarMor: DiagramC S ⇒ DiagramC T (CM) = Dia S -> Dia T
      ^ lit: Dia ℕ -> Tmpl (mapDia lit)                                                 [diagram]
      |
 Dia S --F layout--> Layout S --D compile--> Diagram ----D `diagram d`----+
 Dia S --F namesAlgebra--> Usage                                           |
   |  pure d  (leaf of Scene)         hold n d = Hold n (Drive const (pure (mapDia lit d)))
   v                                                                       |
 Anim = TimeC ⋆ Tmpl --F timeAlg/sample (any Clock)--> TM (Dia T)         |
   |        |  --F durAlg, footprintAlg, perform[ds] ; timeline (ℕ tabulation) --D Render.render--> ContentShape
   |        |                                                  `animation d ds ms play`  ----+
   |   Scene(Scene A) --join = >>= id--> Scene A  (nested-flat = foldS-bind)               |
   |                                                                                        v
 ContentC --CM inl--> BlockC <--CM inr-- LayoutC   (columns/box/... hold Content: shape fields) 
   |          \         |
   |           lowerDeck l = lower (deck l): K DeckC->DeckC from l : K ContentC->ContentC (via Lower.block, layout)
   |                    |  elabL : K BlockC -> DeckBlockC C   (pause ↦ await next)   [Steps/Input.agda:54]
   |                    v
   |  DeckBlockC C = BlockC ⊎ AwaitC ⊎ LabelC --CM toProgC--> ProgC (Shape BlockC)  [Input/Deck.agda:43; [ds]: identity]
   |  AwaitC C --CM awaitIn--> BlockAwaitC                                      
   |  ProgC (Nav⊎C) --K lowerOp (= lowerDeck b)--> ProgC (S b)   (also lowerCmdBlock on Body⁺, main only)
   |  ProgC (Nav⊎C) --K skipOp--> ProgC (Nav⊎C)
 DeckC ⋆ ⊤ --F slides--> List Slide --F deckBody--> Body⁺ --toProg--> Prog (Nav⊎C) ⊤    (= deckProg)
 Prog C A --F sem--> Machine C --liftE(dec)--> Machine D ;  Prog --F nextCount/labelTable--> ℕ / String->Maybe ℕ
 Prog X ⊤ --F sceneBy[ds]--> Scene (Maybe Leaf) --F perform--> page (fragments)  ;  deckS[ds]: List Slide -> Scene(Scene)
 DeckC --F deckAlgBy f (Reveal | Plain)--> Forest <--hom restyle (ContentC only)
```

| # | arrow (file:line) | kind, direction | structure / law | theorem (module.name:line) |
|---|---|---|---|---|
| A1 | `coreO subO ordO floorO` (`Ordered.agda:123-132`), `weakenQ = translate inl` (`:168`) | CM, layer -> `OC`/`QC` | folding a weakened term = folding with restricted handler | `Signature.Properties.foldT-translate:67`, `weaken-bind:82`, `evalQ-weaken` (`Ordered/Properties/Laws.agda:127`) (V) |
| A2 | `lowerO : Lowering OC OC`, `lowerQ = lower lowerO` (`Ordered.agda:285-291`) | K, ordered/floor -> core | evaluation preserved at ℕ; faithful | `Discrete.lower-ℕ:52`, `discrete-ℕ:88`, `Faithful.faithful-lower:168`; `Laws.foldT-lower:61` is a hand copy of generic `lower-fusion` (V) |
| A3 | `evalO O ρ` (`Ordered.agda:203`) | F, `OExpr V -> S` | homomorphism of `Ops/Ord/Floor` layers; bind law | `Laws.evalO-hom:73`, `-ord-hom:80`, `-floor-hom:83`, `foldT-bind:44`, `evalO-substO:101` (V) |
| A4 | `mapDia f = translate (scalarMor f)` (`Syntax.agda:321`; `MapFusion.agda:81`) | CM + K, `Dia S -> Dia T` | functor: id, composition; = `lower (embed ·)`; fusion with any fold | `mapDia-translate:87`, `mapDia-lower:104`, `mapDia-id:143`, `translate-∘:126`, `fold-mapDia:183` (V; `translate-∘` is a 10-clause bespoke proof, generic form MISSING) |
| A5 | `layout : Dia S -> Layout S` (`Layout.agda:70`) | F | natural along scalar homs; every connective; | `Layout.Properties.layout-natural:229` (+ `*-natural :87-173`), `Ordered.Laws.layout-evalO:110`, `layout-substO:114` (V) |
| A6 | `namesAlgebra` vs `layout` | F, two algebras, hom between | `anchorNames ∘ layout = names fold` | `Names.Properties.Soundness.names-fusion:101` (V); `names-mapDia` (`Names/Properties.agda:17`) (V) |
| A7 | **Diagram -> Anim**: `pure d : Anim` (leaf); `hold n d = seg (const) (mapDia lit d)` (`Anim/Syntax.agda:96-102`) | D into a Kleisli unit (`pure`) ; `hold` composes A4 with `Hold ∘ Drive` | `sample (pure a)` is the constant eternal timed value (definitional, `foldS` leaf) (V); *agreement with `layout`* only through hypotheses `Exact`/`Faithful` | `Sample.Properties.frames-seg:48`, `Continuous.Properties.leaf-tick:104`, `inst-exact:96`, `Assembly.Continuous.assembly:140` (V; needs `AllExact`, ℚ vs ℕ; the plain statement "frame k of `hold n d` is `d` and `layout_ℕ` of it is `layout d`" is MISSING) |
| A8 | `foldS` readings of `Anim`: `dur`, `footprint`, `sample`/`frames`, `perform`, `place` | F | bind = substitution: `foldS (>>= f) = foldS (foldS ∘ f)`; algebra is congruent | `Syntax.Properties.Generic.foldS-bind:56`; `[ds] Sample.Properties.Nested.timeAlg-congruent:71`, `nested-flat:83` (V) |
| A9 | clocks ℚ vs ℕ: `readA ratClock ratVal` vs `readA natClock natVal` | F twice + logical relation (not an algebra hom: `ι` is not onto) | `RelN` closed under all connectives | `Assembly.Calculus.relN-hold/seq/delay/par` (`Assembly.agda:58-97`), `Assembly.Continuous.assembly:140`, `Param.Properties.assembly:240` (V; `Repeat`, bare `Drive` not covered, `docs/TimeSwitch.md` §8) |
| A10 | `timeline : Anim -> List (Dia ℕ)` (`Timeline.agda:40`) | F then tabulate | length = duration; `⨾` = `++` | `Timeline.Properties.length-dur:29`, `timeline-⨾` (V) |
| A11 | `footprint` vs `names` | F, algebra hom of leaf | footprint of a template = its names | `Footprint.Properties.names-inst:27`, `names-discrete:32`, `par-comm-footprint:42` (V) |
| A12 | **Anim -> Block**: `Render.render` (`Render.agda:76`), `renderLoop`, `renderBoth` | D: `timeline`, `compile`, `resize` into the leaf `animation d ds ms play`/`paramAnimation` | none relating `ds` to `sample` | only `Render.Properties.length-restsOf:12` (V); frame-by-frame agreement MISSING |
| A13 | `Dia -> Diagram -> Content`: `compile`, leaf `diagram d` | D | `compile` at ℤ/ℕ agree on four decks, by `refl` | `Examples/Pairs/Properties.agda:33-39` (examples, not a theorem); general MISSING |
| A14 | `inl : ContentC ⇒ BlockC`, `inr` (`Container/Sum.agda:31`) | CM | `blockAlg = copair …`; `copair-unique` | `Sum.Properties.copair-unique:86` (V) |
| A15 | content lowering -> deck lowering: `Lower.layout/block/deck` (`Lower.agda:95-113`), `lowerDeck l = lower (deck l)`; lowerings `stripNotes`, `diagramPlaceholder`, `animationFinal`, `stripScripts` | K ContentC->ContentC lifted to K DeckC->DeckC (functorial in `l`) | monad morphism by `lower-bind` (V, generic); **`lowerDeck ret ≈ id`, `lowerDeck (l ⋙ m) ≈ lowerDeck m ∘ lowerDeck l`: MISSING**; `animationFinal` has no spec beyond `finalFrame-looping:42`, `finalFrame-no-steps:45` |
| A16 | `elabL : Lowering BlockC (DeckBlockC C)` (`Steps/Input.agda:54`), `elab = lower elabL` | K, `pause ↦ await next` | monad morphism; bridge to old pass | `Steps.Properties.elab-bind:112` (a hand-proved instance of `lower-bind`, redundant, (I)), `stepsBy-elab:135`; `[ds]` `scene-elab` (V) |
| A17 | `toProgC : BlockAwaitC X ⇒ ProgC X` (`Deck.agda:43`), `toProg = translate toProgC` | CM (an isomorphism of containers up to reduction) | bind, lowering naturality | `Input.Slides.Properties.toProg-bind:90` (bespoke), `Lower.Properties.lowerCmdBody-lowerDeck:60` (a naturality square of two K along a CM, 5-clause bespoke induction) (V); `[ds]` deletes both by making the two containers equal |
| A18 | `lowerOp/lowerDeck b`, `skipOp/skipDeck b` (`Input/Supports.agda:56-74`); `lowerCmd`, `lowerCmdBlock`, `lowerCmdBody` (`Lower.agda:134-146`, main only) | K, `ProgC (Nav⊎C) -> ProgC (S b)`; the `Body⁺` copy duplicates it | monad morphism (`lower-bind`, V generic; `Lower.Properties.lowerCmdBody-bind:55` re-states it) | `Supports.Properties.supported-kept:43`, `skip-supported:51` (V) |
| A19 | `sem l : Prog C A -> Machine C` (`Machine.agda`), `machine`, `liftE h` | F into a Moore machine (Set₁, equality `MIso`, so `Fusion` does not apply directly) | Kleisli: `sem (p >>= f) ≈ sem (sem ∘ f) p`; commutes with lowering | `Machine.Properties.sem-bind:87`, `seq-machine:94`, `liftE-*:112-148`; **`Supports.Properties.lower-sound:84`, `lower-supported:106`** (machine of `lowerDeck b p` = `liftE (dec b)` of machine of `p`, hypothesis `Supported p`) (V) |
| A20 | `deckProg d = toProg (deckBody (slides d))` (`Input/Slides.agda`): fold to `List Slide`, then re-sequence with `label` and `await next` | F then constructive K-like re-assembly | table of labels = start positions | `Input.Slides.Properties.slide-table:171`, `auto-start:211`, `elab-count:99`; relation to `machine`/`sem`: MISSING on main (V) |
| A21 | `[ds]` `sceneBy step? : Prog X ⊤ -> Scene (Maybe Leaf)` (`show c;k = c ∥ k`, step = `Delay 1`) | F into a `TimeC`-algebra on `Scene`; **not** a lowering: `show` would have to duplicate the continuation under `Par` (I) | duration, content at tick j, machine agreement, lowering invariance, elab invariance | `[ds] Steps.Properties.dur-sceneBy:72`, `shown-chunks:104`, `machine-shown:141`, `scene-elab:48`; `Lower.Properties.scene-lowered:75` (a bespoke 5-clause copy of `lower-fusion`, (I)) (V); `sceneBy-bind` MISSING |
| A22 | `[ds]` `deckS : List Slide -> Scene (Scene (Maybe Leaf))`, `flat = >>= id` | F then monad `join` | slides in sequence | `[ds] Scene.deck-nested:75`, `startOf-prefix:58`, `deck-shown:80`, `dur-flat:65` (theory module; `Deck` is still `DeckC ⋆ ⊤`) (V) |
| A23 | `deckAlgBy f` Reveal / Plain; `renderDeckBy f = D.fold (deckAlgBy f)` | F, `DeckC -> Forest` | length, bind (Reveal only), per-slide pass pointwise, `present = old renderer` | `Reveal.Properties.renderDeck-length:45`, `renderDeck-bind:50`, `renderDeckBy-cong:63`, `present-renderDeck:73`; `Plain.Properties.renderDeck-length:42`, `renderDeckBy-cong:52`, `present-renderDeck:59`; `Common.Properties.renderBody-bind:25` (V) |
| A24 | Reveal <-> Plain | none: Plain flattens `stack` and wraps in `<section class=slide>`, Reveal nests | – | MISSING (the two `renderDeckBy-cong` / `present-renderDeck` proofs are copies) |
| A25 | `restyle-hom : contentAlg -> restyledContentAlg` (`Restyle.agda:57`), `restyle = fold-hom` (`:76`) | algebra hom, `ContentC` only | markup map commutes with rendering | `Restyle.restyle-hom`, `Fusion.fold-hom` (V); not for `blockAlg`, `deckAlgBy` (MISSING) |
| A26 | Nav: `navM`, `replay` | F + state | `prev ∘ next = id`, label resolution | `Navigation.Properties:87-95`; `[ds] machine-shown` links to scene at body level (V) |

## 3. Gaps

"Generic" = an instance of a lemma already in `Container.*` (`lower-bind`, `lower-⋙`, `lower-fusion`, `lower-embed`,
`fold-hom`, `fold-bind`, `copair-unique`).  Sizes are my estimates (I).

| id | missing arrow / law | size | prio | cost route |
|---|---|---|---|---|
| G1 | **Diagram -> Anim agreement**: for `d : Dia ℕ`, frame `k < n` of `hold n d` is `d` at ℕ (`layout_ℕ (frame) = layout d`; ℚ: `layoutQ = mapLayout ι (layout d)`, no hypothesis because `lit` is exact), `names` = `footprint` | 25-40 | high | `frames-seg` + `fold-mapDia` + `layout-evalO` at `evalO natO`; `evalO-hom` makes `lit` a hom; `Exact`/`Faithful` become automatic for `lit`-templates, so it also shrinks the `AllExact` hypothesis for non-parametric leaves |
| G2 | **Anim-in-Block**: `animation d ds ms (onSteps rs)` produced by `render` has `ds = frames of timeline a` (compile per tick, equal size), `length ds = max 1 (dur a)`; `animationFinal` = last frame of `timeline`; `restsOf` = cumulative durations | 40-60 | high | bespoke (`compile`, `resize`, `frameDiagrams`), uses `length-dur`, `Timeline` laws; `Lower.finalFrame` gets a spec |
| G3 | `lowerDeck` functorial in the content lowering: `lowerDeck ret ≈ id`, `lowerDeck (l ⋙ m) ≈ lowerDeck m ∘ lowerDeck l` (`ShowcaseMain.agda:42` composes with `⋙` and applies once) | 30-50 | medium | `lower-⋙` + congruence in `map (lower l)` of `columns`; or restate `layout l` as a CM-indexed family |
| G4 | **Reveal vs Plain**: `Plain.renderDeck d = hom (Reveal.renderDeck (lower flattenStacks d))` with `flattenStacks : Lowering DeckC DeckC` and a section-rewrapping map; or one parameterised `deckAlgWith` | 40-70 incl. removing duplicates | medium | `lower-fusion` (pull back Reveal's algebra along `flattenStacks`) + `fold-hom`; deletes `Plain.renderDeckBy-cong`, `present-renderDeck`, `renderDeck-length` (≈ 35 lines) (I) |
| G5 | **Deck -> Prog and Prog -> Scene commute with Nav/Machine** at deck level: `view (replay (machine (deckProg d)) n)` vs `flat` scene at `n` (`deck-shown`). `[ds]` §7 records that the machine view *accumulates* (`Par`) across slides while the flat scene hides earlier slides (`Seq`): the two are not equal; the statement must say which | 60-100 | high (needs an author decision on the semantics) | `sem-bind`, `seq-machine`, `deck-shown`, `machine-shown` compose; the dual mismatch is the finding |
| G6 | `sceneBy-bind`: `sceneBy (p >>= f) = sceneBy p >>= (nothing ↦ sceneBy (f tt) ; just c ↦ pure (just c))` (the `pure nothing` end marker is the bind point) | 15-25 | medium-high | direct induction; then `deckBody`, `slideK`, `rest` follow by it; replaces the removed `go-bind`/`goBy-bind` (≈ 60 on main) |
| G7 | `translate-∘` / `mapDia-∘` generic: `translate (m ∘ n) ≈ translate m ∘ translate n` | 8-12 | low-medium | **generic**: `embed (m∘n) = embed n ⋙ embed m` pointwise, then `lower-⋙` + `lower-embed`; replaces `MapFusion.translate-∘:126` (≈ 12 clauses) and `translate-id:110` |
| G8 | `fold-bind` for monoid/⊤-position algebras: `fold (d₁ >>= λ _ → d₂) = fold d₁ ++ fold d₂` when `α (c,k) = f c ++ k tt` | 15-25 once | medium | **generic** `Container.Interpret.Properties` (via `fold-bind-alg`); then `Reveal.renderDeck-bind:50`, `Common.renderBody-bind:25`, Plain's missing one, `[ds]`-removed `go-bind` shapes are 1-line instances (saves ≈ 40) |
| G9 | `sem`/`MIso` is a fold into a Set₁ non-setoid carrier, so `lower-fusion` does not apply to `lower-sound` (`Supports.Properties.lower-sound:84`, ≈ 20 lines) | 30-50 | low | a `Machine` setoid (`MIso`) as `Setoid 1ℓ 1ℓ` then `lower-fusion` at level 1 (generic lemma is level 0 only: `Fusion (C D : Container 0ℓ 0ℓ)`) |
| G10 | `scene-lowered`, `lowerCmdBody-lowerDeck`, `steps-lowered`, `elab-bind`, `toProg-bind`: bespoke instances of `lower-fusion` / `lower-bind` / CM naturality | – | medium | **generic**; `[ds]` already deleted three; `scene-lowered` becomes `lower-fusion` once `sceneBy` is an `F-Algebra` (positions `⊤`, so `Congruent` needs no function extensionality (I)) |
| G11 | `Restyle` lifted from `contentAlg` to `blockAlg`/`deckAlgBy` (hom of the copair; hom for the slide wrapper) | 20-30 | low | **generic** `copair-unique` + `fold-hom` |
| G12 | scalar-level folds re-prove the generic theory over `Handler` (≡-algebras): `Signature.Properties:61-87` (fold-agrees, foldT-translate, weaken-bind), `Ordered.Laws:44-70` (foldT-bind, foldT-lower, `pull`), `MapFusion:162-185` (`pull`, `Congruent`, fold-translate, fold-mapDia), `Diagram.Syntax.Properties.Generic` (`Congruent`, `toAlgebra`, `fold-agrees`, `fold-hom`), `Anim.Syntax.Properties.Generic` (`Congruent`, `foldS-agrees`, `foldS-bind`) | -150 to -250 net (I) | medium (debt) | one **generic ≡-algebra fold** module in `Container.Interpret` (`Congruent`, `pull`, `fold-translate`, `fold-lower`, `fold-bind`, `fold-hom`); 4 `Congruent` and 3 `pull` collapse to 1 |
| G13 | `Repeat`/bare `Drive`/free leaf have no `RelN` clause or `place`; swap law (needs `Windowed`) | 40+ | low | `docs/TimeSwitch.md` §8; not an arrow gap |

## 4. Sorts

Where several types do work (V unless marked):

* **Closed vs open diagrams.** `Dia S = DiagramC S ⋆ ⊥` has no leaves; `Tmpl = Dia (OExpr ⊤)` carries the one parameter inside
  its *scalars*, not as a leaf.  A single sum `DiagramC ⊎ TimeC` would give `Dia`s with temporal nodes inside the geometry and
  `Hold`/`Drive` below `Beside`; the separate sort is what makes `layout` total on `Dia S` and `Seq/Par` only over whole frames.
* **Two-level scalars.** `DiagramC S` is parametric in `S`; `OExpr` is a second free monad.  `Drive` substitutes the scalar variable (`bnd`),
  which is *only* meaningful because scalars are a separate sort (`layout-evalO:110`).  Merging them would lose
  "`layout` commutes with evaluation" as a naturality statement.
* **Stratified nesting.** `columns : List Content`, `slide : Body`: `Content = ContentC ⋆ ⊤` *cannot* contain `await`, `LabelC` or a `slide`; `Input/Deck.agda` says "commands are awaited only at the top of a body".  That well-formedness is the type of
  a shape field.  A single `Prog`-sum with recursive positions would admit `await` inside a column and nested slides; strict
  positivity is the second reason.  Equally `DeckC ⋆ ⊤` forbids a slide inside a slide.
* **`TimeC` has no leaf operations.** Duration, windows, `Par` overlay are decided by `TimeC` alone; `Scene A` for any `A` (`Scene (Scene A)`
  for decks) is a free-monad fact, not a sum-signature fact.
* **`Nav ⊎ C` vs `S b`.** `Supports` is a partial embedding between *sets of awaited commands*; a single sum signature would not have the
  partiality (`inj : Nav ⊎ C -> Maybe S`), which is why `lowerOp` is a lowering `ProgC -> ProgC` and not a CM.

What the separation loses, i.e. injections that are Kleisli/CM maps today but unstated (V that they are absent):

* `BlockC ⇒ ProgC (Shape BlockC)` without elaboration (`inl`-style, `pause` kept as a block command): main has only `toProgC` on `BlockAwaitC`
  and `elabL`; the pure inclusion `Body -> Prog` is not named (≈ 6 lines, CM).
* `LayoutC ⇒ BlockC` (`inr`) is never used: `Lower.block` writes `impure (inj₂ (layout sh) , pure)` by hand (`Lower.agda:108`).
* `AwaitC X ⇒ ProgC X`, `LabelC ⇒ ProgC X`: `awaitIn` exists only into `BlockAwaitC` (`Deck.agda:55`).
* `Anim ↪ Scene A` as a *monad* statement: `Scene` is the free monad on `TimeC`, `Anim = Scene Tmpl` is a `Scene` at a leaf type; `fmap`
  along `Tmpl -> Tmpl` (restyle a template, `discrete`) is a monad-functor action, with `footprint` invariant (`names-discrete`) but the
  functor laws for `fmap` on `Scene` (`>>= pure ∘ f`) are not stated as such (`foldS-bind` covers it by instantiation) (I).
* `Diagram -> Anim` is `pure` (A7): it *is* the unit of the monad, so unit-law facts (`foldS` of `pure`) are definitional, but nothing
  names it as a map `Dia ℕ -> Anim` with its laws (G1).
* `Prog -> Scene` is a **fold, not a Kleisli map** (A21): `show c; k` would need `Par` with the continuation in one branch, and `Lowering`
  grafts the continuation at *every* leaf.  This is a genuine sort difference: `ProgC` is sequential (one continuation), `TimeC` has binary
  `Par`/`Seq`; the relation is through an algebra, so its law is `sceneBy-bind` (G6), not `lower-bind`.

## 5. Efficiency

| gap | cheapest way | what becomes redundant if stated once |
|---|---|---|
| G1 | instance of `fold-mapDia` + `layout-evalO` (generic over scalar homs); no new induction | (I) `AllExact`'s per-leaf `Exact` for `lit`-leaves (part of `Assembly.Continuous:120-132`); informal checks in `Pairs.Properties:33-39` |
| G2 | bespoke ~50 lines; the only gap with no generic route | gives a spec for `Lower.animationFinal` and `Render.render`; nothing deleted |
| G3 | `lower-⋙` + `lower-ret` + map congruence | would justify applying `stripNotes ⋙ diagramPlaceholder` as one pass (`ShowcaseMain:42`) |
| G4 | `lower-fusion` along `flattenStacks` + `fold-hom` on the wrapper | `Plain.renderDeck-length`, `renderDeckBy-cong`, `present-renderDeck` (≈ 35); better: one `deckAlgWith` parametrised by (wrap, stack) and the proofs once |
| G5 | compose existing `sem-bind`, `seq-machine`, `deck-shown`; needs a semantic decision first | the "by positions" workaround in `[ds]` §7 |
| G6 | structural induction, 15-25 lines | `[ds]`-deleted `go-bind` family, `slideK-from`/`rest-from` bind steps in `Input/Slides/Properties.agda:142-162` partly |
| G7, G8, G10, G11 | **generic lemmas in `Container.*`** (≈ 60-80 lines total: `translate-∘`, monoid `fold-bind`, `lower` naturality along a CM) | `MapFusion.translate-∘:126`, `Reveal.renderDeck-bind`, `Common.renderBody-bind`, `Steps.elab-bind`, `Lower.lowerCmdBody-bind`, `toProg-bind` (main; ≈ 80 lines); `lowerCmdBody-lowerDeck`, `steps-lowered`, `scene-lowered` (≈ 45) |
| G12 | one generic ≡-algebra module; every `Slides.*.Properties.Generic`/`pull` becomes an import | 4 `Congruent`, 3 `pull`, 3 `fold-agrees` (≈ 150-250 lines) |

Ordering by (value / effort): G12 and G7/G8 (generic, delete code) first; then G6 and G1 (small, connect DSLs); then G5 after the author
decides accumulate-vs-hide; G2 (the only substantial new proof); G4 as a refactor of the two backends.  `deck-scene` already realises the
Prog = `Body⁺` collapse (-61 lines) and `sceneBy`/`perform`; merging it removes A17, A18's second copy, and the main-only parts of G10.
