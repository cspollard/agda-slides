# Simplifying the library: a proposal for review

Status: proposal, not decided.  Sizes are estimates from reading the code
(`docs/Relations.md` is the evidence); nothing here was compiled.  Literature
is cited from memory unless `docs/Time.md` marks it checked.

## 1. Diagnosis

We kept adding layers (time switch, ordered layer, deck-as-scene) before fixing
the objects and the maps between them.  Result: the same ideas stated several times.

- Drawing primitives exist three times: `Op` (syntax), `Draw` (layout carrier),
  `Element` (+ the `Diagram` record, output).  `Dia` and `Diagram` are mis-named.
- About 275-375 lines of local proofs are hand-written instances of generic lemmas
  already in, or missing from, `Container.*` (`elab-bind`, `lowerCmdBody-bind`,
  `translate-∘`, four `Congruent`, three `pull`, `renderDeck-bind` ...).
- Reveal and Plain share no code but have literally copied proofs.
- About 2.5k lines (`Formula`, `Param`, `Phases`, `Share`, `SharePhases` + proofs)
  exist to ship parametric encodings to a hand-written JS evaluator.

## 2. What we want to capture (five objects, one carrier split)

| Object | Definition | Semantics | Compass |
|---|---|---|---|
| Scalar theory | layered Lawvere theory (core, sub, ord, floor, ease); models ℕ, ℚ; time is a scalar | `ι : ℕ → ℚ` model hom | `docs/Time.md` |
| `Diagram S` | free algebra of the layout signature over scalar `S` | `Layout S`: frame, drawings at resolved positions, anchors (the carrier of the main fold; names, footprint are other folds) | Yorgey (envelopes), Henderson |
| `Scene A` | `TimeC ⋆ A`, `TimeC = Seq, Par, Hold, Delay, Repeat, Drive`, leaves `A` | sparse **events** `(onset, duration, leaf in local time)`, from which `T → Maybe ⟦A⟧` is a fold | Hudak (temporal media, `perform`) |
| `Prog C A` | free monad over `Await C` and scenes | Moore machine `νX. Out × (C → X)`; backends bind a subset of `C` | Hancock-Setzer, Rutten, Elliott |
| Content `BlockC` | leaf carrier of decks (flow content, laid out by the browser) | HTML; **not** `Layout` | the carrier split of `docs/Design.md` |

Animation = `Scene (Diagram Σ)` with a free time variable in the scalar: static
structure, varying scalars, presence windows from `Hold`/`Delay`/`Seq`.  A deck =
`Prog` over `Scene (content)`; `pause` is `Delay 1`.  We keep several specific
types (`Deck`, `Diagram`, `Scene`, `Prog`); what matters is the maps.

## 3. The maps that carry the weight (each stated once, generically)

1. **Kleisli injections** `C ⋆ → (C ⊎ D) ⋆` and **lowerings**: `lower-bind`,
   `lower-⋙`, `lower-fusion` (exist in `Container.Lowering.Properties`).
2. **Folds are algebra homomorphisms**: layout natural in the scalar; events →
   pointwise sampling (events carry relative windows plus a shift action, so
   nested clocks are a monoid-action law); machine fold.
3. **Embeddings with agreement**: `Diagram → Scene` (constant leaf; gap G1,
   ~30 lines), `Deck → Scene (Scene A)` (proved), `Prog → Scene` (`sceneBy-bind`
   missing).
4. **Backends are algebras** over one shared deck algebra core; `Restyle` is a hom.
5. **Model homomorphism** `ι : ℕ → ℚ`; lowerings (`Sub ↦ (a ⊔ b) − b`) where `ι`
   fails to preserve an operation.

## 4. Proposed simplifications (in order of safety)

1. **Generic lemmas first** (pure deletion): a monoid-algebra `fold-bind`
   and a generic ≡-algebra congruence in `Container.*`; re-instance the local
   copies.  About -275 to -375 lines; touches no types.
2. **Names and one primitive vocabulary**: `Dia` → `Diagram`; the output record
   dissolves into `Layout`; `Element` merges into `Draw` (+ `group`, `path`);
   one place converts half-units to printed coordinates.
3. **Events as the temporal semantics** (`perform` with relative windows);
   `Sample`, `Timeline`, `Footprint` become folds of it; assembly is stated on
   events.  Size not estimated.
4. **Shipping**: ship the event list with parametric leaves and generate the JS
   evaluator from the scalar signature (Stage 5); then delete the encoding stack
   piece by piece, keeping `Share` only if page size demands it (measure).
5. **Backends**: one shared `deckAlgWith`; Reveal and Plain differ only in
   their lowering and shell.

## 5. What we choose not to support

- A single-sorted mega-signature (loses well-formedness; indexed containers would
  rewrite `Container.*`).  Specific DSLs related by injections instead.
- Value-dependent FRP (switching on behaviours); program-level `‖`.
- `Track` derived from `Ease` (needs `Scale` and a time-select `Seq`; deferred).
- A generic `Time` parameter beyond the `Clock` record; `blackBox` segments.

## 6. Order and gates

Finish and merge `deck-scene` (gates and docs outstanding) → 1 → 2 → 3 → 4 → 5.
Each step is one agent on one branch, with: measured lines deleted, `make check`
time and memory vs the previous step, goldens byte-identical unless explained,
and the closure check.  If a step adds more than it deletes, stop and report.

## 7. Decisions for the author

1. At deck level, should the machine's view be the accumulated content or the
   visible slide only (`docs/Stage4.md` section 7)?
2. A fade: presence window (in/out) or an opacity scalar?
3. Is a deck a scene over slides (as spiked), with `Prog` only for input?
4. How far to go on step 4 (generated JS evaluator is the largest and riskiest change)?
5. Is merging the `Layout`/`Diagram`/`Draw`/`Element` vocabularies acceptable
   given every deck example touches them (goldens must stay identical)?
