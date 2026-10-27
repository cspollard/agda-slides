# Bloat audit of the Stage 1 code (branch `stage1-simplify`, from `stage1-input`)

Standing rules: `--safe --without-K`, principled (Containers, FreeMonads, Algebras), keep the laws
that justify the design, proofs in `X.Properties` (executables never import them), no instance
search in core, no postulates. New decision: **backends need not interpret inputs identically**.

Measure: `find src -name '*.agda' | xargs cat | wc -l` was 16052 on `a61d970` (before Stage 1),
19131 on `stage1-input`, 17883 after this audit (Stage 1 added 3079 lines of Agda, now 1831).

## Finding 0: nothing executable uses Stage 1

No `*Main` module imports `Slides.Input*`, `Slides.Backend.{Input,Reveal.Supports,Plain.Supports}`
or `Slides.Steps.Input` (`tests/check_closure.py` closures are unchanged, generated output is
untouched). Stage 1 is a checked design with no consumer yet, so a module earns its place only by a
theorem that justifies the design, a negative test, or because a later stage (2, 5-7 of
`plan/Unify.md`) needs it. "Needed later" is not enough on its own: what a later step needs and
does not already have is a few clauses to re-add.

## Per module (before lines; verdict; after lines)

| module | used by | verdict |
|---|---|---|
| `Input` 81 | everything below | keep; `mapC`/`mapP` removed (lift-lemma was their only user, and `lower-sound` subsumes it) 65 |
| `Input.Nav` 60 | all | keep; DecEq quadratic in constructors (30 clauses) is now a retract through `Slides.DecEq` 55 |
| `Input.Machine` 67, `.Properties` 166 | `Supports.Properties` (`lower-sound`), `Navigation` | keep: `sem-bind`, `seq-machine`, `await-seq` justify the fold; `liftE-*` are `lower-sound`'s lemmas; `lift-lemma` removed 151 |
| `Input.Navigation` 78, `.Properties` 84 | `Example` and its own laws only | keep (see below); `nextCount`/`labelFrom` use one `δ` clause, `labelFrom-shift` 9 clauses to 1, `gotoLabel-view` (a restatement of `gotoLabel-goto`) removed 81 + 73 |
| `Input.Supports` 90, `.Properties` 107 | `Lower`, `Steps.Input`, Reveal/Plain supports | keep (`lower-sound`, `lower-supported` are the plan's "lowering is sound"); now also holds `command` / `command-render` 95 + 116 |
| `Input.Binding` 53, `.Properties` 22 | Backend.Input, negative tests | merged vocabulary: `on`, `choice`, `disjoint*?` moved here; unused `conflict?` and `⊕-right` removed; `choice-∈`, `on-∈`, `bind-kind` 61 + 45 |
| `Input.Deck` 62 | `Steps.Input`, `Lower` | keep `BlockAwaitC`, `DeckBlockC`, `Body⁺`, `toProg`; `DeckShape⁺`/`DeckC⁺`/`Deck⁺` had no user 50 |
| `Input.Example` 66 | nothing (checked by `refl`) | keep: the only check that `navDeck` computes; the `Real` module (unused) removed 55 |
| `Backend.Input` 236 | Reveal/Plain supports, negative tests | keep; `on/choice/disjoint*?` moved out; `decVia` is `retract-dec` 220 |
| `Backend.Input.Properties` 49 | Reveal/Plain properties | removed: `choice-∈`/`on-∈` moved to `Binding.Properties`; `∀-names`, `isNothing?` only served `ctrl-ignored` (a fact, now a doc table) 0 |
| `Backend.Command` 18, `.Properties` 22 | Reveal/Plain properties | inlined into `Input.Supports` (`command`) and `.Supports.Properties` (`command-render`) 0 |
| `Backend.Conformance` 58, `.Properties` 131 | nothing | removed: the conformance decision makes it unnecessary; the cross-backend facts duplicated the per-backend ones 0 |
| `Backend.Reveal.Supports` 151, `.Properties` 121 | negative control | keep tables and laws (`revealKeys-kind`, `reveal-render`, `reveal-command`, `revealSupports-total`); the 9 "what reveal does" theorems (modifier, ArrowDown, hash, hashchange) are `refl` facts nothing depends on: now a doc table, pinned by `nav.mjs` 151 + 83 |
| `Backend.Plain.Supports` 87, `.Properties` 90 | negative control | same 87 + 50 |
| `Steps.Input` 96 | `Lower.Properties`, `Steps.Properties` | keep `elab`, `goBy`, `stepsBy`, `afterBy`, `isNext(S)`; `elabDeck`, `stepsDeck`, `hasStep` had no user 82 |
| `Steps.Properties` 200 | `Lower.Properties` (`stepsBy-elab`) | keep `bind-assoc`, `go-bind` (moved out of `Steps`, so executables no longer typecheck proofs), `goBy-bind`, bridge (`stepsBy-elab`, `go-bind-elab`); removed: dead `bind-assoc⁺` (the two copies of `bind-assoc`: the `Body⁺` one was never used; the other cannot be shared because `k tt` only reduces on a container whose positions are literally `⊤`), `afterBy-bind`, `after-∨`, `hasStep-bind`, `after-elab`, `hasStep-elab-bind` (a "has a step" predicate nothing used) 146 |
| `Lower` +39, `Lower.Properties` +105 | the above | keep `lowerCmd{,Block,Body}` and the laws that connect them to `lowerDeck` (`lowerCmdBody-lowerDeck`, `steps-lowered`, `steps-pipeline`); `lowerCmdDeck`, `lowerCmd-supported/unsupported` (restatements of the definition) removed |
| `Spike/Input/*` 774 | `make check` only | removed (history on `spike-input`) |
| `tests/negative`: `TwoDecodersOneName` + `DistinctNamesOk` 37 | `make test-negative` | removed: the same mechanism (`disjoint*?` instance) as `TwoCommandsOneKey`/`DistinctKeysOk`, with names instead of keys. `NoNavBackend` tests a different thing (`NavTotal`), kept |
| `docs/Input.md` 134, `docs/NavInventory.md` 195, `plan/Unify.md` 358 | readers | `Input.md` is the single source of truth for the design; `NavInventory.md` keeps the inventory of the code before Stage 1, the risks and surprises (port plan and the command table dropped, 195 to 126); the conformance section is a short decision plus a table (134 to 113). `Unify.md` is plan history, left alone |
| `tests/browser/nav.mjs` 322 | `make test-nav` | unchanged: it pins what the browsers do, and is what the doc table cites |

## Challenged items

* **Conformance (189 lines)**: dropped. The decision makes exactness a non-goal. The facts survive as one
  doc table (`docs/Input.md`, "Backend bindings"), pinned by `nav.mjs`.
* **`navM`/`Navigation` as the abstract semantics of `goto`/`gotoLabel`**: kept. It is the only
  definition of what the non-awaited `Nav` commands mean, `labelTable-label`/`labelTable-next` justify
  `label`, and `view-next`/`prev-next` justify history-by-replay. Smaller only by about 15 lines
  (the `δ` clause); a single fold for `nextCount` and `labelFrom` would save about 6 more and
  complicates `labelFrom-shift`, so not done.
* **Two binding vocabularies** (`Input.Binding` vs `Backend.Input`): merged. The generic part
  (`Decoder`, `⊕`, `Disjoint`, `on`, `choice`, `disjoint*?`) is in `Input.Binding`; `Backend.Input`
  keeps the physical types (`Key`, `Hash`, `Event`, `Ext`, `Mode`) and the two checked constructors.
* **`Backend.Command`**: inlined.
* **Reveal/Plain duplicated machinery**: the shared part was the disjointness boilerplate
  (`kinds-disjoint`, `choice-∈` wiring), now one `bind-kind`. What remains (the vocabulary, the read and
  render tables, the `Supports` record with its two inverse proofs) is per-backend data of the same
  shape, not duplicated code; a `fromDec` constructor would save under 10 lines.
* **DecEq via retraction**: `decVia` now delegates to `Slides.DecEq.retract-dec`; `Nav` uses it directly.
* **Two copies of `bind-assoc`**: only the `Body` one was used; the `Body⁺` one is removed.

## Kept despite doubts

* `Navigation` + `Example` (no consumer until labels reach a backend; see above).
* `lower-sound`/`lower-supported` and the `MIso` machinery under them (270 lines): the one lowering
  theorem the plan promised.
* `present`, `NavTotal`, `printS`, `¬NavTotal-print`, `NoNavBackend` and its control: the "a backend without
  navigation rejects decks" requirement.
* `reveal-command`/`plain-command`, `reveal-render`/`plain-render`: the end-to-end round trip through `Supports.dec`.
* `on-∈`: five lines, the specification of `on`; `go-bind-elab`, `goBy-bind`: the plan's "`go-bind` restated as an instance".

## Deferred

* **Keys as data, not an enumeration** (about 110 lines): `KeyName` has 18 constructors, an `idx`/`un`/`un-idx`
  triple, `names` and a triangular `names-cover` only so that `Disjoint` can be decided over "all keys". If a kind carried its key
  list (`List I × S`) disjointness would be "the lists share no element" (decidable from `DecEq I` alone) and
  `KeyName` could be `String` (what `plain.js` reads, `e.key`). That changes `Disjoint`, `bindKeys`
  and both tables; deliberately not done under "safe".
* **`Body⁺`/`Prog` duplication**: a body that awaits exists as `BlockC ⊎ AwaitC X` (for `Steps`) and as
  `ProgC X` over `Shape BlockC` (for `Supports`); `lowerCmdBody` and `lowerDeck` are two lowerings of the same
  thing tied by `lowerCmdBody-lowerDeck`, and `skipOp`/`lowerOp` are near copies. Stage 2 should pick one
  (about 60 lines).
* `Unify.md` section 4b repeats about 70 lines of `Input.md`; trim when the Stage 2 plan is written.
* Lifting `elab`/`stepsBy`/`lowerCmdBody` to whole decks was removed, not replaced: one clause per slide
  constructor when "present" needs it.
