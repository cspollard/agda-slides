# User input: commands, programs, machines

Design note for `Slides.Input.*` (Stage 1 of `plan/Unify.md`). Input is a parameter of the
program: a program names the commands it awaits, a backend says which it supports.

## Programs

* `Slides.Input.Nav`: `Nav = next | prev | first | last | goto n | gotoLabel s`, with
  decidable equality. Every deck requires it.
* `Slides.Input V` (`V` the scene vocabulary, one continuation each; for `Slides.Core`
  take `V = Shape BlockC`): containers `SceneC V`, `AwaitC C = C ▷ ⊤`, `LabelC = String ▷ ⊤`,
  `ProgC C = SceneC ⊎ AwaitC C ⊎ LabelC`, `Prog C A = ProgC C ⋆ A`, and `Deck C A = Prog (Nav ⊎ C) A`.
  Smart constructors `show`, `await`, `label`, `pause = await (inj₁ next)`, `_⨾_`.
  Moving a program to a backend's vocabulary is a lowering (below).
* One sequential control program. There is no parallel node (`‖`) yet.

## Machines

`Slides.Input.Machine`: `Machine C` = state, init, `step : State → C → State`, `view : State → List V`.
`sem l` is the Kleisli fold of the program algebra (`show` adds to the view, `await c` waits for
`c` and ignores other commands, `label` does nothing); `machine = sem (λ _ → idle)`.
Machines are equal up to `MIso` (state bijection preserving init, step, view). Laws
(`Machine.Properties`): `sem-bind` (the fold is a monad morphism), `seq-machine`, `await-seq`, and
the `liftE-*` facts about the decoder adapter `liftE` that `lower-sound` uses.

`Slides.Input.Navigation`: `prev`, `goto`, `first`, `last`, `gotoLabel` are not awaited by the
program; `navM M len table` keeps a position (number of `next`s taken) and shows `M` replayed
by that many `next`s (history by replay). `labelTable p l` is the number of `await next`
before `label l` (first occurrence wins); `nextCount p` is the last position; `navDeck`
packages them. Laws (`Navigation.Properties`): `labelTable-label`, `labelTable-next`,
`gotoLabel-goto`, `view-next`, `prev-next`. `navM` is the abstract semantics of `goto` and
`gotoLabel`; backends need not agree with it on jumps (see "Conformance: decision").

## Backends: Supports, lowering, binding

`Slides.Input.Supports`: `Supports C` has a backend vocabulary `S` (decidable), a partial
embedding `inj : Nav ⊎ C → Maybe S` and the decoder `dec : S → Maybe (Nav ⊎ C)`, inverse to
each other where defined. `NavTotal` says all of `Nav` is supported; `present` requires it, so a
backend without `Nav` (`printS`, `¬NavTotal-print`) rejects decks. `lowerDeck` (a
`Container.Lowering.lower`) keeps scenes and labels, renames a supported `await k` to
`await (inj k)` and *skips* an unsupported one: the documented default. `skipDeck` is that
default in the generic vocabulary. `Supports.Properties`: `lower-sound` (for every deck, the
backend machine is the generic machine of `skipDeck p` seen through `dec`) and
`lower-supported` (all awaits supported: the same behaviour as `p`).

`Slides.Input.Binding` (the one binding vocabulary): a backend reads a physical input as a command
by *kind*: `on ks s` is a decoder `I → Maybe S` (so families such as `goto n` or `#/n` are
expressible), `choice` combines kinds by `_⊕_` (first match wins). A conflict is an input that two
kinds decode; `Disjoint` rules it out and `disjoint?`/`disjoint*?` decide it over a finite list of
inputs. `choice-∈`, `bind-kind` (`Binding.Properties`): disjoint kinds lose nothing.
`Supports.command b r` reads an input with `r : Decoder I (S b)`, then decodes it with `dec`;
`command-render` (`Supports.Properties`) is the round trip.

## Decks that await

`Slides.Core.Body` is unchanged (`pause` is still a layout command), so no deck changes. The
stratified wrapper is `Slides.Input.Deck`: `BlockAwaitC X = BlockC ⊎ AwaitC X ⊎ LabelC` (a body may carry `label l`; `toProgC` maps it to `Slides.Input`'s `label`),
`DeckBlockC C = BlockAwaitC (Nav ⊎ C)`, `Body⁺ X`, and `toProg : Body⁺ X → Prog X ⊤` (scenes `Shape BlockC`), so `Supports.lowerDeck` applies to a body.

* `Slides.Steps.Input`: `elab` (`pause ↦ await next`, a Kleisli lowering), and the second pass
  `stepsBy step?` (mode, `afterBy`) where `step?` says which awaited commands are steps: `isNext`
  for `Nav ⊎ C`, `isNextS b` (decodes to `next`) for a backend vocabulary.
* `Slides.Lower`: `lowerCmd b` (supported renamed, unsupported skipped), `lowerCmdBlock`,
  `lowerCmdBody`. Awaits occur only at body level, so nothing else is touched. Lifting both
  passes to whole decks (a clause per slide constructor) is left to the step that presents a deck.
* Laws: `Slides.Steps.Properties` (`stepsBy-elab : stepsBy isNext (elab b) ≡ steps b`, `goBy-bind`,
  `go-bind`, `go-bind-elab`, `elab-bind`); `Slides.Lower.Properties` (`lowerCmdBody-bind`,
  `lowerCmdBody-lowerDeck`, `steps-lowered`, `steps-pipeline`).

## Slide labels

A physical `goto` addresses a *slide* (`#/intro`, `#3`); `navM`'s `goto k` is a *position* (a count of `next`s). The bridge is a label at the start of every slide, `Slides.Input.Slides`:

* Authoring: `slideAs "intro" body`, or `labelled "intro" opts` in `slideWith`/`stackWith` (`SlideOptions.label`; a stack's label names its first slide). Labels are opt-in: unlabelled decks are unchanged.
* `slides d` lists the slides (a stack flattened, as plain does); `deckBody`/`deckProg d` is one program: per slide `label (autoLabel i)` (the numeral of `i + 1`, plain's `#n`), the user label, the elaborated body, and an `await next` between consecutive slides. `labelTable (deckProg d)` and `navDeck` then do slide-addressed goto through the position machine.
* `Slides.Input.Slides.Properties`: `slide-table` (`labelTable (deckProg d)` is the first match in the independent list `entries`: slide `i` starts after the pauses and `next`s of the earlier slides) and `auto-start` (the label of slide `i` resolves to `startOf`, when no user label is a numeral: `Fresh`). New sequencing laws in `Navigation.Properties`: `nextCount-bind`, `labelFrom-bind`. Examples by `refl`: `Slides.Input.Example` (`Slides.Examples.Labels`).
* Caveat: a `pause` is one `await next` in the machine but `Slides.Steps` wraps each later command in its own fragment, so machine positions are not physical fragment indices; the table is exact for slides (the ordinal), not for fragment steps.
* Hashes: reveal reads `#/id` as `gotoLabel id` (`Hash.named`; round trip `reveal-render`); plain reads `#n` only (`plain.js` is a golden asset), so it has no label hash. The slide's `id` is produced for now by `Slides.Lower.labelMounts` (an empty `div#id` at the start of a labelled slide; reveal resolves the id to the enclosing section); the intended home is `slideAttrs` (`Backend.Common`: `opt "id" (SlideOptions.label o)`, the outer section of a labelled stack). Test: `make labels test-labels` (`tests/browser/labels.mjs`).

## Backend bindings

How a physical input becomes a command (the modules are `Slides.Backend.{Input,Reveal.Supports,Plain.Supports}`; their laws are in the `.Properties` modules).

* `Slides.Backend.Input`: `Event = keydown Key | hashLoad Hash | hashChange Hash`, `Key = KeyName × Mods` (`bare | shift | ctrl`, `ctrl` standing for ctrl and meta), `Hash = flat n | grid h v` (`#n`, `#/h/v`), `Ext = overview | tick`,
  `Mode = linear | stacked`. `on ks s` is one *kind*: the keys `ks` mean `s`. `choice` folds kinds with `_⊕_`.
  `bindKeys`/`bindNames` are `choice` guarded by an instance argument `True (disjoint*? ...)`: the kinds must be pairwise `Disjoint`
  on all (finitely many) keys, decided by computation, so a clash is "No instance of type" (`tests/negative/TwoCommandsOneKey`).
  `bind-kind` (`Binding.Properties`): no kind is shadowed.
* `revealSupports`, `plainSupports : Supports Ext` (any `V`). Reveal: vocabulary `RCmd = Nav ⊎ Ext ⊎ Move ⊎ (ℕ × ℕ)` (the grid moves `right left down up` and the vertical goto `slideV h v`,
  which have no `Nav ⊎ Ext` meaning: `dec` is `nothing`); `revealKeys : Mode → Decoder Key RCmd`, `revealHash`, `revealRead`, `revealRender` (canonical input per command).
  Plain: `PCmd = Nav ⊎ ⊤`, `plainKeys : Decoder KeyName PCmd` (key *names* only: modifiers cannot matter by construction), `plainHash`, `plainRead`, `plainRender`; `await overview` is skipped.
  Gaps by design: `tick` has no physical input yet (`render = nothing`), and neither has plain's `gotoLabel` (reveal's is `#/id`, see "Slide labels"); alt-modified keys (reveal's skip-fragments) are not modelled.

What the two backends do differently (pinned by `tests/browser/nav.mjs`; a table, not theorems, because nothing depends on it):

| | reveal | plain |
|---|---|---|
| modifiers | Shift+Space is `prev`; Ctrl and meta disable every key | `e.key` only: Shift+Space is `next`, Ctrl+ArrowRight is `next` |
| ArrowDown | linear deck: `next`; stacked deck: the grid move `down` (no `Nav` command) | `next` |
| `#n` | zero-based, `#n = #/n`; `#/h/v` read | one-based and flat, read on load only; `#/h/v` not read |
| `hashchange` | navigates | ignored |
| overview | `o`, Escape | none (`await overview` is skipped) |
| fragments after a jump | `first`, `goto`, `gotoLabel` backwards land on a slide shown full, forwards fresh (reveal shows the fragments of every slide before the current one); `last` lands fresh | `first`, `goto`, `gotoLabel` land fresh, `last` full (`show(i, revealAll)`) |

Both support all of `Nav` (`revealSupports-total`, `plainSupports-total`); each key table is conflict-free and no kind is shadowed (`revealKeys-kind`, `plainKeys-kind`), and the canonical input of each command reads back as that command (`reveal-render`, `plain-render`, `command-render`).

## Conformance: decision

Backends do **not** have to interpret inputs identically. `navM` (the replay machine) is the *abstract* semantics of `goto` and `gotoLabel` (a position is the number of `next`s taken, history by replay), and `next`/`prev` are exact in every backend (they are what `pause` means and what the animation player steps on). A backend is free to differ on jumps, modifiers and hash grammars, as the table says; no theorem relates a backend to `navM` beyond the lowering soundness above. (An earlier draft proved per-backend "conformance" statements and proposed a slide-equality relation for jumps; it was dropped because nothing depends on it.)

Two things the deck side (steps 2, 5-7) still has to settle: (a) physical `goto` is by *slide* (`#/h`, `#n`) while `navM`'s `goto k` is by *position*, so the lowering must give the slide table, best as a `label` per slide; (b) reveal's grid moves and the vertical goto have no `Nav` meaning, they are reveal extensions. The mode (`linear` or `stacked`) is a property of the deck (does it contain a `stack`), chosen when presenting.

Step 6 on paper (not implemented, no output changes): for reveal, `Reveal.initialize` receives a `keyboard` map only for keys where a deck's binding differs from `revealKeys`; for the default binding the map is empty and `init.js` is byte-identical. Plain keeps its key table in `assets/plain.js` (byte-exact golden); a test would extract the `e.key` names of `plain.js` and compare them with the decoded kinds of `plainKinds` (generating `plain.js` from them is Stage 5 and changes the golden once).

## Deferred

* `‖` (parallel programs at `C₁ ⊎ C₂`): needs a `ParC` node with a join; the product lemma
  `machine (p ‖ q) ≅ machine p ⊗ machine q` is in the spike branch.
* Choice (needs the offered commands in the shape; `OnC` is not covariant).
* `tick` is an ordinary command; the clock is not built.
* Parameterised bindings beyond labels: `goto n` and `gotoLabel s` are Nav kinds; other
  families are decoders.
* Strict absence and time (Stage 2).
