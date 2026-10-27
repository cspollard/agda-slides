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
  A map of commands `C → D` is a container morphism `mapC`, so `mapP` is
  `Container.Lowering.translate`.
* One sequential control program. There is no parallel node (`‖`) yet.

## Machines

`Slides.Input.Machine`: `Machine C` = state, init, `step : State → C → State`, `view : State → List V`.
`sem l` is the Kleisli fold of the program algebra (`show` adds to the view, `await c` waits for
`c` and ignores other commands, `label` does nothing); `machine = sem (λ _ → idle)`.
Machines are equal up to `MIso` (state bijection preserving init, step, view). Laws
(`Machine.Properties`): `sem-bind` (the fold is a monad morphism), `seq-machine`, `await-seq`,
`lift-lemma` (`mapP f` is invisible up to the decoder adapter `liftE`).

`Slides.Input.Navigation`: `prev`, `goto`, `first`, `last`, `gotoLabel` are not awaited by the
program; `navM M len table` keeps a position (number of `next`s taken) and shows `M` replayed
by that many `next`s (history by replay). `labelTable p l` is the number of `await next`
before `label l` (first occurrence wins); `nextCount p` is the last position; `navDeck`
packages them. Laws (`Navigation.Properties`): `labelTable-label`, `labelTable-next`,
`gotoLabel-goto`, `gotoLabel-view`, `view-next`, `prev-next`.

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

`Slides.Input.Binding`: a backend reads a physical input as a command by *kind*: one decoder
`I → Maybe S` per kind (so families such as `goto n` or `#/n` are expressible), combined by
`_⊕_` (first match wins). A conflict is an input that two kinds decode; `Disjoint` rules it out
and `disjoint?` decides it over a finite list of inputs; `conflict?` is the finite-table case
(`S → I` injective). `⊕-left`, `⊕-right` (`Binding.Properties`): disjoint kinds lose nothing.

## Decks that await (port steps 1-3)

`Slides.Core.Body` is unchanged (`pause` is still a layout command), so no deck changes. The
stratified wrapper is `Slides.Input.Deck`: `BlockAwaitC X = BlockC ⊎ AwaitC X`,
`DeckBlockC C = BlockAwaitC (Nav ⊎ C)`, `Body⁺ X`, `DeckC⁺ X` (slides whose bodies are `Body⁺ X`),
and `toProg : Body⁺ X → Prog X ⊤` (scenes `Shape BlockC`), so `Supports.lowerDeck` applies to a body.

* `Slides.Steps.Input`: `elab` (`pause ↦ await next`, a Kleisli lowering; `elabDeck` slide by
  slide), and the second pass `stepsBy step?` (mode, `afterBy`, `hasStep`) where `step?` says
  which awaited commands are steps: `isNext` for `Nav ⊎ C`, `isNextS b` (decodes to `next`) for a
  backend vocabulary. `stepsDeck` lifts it to decks.
* `Slides.Lower`: `lowerCmd b` (supported renamed, unsupported skipped), `lowerCmdBlock`,
  `lowerCmdBody`, `lowerCmdDeck`. Awaits occur only at body level, so nothing else is touched.
* Laws: `Slides.Steps.Properties` (`stepsBy-elab : stepsBy isNext (elab b) ≡ steps b`, `goBy-bind`,
  `afterBy-bind`, `after-∨`, `hasStep-bind`, `go-bind`, `go-bind-elab`, `elab-bind`);
  `Slides.Lower.Properties` (`lowerCmd-supported/unsupported`, `lowerCmdBody-lowerDeck`,
  `steps-lowered`, `steps-pipeline`).

## Deferred

* `‖` (parallel programs at `C₁ ⊎ C₂`): needs a `ParC` node with a join; the product lemma
  `machine (p ‖ q) ≅ machine p ⊗ machine q` is in the spike branch.
* Choice (needs the offered commands in the shape; `OnC` is not covariant).
* `tick` is an ordinary command; the clock is not built.
* Parameterised bindings beyond labels: `goto n` and `gotoLabel s` are Nav kinds; other
  families are decoders.
* Strict absence and time (Stage 2).
