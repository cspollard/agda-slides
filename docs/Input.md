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

## Backend bindings

How a physical input becomes a command (the modules are `Slides.Backend.{Input,Command,Reveal.Supports,Plain.Supports,Conformance}`; their laws are in the `.Properties` modules).

* `Slides.Backend.Input`: `Event = keydown Key | hashLoad Hash | hashChange Hash`, `Key = KeyName × Mods` (`bare | shift | ctrl`, `ctrl` standing for ctrl and meta), `Hash = flat n | grid h v` (`#n`, `#/h/v`), `Ext = overview | tick`,
  `Mode = linear | stacked`. `on ks s` is one *kind*: the keys `ks` mean `s`. `choice` folds kinds with `_⊕_`.
  `bindKeys`/`bindNames` are `choice` guarded by an instance argument `True (disjoint*? ...)`: the kinds must be pairwise `Disjoint`
  on all (finitely many) keys, decided by computation, so a clash is "No instance of type" (`tests/negative/TwoCommandsOneKey`, `TwoDecodersOneName`).
  `Binding.Properties` gets `choice-∈` (`Backend.Input.Properties`): no kind is shadowed.
* `Slides.Backend.Command`: `command b r : Decoder I (Nav ⊎ C)` is `Supports.dec` after the reading `r : Decoder I (S b)`; `command-render` (round trip): if `inj k = just s` and `render s = just i` and `r i = just s` then `command b r i = just k`.
* `revealSupports`, `plainSupports : Supports Ext` (any `V`). Reveal: vocabulary `RCmd = Nav ⊎ Ext ⊎ Move ⊎ (ℕ × ℕ)` (the grid moves `right left down up` and the vertical goto `slideV h v`,
  which have no `Nav ⊎ Ext` meaning: `dec` is `nothing`); `revealKeys : Mode → Decoder Key RCmd`, `revealHash`, `revealRead`, `revealRender` (canonical input per command).
  Plain: `PCmd = Nav ⊎ ⊤`, `plainKeys : Decoder KeyName PCmd` (key *names* only: modifiers cannot matter by construction), `plainHash`, `plainRead`, `plainRender`; `await overview` is skipped.
  Gaps by design: `gotoLabel` and `tick` have no physical input yet (`render = nothing`; hashes for labels are step 7); alt-modified keys (reveal's skip-fragments) are not modelled.

Facts about the two backends, as theorems (each pinned by `tests/browser/nav.mjs`):

| fact | theorem |
|---|---|
| Shift+Space is `prev` in reveal, `next` in plain; plain ignores every modifier; reveal ignores ctrl/meta | `shiftSpace-prev`, `ctrl-ignored`, `plain-ignores-mods`, `shiftSpace-differs`, `ctrl-differs` |
| ArrowDown on a stacked deck is the grid move `down` in reveal (a no-op on a horizontal slide), `next` in plain; on a linear deck reveal agrees | `arrowDown-differs`, `arrowDown-linear-agrees` |
| `#n` is zero-based in reveal (`#n = #/n`), one-based and flat in plain; `#/h/v` is reveal only | `hash-flat-grid`, `plain-hash-one-based`, `hash-differs`, `grid-hash-differs` |
| reveal reads `hashchange`, plain only reads the hash on load | `hashchange-load`, `plain-no-hashchange`, `hashchange-differs` |
| Space, PageDown, PageUp, Home, End agree; the overview is reveal only | `agree-bare`, `overview-only-reveal`, `plain-skips-overview` |
| key tables conflict-free, no kind shadowed, canonical inputs round-trip through `Supports` | `kinds-disjoint`/`plainKinds-disjoint`, `revealKeys-kind`/`plainKeys-kind`, `reveal-command`/`plain-command` |
| both support all of `Nav` | `revealSupports-total`, `plainSupports-total` |

## Conformance

`navM` (the replay machine) is the specification of what a navigating backend shows. Where does a real backend differ?
Both backends keep the *slide* and the *fragments shown on it*; `navM` keeps one number, the count of `next`s, and shows the program replayed by that many.
The table `specEntry`/`plainEntry`/`revealEntry` (`Slides.Backend.Conformance`) records how many of the target slide's fragments each leaves shown after a command.

* `next`: enters a slide with none shown, in all three. `prev`: enters the previous slide with all shown, in all three.
* `first`, `last`, `goto`, `gotoLabel`: the specification lands on a position (`first` = 0, shown none; `last` = `len`, shown all; `goto k` = the start of slide `k`).
  Plain does exactly that (`plain-conforms`).
  Reveal does not: it shows the fragments of every slide *before* the current one and hides those after (`updateSlides`), so its state depends on where you came from.
  A jump backwards (`#/1` from slide 5, Home from slide 5) lands on a slide shown full; a jump forward (`End`, `#/5` from 0) on one shown fresh.
  Probed in a browser: Home from slide 5 with two fragments on slide 0 shows 2 of 2; End from slide 0 with two fragments on the last slide shows 0 of 2. Pinned today: `#/1` from 5 shows 3 of 3.
  Theorems: `reveal-steps-conform`, `reveal-conforms-off-jumps` (reveal agrees with the specification except on `Jump` commands), `reveal-goto-back` (the deviation), `reveal-goto-fwd`.

**Proposal.** Keep `navM` exact, and define conformance of a backend as *exact on `next` and `prev`, slide-equal on `first`, `last`, `goto`, `gotoLabel`*:
after a jump the backend shows the slide the specification shows, with the fragments of that slide at any progress.
So the specification of a jump is the weaker relation "same slide" (positions `p ≈ q` iff no slide boundary lies between them), not equality of positions; plain happens to satisfy the stronger one.
Why this and not the alternatives:

1. *A stated per-backend deviation* would say the same thing in prose and leave nothing to prove against; the relation is the deviation made precise, and it is the same for every backend (a later one gets it for free).
2. *Making reveal exact* needs the fragment index in the hash (`#/h/v/f`, `fragmentInURL`) or `Reveal.slide(h, v, f)` from our own handler: it changes the hash grammar and `init.js` (goldens) and fights reveal's retained state; and its payoff is small (a viewer who jumps to a slide expects the slide, not a particular fragment).
3. *Making the specification reveal-like* (history-dependent) would make `view` depend on the path, losing `view-next`, `prev-next` and the replay model, to describe one backend's implementation detail.
4. The weakening is confined: steps (the thing `pause` means, and the animation player's `step`) stay exact, so the fragment count of a slide and `lower-sound` are unaffected; only `goto`-like commands are up to the slide.

Two things this leaves open for the deck side (steps 2, 5-7): (a) physical `goto` is by *slide* (`#/h`, `#n`) while `navM`'s `goto k` is by *position* (number of `next`s), so the lowering must give the slide table (slide `i` starts at position `s_i`), best as a `label` per slide, in the way `labelTable` already resolves labels; (b) reveal's grid moves (`right left down up`, `slideV`) and the vertical goto have no `Nav` meaning: on a stacked deck `next` and `prev` traverse the stack as one sequence (Space down the stack first, pinned), the grid moves are reveal extensions outside the specification, and a conforming trace contains specification commands only.
The mode (`linear` or `stacked`) is a property of the deck (does it contain a `stack`), chosen when presenting.

Step 6 on paper (not implemented, no output changes): for reveal, `Reveal.initialize` receives a `keyboard` map only for keys where a deck's binding differs from `revealKeys`; for the default binding the map is empty and `init.js` is byte-identical. Plain keeps its key table in `assets/plain.js` (byte-exact golden); a test would extract the `e.key` names of `plain.js` and compare them with the decoded kinds of `plainKinds` (generating `plain.js` from them is Stage 5 and changes the golden once).

## Deferred

* `‖` (parallel programs at `C₁ ⊎ C₂`): needs a `ParC` node with a join; the product lemma
  `machine (p ‖ q) ≅ machine p ⊗ machine q` is in the spike branch.
* Choice (needs the offered commands in the shape; `OnC` is not covariant).
* `tick` is an ordinary command; the clock is not built.
* Parameterised bindings beyond labels: `goto n` and `gotoLabel s` are Nav kinds; other
  families are decoders.
* Strict absence and time (Stage 2).
