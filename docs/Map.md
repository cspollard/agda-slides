# Module map

Read this before opening files: it says what each namespace is for, which modules are on the
critical path of the parametric-time migration (`docs/Time.md`, `plan/Unify.md` 4c/4d), and
which can be parked.  Line counts are approximate (main at the time of writing).  Modules marked
*theory* are proofs no executable imports (`tests/check_closure.py`).

## Namespaces

| Namespace | Role | Lines |
|---|---|---|
| `Container.*` | containers, polynomial functors, `⊎`, free monad, folds (`Interpret`), Kleisli lowerings; the generic algebra every language below is an instance of | 1.8k |
| `Slides.Diagram.{Syntax,Signature,Expr,Ordered,Scalar,NatQ}` | the diagram language and the **layered scalar signature**: core, sub (`Expr`), ordered/floor/ease (`Ordered`), scalars `Ops`, ℕ inside ℚ | 1.5k |
| `Slides.Diagram.{Place,Layout,Draw,Geometry,Names,Delta,...}` | layout algebra into `Layout S`, names, diffs, text metrics; `Place.Properties.*` are the layout laws | 3.5k |
| `Slides.Anim.*` | animations: `Syntax` (free monad), `Track` (easings, pieces), `Continuous`, `Timeline`, `Footprint`, `Render`; shipped data `Formula`, `Param`, `Phases`, `Share`, `SharePhases`; assembly proofs `Assembly.*` (*theory*) | 5.3k |
| `Slides.Input.*` | user input as a parameter: `Nav`, `Machine`, `Supports`, `Binding`, `Deck`, `Slides` (labels) | 1.2k |
| `Slides.{Core,DSL,Components,Steps,Lower,Literals,Math,Resources}` | deck vocabulary (`BlockC`/`DeckC`), `do`-notation, `pause` elaboration, lowerings | 1.0k |
| `Slides.Backend.*` | `HTML`, `Common`, `Diagram` (SVG), `Reveal`, `Plain`, `Input`/`*.Supports`, `Restyle`; `*.Properties` are structural laws | 2.3k |
| `Slides.Examples.*`, `Slides.Driver` | decks and their `*Main` executables; `Pairs`, `PairsHero` are the heavy ones | 2.0k |
| `Slides.Spike.*` | not part of `make check`'s `Everything`; spikes live on branches | — |

Files in `assets/` (`animation.js` evaluator and player, `plain.js`, CSS) are static; the JS
evaluator is tested, not proved.

## Critical path of the time migration

`Container.*` → `Slides.Diagram.{Signature,Expr,Ordered*,Scalar,NatQ}` → `Slides.Diagram.Syntax`
→ `Slides.Anim.{Syntax,Track,Continuous,Timeline,Footprint,Render}` → `Slides.Anim.Assembly*`
→ `Slides.Anim.{Formula,Param,Phases,Share*}`.  Slowest checks (cold, ms, from the last profile):
`Anim.Param.Properties` 96k, `Anim.Assembly.Continuous` 45k, `Anim.Continuous.Properties` 44k,
`Examples.Pairs.Properties` 35k.

The inner loop is `make check-core` (containers, diagrams, animations only).  `make check` is
the gate.

## Parking candidates (leaf proof modules; nothing in `src/` imports them)

`Slides.Lower.Properties`, `Slides.Steps.Properties`, `Slides.Input.Slides.Properties`,
`Slides.Backend.{Common,Plain,Reveal}.Properties`, `Slides.Examples.Pairs.Properties`,
`Slides.Examples.PairsHero.Properties` (about 900 lines).  They state facts about types the
migration changes, so they will need re-deriving on return; parking only defers that and keeps them
out of the way.  Use `make park WHY='...' MODS='A.B C.D'` and `make unpark`
(`tests/park.py`, manifest `park/MANIFEST.md`).  `make test` fails while anything is parked, so a
parked module cannot reach `main`.  Park on the migration branch, never on `main`.

## Briefing agents

Every task given to a coding agent must say: read `docs/Map.md` first, work in a worktree, use
`make check-core` while iterating and `make check` before reporting, and list anything parked.
