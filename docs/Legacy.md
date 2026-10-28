# Consulting the legacy implementation

The previous implementation (18.4k lines of source, 40 modules of proofs) is preserved, not
deleted.
- Git tag `legacy`; read-only checkout at `../agda-slides-legacy` (detached HEAD, do not edit).
  Read files there with the normal tools; no `git show` needed.
- Unmerged spike tags: `archive/stage2-ordered`, `archive/stage2-assembly`,
  `archive/stage4-spike`, `archive/spike-timed`, `archive/deck-scene` (WIP, chunk semantics for
  pause; worktree `../agda-slides-deck`), `archive/relations-audit`.
- Orientation in the legacy tree: `docs/Map.md` (namespaces), `docs/Relations.md` (arrows
  between languages and the gaps found), `docs/Time.md` (time domains and literature),
  `plan/Simplify.md` (the diagnosis behind the rebuild).

## Protocol
1. Do not read legacy code to learn the design: `docs/Objects.md` is the design.
2. When a step needs a fact the legacy already proved, look it up below, read only that
   module, and port the statement against the new definitions.  Port a proof only if it states
   something the new design still needs; otherwise leave it behind.
3. Never copy a definition across; re-derive it from the new objects and compare.

## Where the proofs are (expectations, not audits)
| Topic | Legacy location | Expected to carry over |
|---|---|---|
| Free monad, folds, lowerings, sums | `Container/**` | yes: kept as is; add the generic bind-law and fold-congruence lemmas here |
| Layout laws, validity, naturality in the scalar | `Slides/Diagram/Place/Properties/{Laws,Valid}`, `Diagram/Layout/Properties` | statements yes, proofs re-done against Space |
| Ordered scalar layer, faithfulness of ℕ in ℚ | `Slides/Diagram/Ordered*`, `Diagram/NatQ` | the lowering ideas, as Space/Time/Coupling lowerings |
| Diagram syntax maps (map fusion) | `Slides/Diagram/Syntax/Properties/MapFusion` | yes, becomes a generic container-morphism lemma |
| Names soundness | `Slides/Diagram/Names/Properties/Soundness` | yes |
| Temporal container, sampling, assembly | `Slides/Anim/{Syntax,Sample,Assembly*}`, `Slides/Time*` | the skeleton laws; assembly restated on events |
| Tracks and easing | `Slides/Anim/Track*` | replaced by Coupling terms |
| Shipped parametric encodings | `Slides/Anim/{Share*,Formula*,Param*,Phases*}` | no: left behind (see Objects.md, shipping) |
| Input machine, navigation, labels | `Slides/Input/**` | machine laws yes |
| Deck vocabulary, pause elaboration | `Slides/{Core,DSL,Steps,Lower}*` | restated for deck as scene of scenes |
| Backends, HTML, shared proofs | `Slides/Backend/**` | one shared deck algebra |
| Examples and goldens | `Slides/Examples/**`, `tests/golden` | the acceptance suite (goldens kept here) |

## Tooling notes carried over
Worktrees need a plain copy of the parsnip contents (not nested, no `.git`); never `git add -A`;
`npm install` in `tests/browser`; Bash calls cap near 2 minutes, so run long builds in the
background with a log; BSD sed has no `\?` (use `sed -E`, or Python); never mask failures
with `|| true`.
