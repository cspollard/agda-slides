# An ordered layer for the scalar signature (Stage 1b / scalar side of Stage 2)

**Landed (branch `ordered-migration`, M1 to M3).** The design below is as built, with these
changes against the spike: (1) the signature is split in two, `OC = ExprC ⊎ OrdC ⊎ FloorC` (the
layers ℕ and ℚ both read; `OExpr`, `OOps`, the language of every template) and `QC = OC ⊎ EaseC`
(ℚ only), because a template must be evaluable in ℕ (the flipbook, the assembly proofs) and
`Ease` has no ℕ reading; templates are `Dia (OExpr ⊤)` and `Ease` stays a node of the shipped
formulas and of `QExpr` for M4; (2) the lowering is a Kleisli endomorphism of `OC`
(`lowerO`), with the monus as `(a ⊔ b) − b` instead of `max (a − b) 0`: the minuend is the larger
by construction, so a lowered term is `FaithfulO` at every assignment (`faithful-lower`), and
`Pct p x` is `DivBy 99 (MulLit p x)`; (3) models are explicit records (`OOps`, `QOps`: `natO`,
`ratO`, `ratQ`) with laws `QLaws`; (4) `discrete d` is a function, not a constructor:
`template (mapDia (λ e → lowerQ e >>= λ _ → holdT) d)`; `Euclid`, `DParam`, `DPhases`, the
`D` flag of the player and the second set of Properties are gone (`plan/Unify.md` 4c).
Modules: `Slides.Diagram.Ordered` and `.Properties{,.Discrete,.Faithful,.Laws}`.

Status: design and spike, branch `stage2-ordered`; nothing in `src/Slides` outside `Spike/` is
changed. Spike modules (all `--safe --without-K`, no postulates, no holes, no instance search
beyond `NonZero` literals, none imported by an executable):

| Module | Lines | What |
|---|---|---|
| `Slides.Spike.Ordered` | 243 | the layers `OrdC`, `FloorC`, `EaseC`, their handlers, `QC`, `evalQ`, the ℚ reading `ratQ`, the translations `toQ` (container morphism) and `lowerD` (lowering) |
| `Slides.Spike.Ordered.Properties` | 156 | `ι` against the new operations (`ι-*`, `ι-<ᵇ`, `ι-⊓`, `floor-ι`, `ι-divBy`, `ι-modBy`, `ι-mulLit`, `ι-monus`, `ι-pct`), `IsOrdHom`, `IsFloorHom`, `ι-ord`, `ι-floor` |
| `Slides.Spike.Ordered.Properties.Discrete` | 91 | discrete templates are ℚ templates at ticks: `faithful-D` (with side conditions) and `discrete-is-ordered` (none) |
| `Slides.Spike.Ordered.Properties.Laws` | 189 | free-monad laws, fusion (`foldT-bind`, `foldT-lower`), `evalQ-hom`, continuous templates embed, `Ease` laws, sample-and-hold and loops |

Cold check times (`/usr/bin/time -l`, Agda 2.7.0.1, `-A1g`, dependencies cached; each figure
includes about 3.5 s to load the standard library): 4.0 s / 8.3 s / 5.2 s / 4.8 s, peak 1.7 to
2.4 GB. About 6 s of real checking in all.

## 1. The design

The scalar signature stays layered, `Term Σ V = Σ ⋆ V`, layers combined by `_⊎_`, each layer read by
its own record of operations and the sum by the copairing `_⊕_`. Three layers are added:

```
OrdC    Lt a b x y   x if a < b else y          Min a b
FloorC  DivBy d x    ⌊x / (d+1)⌋                ModBy d x   x − (d+1)·⌊x/(d+1)⌋       MulLit n x   n·x
EaseC   Ease e x     Slides.Anim.Track.progress e x
QC      = ExprC ⊎ (OrdC ⊎ (FloorC ⊎ EaseC))          QExpr V = Term QC V
```

The names and arities of `Lt`, `DivBy`, `ModBy`, `MulLit` are those of `EuclidC`, so the
operations of `Euclid` are the new layers' operations read in ℚ instead of ℕ. The ℚ reading
(`ratQ`) is `ratOps` plus: `lt` by the strict comparison `a <ᵇ b = not (b ≤ᵇ a)`, `min = ⊓`,
`divBy d x = ⌊⌊x⌋ / (d+1)⌋` (integer floor division, an integer-valued scalar), `modBy` the real
remainder `x − (d+1)·divBy d x` (so a loop is smooth in fractional time), `mulLit`, and
`ease = progress`. `Floor` is `DivBy 0` and `Clamp lo hi` is `Min hi (Max lo x)`: neither is a
primitive.

A term is a *time-varying scalar*: the variable is the time (or any other context variable).
Substitution along `τ ↦ e(τ)` is `_>>=_` of the free monad: delay, stretch, reversal, loop
(`loopT d = modByQ d tQ`) and sample-and-hold (`holdT = divByQ 0 tQ`) are Kleisli arrows.

### Which operations are homomorphisms of `ι : ℕ → ℚ`

| Layer | Operation | Status | Where |
|---|---|---|---|
| core | `0`, `Lit`, `+`, `⊔` | homomorphism, no condition | `IsCoreHom`, `ι-+`, `ι-⊔` |
| core | `Pct p` | only if `p·x` divisible by 100 (ℕ rounds down, ℚ is exact) | `Exact%` in `Faithful` |
| sub | `Sub` | only where `b ≤ a` (monus against real difference) | `ι-∸` |
| ord | `Lt`, `Min` | homomorphism, **no condition** | `ι-ord : IsOrdHom natOrd ratOrd ι` (`ι-<ᵇ`, `ι-⊓`) |
| floor | `DivBy`, `ModBy`, `MulLit` | homomorphism, **no condition** | `ι-floor : IsFloorHom natFloor ratFloor ι` |
| ease | `Ease` | **no ℕ reading exists**, so no homomorphism to state | — |

The weaker relation for the two non-homomorphisms of the old layers is a *lowering*
(`Container.Lowering`, a Kleisli map `DExprC → QC ⋆`): `Sub a b ↦ max (a − b) 0` and
`Pct p x ↦ ⌊p·x/100⌋ = DivBy 99 (MulLit p x)`, every other node to its namesake. Then

```
discrete-is-ordered : ι (evalD natD ρ e) ≡ evalQ ratQ (ι ∘ ρ) (lowerQ e)       -- for every e, ρ
```

with no hypothesis (`ι-monus`: `ι (a ∸ b) = (ι a − ι b) ⊔ 0`; `ι-pct`). The structural translation
along the container morphism `dToQ` is also proved (`faithful-D`), with the side conditions
of `Faithful` on core and sub nodes only (`FaithfulD`: the ordered nodes have none); the lowering
is the one to use, since a discrete template means the ℕ value, and `toQ` can be dropped.
For `Ease` the relation is the restriction itself: the ℕ-indexed reading of an ordered term is
`evalQ ratQ (ι ∘ ρ)`, defined for every term; only the `ℕ`-valued reading (`evalD natD`) is
partial, and only for ease-free terms.

### The monad, and layout

`QExpr V = QC ⋆ V` is the stdlib free monad, so `subst` is `_>>=_` and its laws are the generic
`Container.FreeMonad.Properties` ones at `QC` (`qsubst-pure`, `qsubst-assoc`, one line each).
Not re-proved: `subst-bind`, `node-eq`, `subst-assoc` of `Expr.Properties` (about 80 lines) have
no analogue, because `subst` is not a separate evaluator. One generic lemma replaces
`evalWith-subst` and `evalD-substD` for every present and future layer:
`foldT-bind : foldT H ρ (e >>= σ) ≡ foldT H (foldT H ρ ∘ σ) e`, and `foldT-lower` is the same for a
lowering (concretely `Container.Lowering.lower-fusion`). `evalQ-hom` shows evaluation is an
`Ops`-homomorphism (six `refl`s), so `layout-natural` applies unchanged. `weakenQ : Expr → QExpr`
(`evalQ-weaken`) embeds the continuous templates, with the same value, no condition.

### `Ease`

`ease-progress` is `refl`. Proved: `ease-0`, `ease-1` (every easing), `ease-reversal`
(`Ease e (1−a) = 1 − Ease (reverseE e) a`, the existing `reversal`), and for the non-Bézier
easings `ease-range` (`[0,1] → [0,1]`) and `ease-mono`. Not proved: range of a Bézier (it holds
only for control points in `[0, 100]`; overshoot is allowed), and monotonicity of a Bézier.

### Sample-and-hold, loops

`hold-law : sample (e >>= λ _ → holdT) at q = sample e at (divBy 0 q)`. A discrete (flipbook)
body is the ordered body composed with `holdT`; this is what `units` does today, so `units` need
not be a semantic boundary but a signature term. (`units` clamps negatives; `divBy 0` does not.)
`loop-period`: `modBy d (ι (t + d + 1)) = modBy d (ι t)` on ticks. Not proved: `n`-periodicity for
real time (needs `⌊x + n⌋ = ⌊x⌋ + n`).

## 2. Decisions

1. **Is `floor` in the signature or only at `units`?** In the signature, as `DivBy 0`, because
   `t / 4` and `t mod 64` apply floor to terms *inside* a formula, not only to the time at the
   boundary. At the boundary it becomes a term (`holdT`), by `hold-law`.
2. **`Lt`: Bool or 0/1?** Neither: the select form `lt a b x y`, as `Euclid` and the JS (`[8, a, b, x, y]`)
   have it. A Bool needs a second sort (indexed containers), a 0/1 scalar needs a term-times-term
   product that the signature does not have, and the select form is a homomorphism of `ι` with
   one proof (`ι-<ᵇ`). `lt a b 1 0` is the 0/1 scalar.
3. **Loops** are `d >>= λ _ → modByQ (n−1) τ`: smooth in ℚ, periodic on ticks. `Slides.Anim.Loop`
   keeps the player-stepping lemma (`advance-phase`).
4. **Layout and the monus.** Lower the *leaves* (user formulas) with `lowerQ`, then lay out in
   the real-subtraction ordered scalar: the layout's own differences are exact on valid layouts
   (`Faithful`). Lowering the layout's differences would bloat every shipped coordinate.
5. **JS evaluator (`assets/animation.js` `ev`).** The flag `D` and its two mode-dependent
   branches (`Math.max(0, x−y)`, `Math.floor(x*y/100)`) disappear: the monus and the floor
   percentage are lowered to existing operations. New: `Min` (one code), `Ease` (`[op, e, x]`,
   calling the existing `ease`), and `ModBy` must read `y − x·Math.floor(y/x)` instead of `y % x`
   (they differ only for negative `y`). `DivBy` (`Math.floor(y/x)`), `MulLit`, `Lt` exist.
   `pframe`'s discrete branch (`k = floor t`, `Math.floor(x + 1e-9)`) is replaced by `holdT`
   in the formula. With the signature the single source (Stage 5), the op table is generated.

## 3. What each existing module becomes

Line counts are `wc -l` at `main` (913b291).

| Module | Lines | Fate |
|---|---|---|
| `Diagram/Euclid.agda` | 199 | deleted; its content is `Diagram/Ordered.agda` (the spike's `Ordered.agda` without `toQ`/`dToQ`) |
| `Diagram/Euclid/Properties.agda` | 71 | deleted (`evalD-hom`, `nodeD`, `evalD-substD`, `weakenE-hom`: `evalQ-hom`, `foldT-bind`, `evalQ-weaken`) |
| `Diagram/Euclid/Properties/Layout.agda` | 58 | deleted (layout natural along `evalQ-hom`) |
| `Anim/DParam.agda`, `DParam/Properties.agda` | 73 + 96 | deleted (a discrete segment is a template segment) |
| `Anim/DPhases.agda`, `DPhases/Properties.agda` | 28 + 144 | deleted |
| `Anim/Formula.agda` | 190 | `encD` (13) deleted; `fdiv/fmod/fmul/flt` stay and get ℚ clauses; `Min`, `Ease` nodes added, never folded when closed (`Ease` Bézier in ℚ is a 16-step bisection) |
| `Anim/Formula/Properties.agda` | 493 | about 170 lines (`⟦_⟧ᴺ`, `⟦_⟧ᴰ`, `encD-semN`, `enc-numN`, `half-semN`) replaced by about 40 lines of ℚ clauses |
| `Diagram/Param.agda` | 50 | `DParam`, `AnyParam.discrete` deleted (about 14) |
| `Anim/Render.agda`, `Backend/Diagram.agda` | 116, 367 | the `discrete` branch (about 6 + 25) deleted |
| `Anim/Syntax.agda` | 162 | `discrete`, `tweenD`, the `bodyAt` case (about 10) deleted |
| `Anim/Continuous.agda`, `Footprint/Properties`, `Param/Properties` | | the `discrete` cases (about 3 + 6 + 6) deleted; `Continuous` gains the discrete templates |
| `Diagram/Expr.agda`, `Expr/Properties.agda` | 218, 173 | unchanged in M1 to M3; M5 (optional): `Expr = Term QC`, `subst = _>>=_`, about 80 lines of `Expr.Properties` go |
| `Diagram/Expr/Properties/Faithful.agda` | 192 | unchanged (still the statement for real-subtraction templates; `FaithfulD` not needed) |
| `Examples/PairsHero*` | 176, 166 | `DiscreteOps` becomes `QOps`; frames written once, as now; about 30 touched lines |
| `Anim/Track*` | 191 + ... | unchanged in M1 to M3; M4 only if `Scale` is added (section 5) |
| `assets/animation.js`, `tests/golden/animation.js` | 208 | about −8 +6 |

Estimated change, scalar side only: about **−850 lines deleted** (328 Euclid, 341 DParam/DPhases,
about 110 Formula net of new clauses counted separately, about 70 plumbing), **+590 added**
(spike without the structural translation `toQ`/`dToQ`/`faithful-D`, about 50, and without the
optional Bézier-free `ease-range`/`ease-mono`, about 35; plus about 40 of ℚ clauses in
`Formula`): net about **−220 lines**, about −25 % of the modules touched. Compile time: the
deleted modules cost about 17 s of real checking (`DPhases.Properties` alone about 13 s), the added
about 7 s. These are estimates from line counts and cold checks of the modules involved; nothing
has been deleted yet. Adding the ordered layer alone (M1) is **+680 lines**: the saving appears
only with M3.

## 4. Migration order and gates

Every step: `make check`, `make test`, `make test-negative`, `python3 tests/check_closure.py`,
`tests/golden`, and the browser tests (`tests/browser/anim-ref.mjs`: the JS player against Agda
exactly at ticks and quarter ticks).

- **M1** `Slides.Diagram.Ordered` (+ `.Properties`), unused. Gate: nothing changes (goldens identical).
- **M2** Formula: ℚ meaning for `fdiv/fmod/fmul/flt`, new `Min`, `Ease`; JS: `Min`, `Ease`, `ModBy`
  as floor-mod; `enc` leaves `Ease` unfolded. Gate: goldens change only in `animation.js`; anim-ref
  unchanged.
- **M3** `discrete d` becomes `template (mapDia (λ e → lowerQ e >>= holdT) d)`; delete DParam, DPhases,
  Euclid, the JS `D` flag. Gate: the frame-level corollary of `discrete-is-ordered` (see section 6),
  PairsHero and AnimRef byte-identical frames at ticks and (hold) at quarter ticks; golden decks'
  `data-param` change textually (lowered formulas), regenerate and review.
- **M4** (deferred) `Ease` in templates and `Track` as a derived `Seq` of `Ease` pieces: needs `Scale`.
- **M5** (optional) `Expr = Term QC`, delete the evaluator-based `subst`.

## 5. Risks

1. **`Track` is not yet derivable.** A piece is `from + (to − from)·Ease e (τ/d)` with rational
   endpoints, and `Seq` is a select on time. The signature has no rational literal: `Pct` covers only
   denominators dividing 100. A new core operation `Scale : ℤ → ℕ → Op` (`n/(d+1) · x`, exact in ℚ;
   in ℕ lowered as `DivBy ∘ MulLit`) is needed, and `Lt τ d a b[τ−d]` makes the shipped formulas
   larger than today's piece tables. Not spiked; M4 is therefore not in the recommendation.
2. **`enc` and exact rationals.** Folding closed `Ease`/`DivBy` nodes in Agda must not run the
   Bézier bisection in ℚ (rationals blow up); the folds must be limited to the exact nodes.
3. **Floats.** `ev` computes in floating point; `Floor`/`Mod` of a float near an integer
   (`0.1 + 0.2`) can land on the wrong side. The discrete player guards with `1e-9`; the hold
   substitution needs the same guard, and the quarter-tick browser comparison is the test.
4. **Formula/Properties** (493 lines, one of the slowest modules): the estimate assumes the ℚ
   clauses cost no more than their ℕ twins; if `enc-sem` needs side conditions for the new nodes
   (it does not for `fdiv/fmod/fmul/flt`, whose folds are exact in ℚ on whole numbers) the saving shrinks.
5. **Layout corollary not proved** (section 6): the frame-level statement needs `faithful-layout` for
   lowered leaves.
6. **Shipped size.** Lowered monus (`max (a−b) 0`) is two nodes for one; shared-subformula
   (`Share`) should absorb it, to be measured on PairsHero.

## 6. What is not proved

- The frame-level corollary: laying out the lowered leaves in the real-subtraction scalar and
  evaluating at `ι ∘ ρ` equals the ℕ layout at `ρ`, `ι`-mapped, for valid layouts. Expected from
  `layout-natural` along `evalQ-hom` plus the existing `faithful-layout`; not done.
- Bézier range and monotonicity; periodicity in real time; that the JS computes `evalQ`.
- Nothing is postulated; no `TERMINATING`; no holes.

## 7. Recommendation

**GO** for M1 to M3 (ordered layer replaces `Euclid` and the discrete shipping pipeline, via the
lowering), because: the theorem that makes it one language is proved without hypotheses
(`discrete-is-ordered`), the two languages and the two evaluator modes collapse into one, the net
estimate is about −220 lines and −10 s of checking, and each step has a byte-level gate.
**NO-GO (defer)** for M4 (`Ease` replacing `Track`) until `Scale` and the size of the `Lt`-encoded
`Seq` are measured on PairsHero.

What would change it: if the frame-level corollary (section 6) needs more than about 100 lines;
if `Formula/Properties` grows instead of shrinking (risk 4); if anim-ref cannot stay exact at
quarter ticks once the `D` flag is gone (risk 3); if the shipped data for PairsHero grows more
than about 15 % after lowering (risk 6). Any one of these turns M3 into a NO-GO, and the ordered
layer then stays what M1 makes it: an addition next to `Euclid`.
