# Rebuild plan

Why: the legacy library grew layer by layer before its objects were fixed (diagnosis in
`../agda-slides-legacy/plan/Simplify.md`).  We rebuild object by object on branch `rebuild`,
against `docs/Objects.md`, consulting the legacy only through `docs/Legacy.md`.

## Rules for every step
- One agent, one worktree, one branch off `rebuild`.  The brief names `docs/Objects.md`,
  this plan and `docs/Legacy.md`, and nothing else to read first.
- Budget: each step states a line budget (below).  A step that exceeds it, or adds more than it
  deletes from the generic library, stops and reports before continuing.
- Report: lines added per module, check time (cold) and peak memory, the list of laws proved
  with their statements, anything postulated or deferred, and the corresponding legacy lines.
- Gate: `make check` clean, no `--allow-unsolved-metas`, no postulates, no `|| true`.  From step 7,
  also the golden and browser gate.
- Proof discipline: lemmas from the laws of the theory, not by computing in ℚ; model facts as
  named hypotheses; generic facts in `Container.*`, never per language.
- Parallelism: steps 2 and 3 are independent after step 1; steps 4 and 5 after both; 6 after 5.

## Status (2026-10-28)
Steps 0 to 4 are done and merged: container lemmas +194 lines (budget 300), scalar theories 700 (700),
Diagram and Layout 1819 (2500), Scene 1490 (2000); `make check` clean, 22 s cold.  Next: Step 5 (Program).

## Steps
0. **Archive and clean (done in the commit that adds this file).**  Legacy tagged and checked
   out read-only; stale branches and worktrees removed; this branch holds only `Container.*`,
   assets, parsnip, goldens, browser tests and the three documents.
1. **Generic lemmas in `Container.*`.**  Bind law for folds into monoids; fold congruence;
   container-morphism action on free monads (map fusion); composition of lowerings.  Budget:
   +300, with the legacy local copies (275 to 375) as the justification.
2. **Scalar theories.**  Space, Time, Coupling as records of operations and laws; ℕ and ℚ
   models; the homomorphism `ι` and the lowerings where it does not preserve an operation;
   the digitisation statement for the discrete fragment.  Budget: 700 (legacy about 1.8k).
3. **Diagram and Layout.**  The free algebra of the layout signature over a Space scalar; the
   placement fold into Layout; one drawing vocabulary; naturality in the scalar; names; SVG as a
   map over the primitive list.  Budget: 2.5k (legacy about 5k).
4. **Scene.**  The temporal signature over leaves with Coupling terms for moving values;
   events as the meaning; pointwise reading, relative windows, shift action; nesting by
   substitution; assembly on events; animation as scene of diagrams.  Budget: 2k (legacy 5.2k).
   Decide fade (window or opacity scalar) here.
5. **Program.**  The free monad with a wait command; the Moore machine; navigation; deck as
   scene of scenes with the pause convention; decide the machine view (accumulated or visible).
   Budget: 1k (legacy 1.2k plus the deck elaboration).
6. **Content and backends.**  Content carrier; the shared deck algebra; reveal and plain
   backends; the event-list shipping format and the generated page evaluator (JS).  Measure page
   size against the goldens before adding any sharing.  Budget: 2.5k (legacy 3.3k plus 2.5k
   encodings).
7. **Examples and the acceptance gate.**  Port the examples (intro, talk, showcase, pairs,
   labels, keys, plain, collider); restore the Makefile targets from the legacy Makefile; goldens
   byte-identical or each difference explained and accepted; browser tests pass; closure check
   (no orphan modules).  Budget: 2k (legacy 2.0k).

Total target about 11k lines against 18.4k.  These are targets from the legacy estimates, not
measurements; revisit after step 2.

## Future plans
- **Setoid equality throughout.**  The scalar theories state their laws with `≡`.  Make the theory
  records setoid-based (laws up to a carried equivalence, folds into setoids via the existing
  `Container` setoid algebras), so that models with non-canonical representatives fit: an
  unnormalised ℚ (numerator and positive denominator, equality by cross-multiplication, normalise
  once at the boundary) defers gcd cost, which made `Hom` exponential when `ι n` was written `n / 1`.
  Do this when a model needs it or after Step 4, whichever is first; not before measuring where
  ℚ arithmetic is slow.  Lighter fixes first: literals in coprime form, fixed-denominator scalars.
- Discharge `PctDigital`; Bézier easing; halving for centring; `Min` and `ModBy` nodes.

## Open items carried over from the legacy work
Image background and slide-number command; inline ASCII documentation for modules as they are
written; PNG and PDF primitives; memory use of the heavy examples; the JS evaluator is tested
against Agda, not proved (the generated evaluator in step 6 makes it one table).
