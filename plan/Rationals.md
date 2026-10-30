# Scalar models with non-canonical representatives

Goal: the scalar theories (Core, Space, Time, Coupling, Hom, the Nat and Rat models) admit models
whose elements have no canonical form, chiefly unnormalised rationals, which defer the gcd.
Everything stays parametric in the scalar; adding a model changes no existing model or deck.

## Steps
1. **Measure first.**  Is the cost gcd/normalisation, or something else?  If not, stop and report.
2. **Carry the equivalence.**  A theory record gets a carrier equivalence and states its laws
   up to it, with a congruence law for every operation.  Prefer the least invasive route: the
   equivalence is a parameter, propositional equality is its default instance, so the current
   API is the special case and callers keep working.
3. **Folds into setoids.**  The folds and `pfold` homomorphisms already take a congruence into a
   setoid; make them take the carried one.  Reuse the container setoid-algebra machinery; no
   per-language re-proofs.
4. **The unnormalised model.**  Whole ticks embed as `n/1` with no gcd; the theory laws come
   from the unnormalised rational properties.
5. **Simplify** is embed after normalise (unnormalised to normalised and back): a setoid
   homomorphism, the identity up to the equivalence, and a model homomorphism of the Time,
   Space and Coupling structure.  Say which operations are not preserved, as for the tick
   embedding from the naturals.

## Gates and budget
`make check` after each step; after steps that touch behaviour, all decks, `make test`,
`make test-numeric`, and byte-identical output for the existing decks.  Stop and report when a
step grows by about 150 lines, when the proofs turn into a rewrite of most of the scalar
modules, or when a design decision belongs to the owner.

## Step 1 result (measured; stops the plan)
Machine load 2.0 to 2.7 throughout, Agda 2.7.0.1, `+RTS -A1g`.
- **Typechecking is not slow.**  `Slides.Scalar.Hom` with its dependencies: 7.6 s of which 6.8 s
  is loading and serialisation; no definition above 0.4 s (`monus-max`, a pure ℕ lemma).
  Showcase 9.4 s, Collider 6.9 s, ATLAS 4.2 s, Tensor 5.8 s, all dominated by loading.
- **Running Collider is slow: 39.4, 39.6, 39.9 s** (Showcase 0.1 to 0.2 s).  A sampling profile
  of the compiled `ColliderMain`: of 10.6k busy samples, GMP routines (all integer arithmetic,
  gcd included) are 3.5%; the rest is closure application and decidable equality on strings,
  characters and lists.  Collider uses no Bézier easing.
- So neither the ℚ normalisation nor a ℚᵘ model would move either number.  The setoid rewrite
  stays worthwhile only as a design goal (non-canonical models), not as a speed-up.
