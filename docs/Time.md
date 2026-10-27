# Time: what each domain supports, and what we want

Status: design note (principles).  It sits in `docs/` because it states what the
code should be measured against; the staged work is in `plan/Unify.md`.
References are marked **[checked]** (bibliographic details confirmed against a
source while writing this) or **[memory]** (cited from memory, to verify before
relying on them).

## 1. The question

Animations, diagrams and decks are being unified as programs over one signature
(`plan/Unify.md`).  Behaviours are terms with a free time variable.  Which set
is "time"?  Today the answer is accidental: layout and discrete templates are in
ℕ, tracks are in ℚ, and `ι : ℕ → ℚ` connects them with `Faithful` side
conditions.  The consequence is two languages (`Euclid`, `DParam`, `DPhases`)
and two JS evaluator modes (the `D` flag).

## 2. What each domain supports

Time enters the language through a handful of operations.  The domains differ in
which of them they have.

| | ℕ | ℤ | ℚ |
|---|---|---|---|
| order, `+`, `0` | yes | yes | yes |
| subtraction | truncated (monus), not inverse to `+` | exact | exact |
| scale by an integer | yes | yes | yes |
| scale by p/q (`τ/d`, slow motion) | no | no | yes |
| subdivide an interval | no | no | yes (dense) |
| floor, mod (loops, hold) | native | native | yes (archimedean) |
| decidable `=` and `≤` | yes | yes | yes |
| induction on time | yes (well-founded) | no | no |
| negative offsets, reversal | no | yes | yes |
| limits, continuity | no | no | no (needs ℝ, not computable) |

Reading the table:

- **ℕ** is what a frame clock is: exact, decidable, inductive.  It cannot say
  `ease(τ/d)` or "half speed", and its subtraction is lossy.  Every `Faithful`
  condition and the `Sub ↦ max (a−b) 0`, `Pct ↦ floor of product` lowerings in
  the ordered-layer spike (`docs/Ordered.md`, branch `stage2-ordered`) come from
  this.
- **ℚ** is the smallest domain in which the animation semantics is closed:
  scaling, easing, subdivision and floor all exist, and everything we evaluate
  is piecewise rational, so ℝ is not needed.
- **ℤ** adds only negatives (reversal, origin shifts).  Keep it only if a
  feature needs it.

## 3. Principle: semantics is dense, observation is discrete

The semantic time of a behaviour is a totally ordered domain with the
operations the program uses.  A *backend* observes it by sampling along an
embedding `ℕ → T`, `n ↦ n·Δ`.  ℕ is the observation clock, not a second
semantics.  This is the denotational-design discipline: fix the meaning first;
an implementation is correct when it is a homomorphism of that meaning.

Consequences:

1. One language of behaviours.  A "discrete" template is the same term, lowered
   when its ℕ reading is wanted (not a second language).
2. One evaluator.  A sampled value is `eval` at a tick; there is no `D` mode.
3. Exactness claims are explicit: the exact statements are about ℚ; the JS runs
   on doubles, and the browser tests at ticks and quarter ticks are what guard
   that gap.

## 4. Parametric in the time unit

"Parametric in time" has a standard meaning here: the signature is layered, a
time domain is a *model* of the layers it supports, and a term is evaluated in
any model that supports every layer it uses.

```
  Core      ordered monoid: 0, +, ⊔ (max), literals
  Sub       truncated or exact subtraction
  Ord       Lt (4-ary select), Min
  Floor     DivBy d, ModBy d, MulLit n
  Scale     multiplication by p/q               (not yet spiked)
  Ease      easing curves                       (ℚ only: no ℕ reading)

  models:   ℕ  = Core + Sub(monus) + Ord + Floor
            ℚ  = Core + Sub + Ord + Floor + Scale + Ease
            ι : ℕ → ℚ is a homomorphism on every layer they share
```

The spike established which homomorphism statements are unconditional (`+`, `⊔`,
`Lt`, `Min`, `DivBy`, `ModBy`, `MulLit`, literals) and which need `Faithful` or a
lowering (`Sub`, `Pct`).  This is the same shape as the `Supports` records for
inputs and backends (a theory, its models, structure-preserving maps), and the
same shape as the layered scalars already in the code.

Whether we need a generic `Time` parameter in the code, or only this layering
with ℚ as the semantic model and ℕ as a tick index, is **open** (§6).

## 5. What we want, and why it is worth it

| Goal | Why | Compass |
|---|---|---|
| Behaviours as terms of a signature, syntax a free monad, meaning an algebra | substitution (time warps, composition) is `>>=`; the monad laws and one fusion lemma replace many ad hoc proofs | Abbott–Altenkirch–Ghani; Swierstra; Plotkin–Power |
| Signatures combined by `⊎` | independent layers and independent inputs compose without interference | Hyland–Plotkin–Power (sum of theories) |
| Meaning first, backends are homomorphisms | each backend's correctness is one lemma, not a re-derivation | Elliott–Hudak; Elliott |
| ℕ only as the observation clock | removes the second language and the second evaluator | digitisation results |
| Inputs and `tick` are commands of the program, backends support a subset | composition is checked at binding; no backend need implement every command | algebraic operations (Plotkin–Power) |
| Absence is strict; only `Par` is lenient | a precise reading of "not yet on screen" | (own design; `overlay-no-unit`) |

If a feature in the codebase has no row here, it is a candidate for removal or
for an explicit justification.

## 6. Literature

- **Denotational animation / FRP.**
  Elliott and Hudak, *Functional Reactive Animation*, ICFP 1997 **[checked]**
  (behaviours as functions of continuous time).
  Elliott, *Push-pull functional reactive programming*, Haskell Symposium 2009,
  doi 10.1145/1596638.1596643 **[checked]** (simple denotational semantics;
  implementation as a homomorphism of it).  The type-class-morphism discipline
  is from Elliott's later writing on denotational design **[memory]**.
- **When discrete observation suffices.**
  Henzinger, Manna, Pnueli, *What good are digital clocks?*, ICALP 1992, LNCS
  623, pp. 545–558 **[checked]**: integer-time verification is sound for a large
  class of systems and properties (time-bounded invariance and response).  The
  precise closure conditions were not in the sources I read; **[memory]** only.
  Alur and Dill, *A theory of timed automata*, TCS 126(2):183–235, 1994
  **[checked]** (dense time with clocks).  What transfers to us is the *shape*
  of the claim, that observation at integer points can be exact for a class of
  properties, which we should state and prove for ours, not assume.
- **Discrete time with types.**
  Krishnaswami, *Higher-order FRP without spacetime leaks*, ICFP 2013
  **[checked]**; Bahr, Graulund, Møgelberg, *Simply RaTT*, PACMPL 3 (ICFP) 2019
  **[checked]** (note: ICFP, not LICS).  This tradition is about causality and
  space leaks; we have neither problem (animations are finite, closed
  programs), so it is background, not a dependency.
- **Synchronous and dataflow.**
  Halbwachs, Caspi, Raymond, Pilaud, *The synchronous dataflow programming
  language LUSTRE*, Proc. IEEE 79(9), 1991 **[checked]**.
  Uustalu and Vene, *The essence of dataflow programming*, APLAS 2005, LNCS 3780
  pp. 2–18 **[checked]** (comonadic streams over ℕ).
- **Syntax as free monads on containers; combining signatures.**
  Abbott, Altenkirch, Ghani, *Containers: constructing strictly positive types*,
  TCS 342(1):3–27, 2005 **[checked]**.
  Swierstra, *Data types à la carte*, JFP 18(4):423–436, 2008 **[checked]**.
  Hyland, Plotkin, Power, *Combining effects: sum and tensor*, TCS 2006
  **[memory; the search did not return it, only later work building on it,
  e.g. Bacci–Mardare–Panangaden–Plotkin, LMCS]**: the sum of effects is their
  non-interacting union, which is our `⊎`.
  Plotkin and Power, *Algebraic operations and generic effects* **[memory]**:
  operations such as `tick` and `await` are algebraic operations.

## 7. Decision on the time unit (author, 2026-10-27)

- **`Time` is a parameter.**  The semantics of scenes and behaviours is stated against
  an abstract model of the layered time theory of section 4 (a record of the layers
  used, with their laws), not against ℚ.
- **The first instance is `Time = ℚ`.**  Everything is implemented and tested there.
- **Proofs use extrinsic properties.**  Lemmas are proved from the laws of the model
  record (monoid, order, floor spec, scaling), never by computing in ℚ, so that
  the language can later be generalised (another model) or specialised (a smaller
  theory) without re-proving.  A property of a *model* (density, induction,
  archimedean) is a named hypothesis of the lemma that needs it.
- **ℕ is the tick clock**: it indexes control-machine states and observation
  instants, read through a model homomorphism `ι : ℕ → ℚ`; it is not a second value
  language (discrete templates are lowered terms, `docs/Ordered.md`).
- **ℤ is not adopted** unless a feature needs negative offsets.
- **Variance** (see the discussion in the plan): a larger theory gives a larger
  signature `TimeC(L) ↪ TimeC(L')` and a monad morphism; a model of `L'` restricts to
  a model of `L`; evaluation is natural along model homomorphisms; a lowering for
  an operation that `ι` does not preserve is a Kleisli arrow `C⋆ → C'⋆`.  Order is
  kept algebraic through the select form `Lt a b x y`.  Models are explicit records
  (no instance search).
- **Consequence:** the ordered-layer migration M1 to M3 (`plan/Unify.md` 4c) is the
  implementation, now stated against the model record.

## 7b. Open questions

1. **Generic `Time` parameter, or fixed ℚ?**  The code must at least say, per
   module, which layers it uses.  A record `TimeDomain` (ordered monoid plus
   optional layers) is the parametric form; fixing ℚ with an ℕ tick index is the
   cheap form.  Recommendation: start with the cheap form and make the layering
   (§4) explicit in the module headers; generalise only if a second model with a
   real use appears.
2. **Digitisation statement.**  State and prove, for our signature, that
   sampling at ticks agrees with the ℕ reading for the discrete fragment (the
   spike's `discrete-is-ordered` is the core of it); decide what is claimed for
   quarter ticks and non-integer Δ.
3. **`Scale` and the time-select `Seq`.**  Needed before `Track` can be derived
   from `Ease` (stage M4 of the ordered-layer plan); neither is spiked.
4. **Frame-level corollary.**  Layout of lowered leaves in an exact scalar,
   evaluated at `ι ∘ ρ`, equals the ℕ frame; expected from `layout-natural` and
   `faithful-layout`, not built.
5. **JS agreement** with the Agda evaluator is tested, not proved; the Stage 5
   generated evaluator would make it a property of one table.

## 8. Audit criterion

Before each migration step, list what it deletes and what it adds, and check
each remaining module against §5.  A module that supports no goal there, or
exists only to emulate a quirk of ℕ, is a deletion candidate.
