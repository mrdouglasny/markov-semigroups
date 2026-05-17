# Gusakov, Nelson, Watt — "Structuring Definitions in Mathematical Libraries" (arXiv:2509.10828, 2025)

*Structured reading; second entry in the [def-study](README.md) collection.*

Directly on-topic for everything in
[bundled-vs-unbundled.md](bundled-vs-unbundled.md): the paper is a
case-study analysis of how Mathlib definitions get designed,
refactored, and ultimately adopted. Treats Mathlib inclusion as an
empirical signal for "good" definitions, then dissects four
case studies and the design patterns that emerge.

## Abstract & framing

The authors argue **definition structuring is the most challenging
aspect of codifying mathematical theories in proof assistants and
computer algebra systems**. Practitioners balance level of
generality, readability, and type-system ergonomics, and typically
settle on a definition only after extensive trial and error
formalizing standard theorems against it. The paper's contribution:
make these design trade-offs explicit by analyzing four detailed
Mathlib case studies.

This is the same operational rule we've been applying in
`markov-semigroups` and capturing in
[`bundled-vs-unbundled.md`](bundled-vs-unbundled.md): **stress-test
candidate definitions against real use-case theorems before
committing.**

## The four case studies

### 1. Continuous Functional Calculus (CFC) — dependent-type handling
- Evolved from element-level predicates to algebra-wide properties
  using `outParam`.
- Authors then converted entire typeclasses to `Prop` using **proof
  irrelevance**, exploiting Stone–Weierstrass uniqueness to abstract
  away the specific morphism.
- **Junk-value approach explicitly recommended**: rather than
  enforcing the strict-typed `C(spec a, ℝ) →⋆ₐ A` everywhere,
  accept bare `f : ℝ → ℝ` and "output 0 otherwise." Reduces
  propositional-equality friction; mathematical content lost to junk
  values is recovered as separate lemmas.

This is the exact `cfcL` vs `cfc` story we wrote about in
[`bundled-vs-unbundled.md`](bundled-vs-unbundled.md). The paper
**validates the unbundled-with-junk choice with explicit
methodology**.

### 2. Graded rings — sigma types and definitional equality
- Two candidate forms tested:
  - Bundled: multiplicative associativity baked in via dependent
    pair structure.
  - Unbundled: definitional-equality-friendly multiplication
    `A i → A j → A (i + j)` between distinct grade types.
- Trade-off was explicitly between bundling structural laws vs.
  preserving Lean's `rfl`-level type rewriting.

### 3. Matroids — choosing among cryptomorphic definitions
- Matroids have ~5+ equivalent definitions in the math literature
  (independent sets, bases, circuits, rank function, closure).
- Mathlib choice: collapse the hierarchy and **define `Matroid`
  with an explicit carrier set rather than a type parameter**.
- "Instead of having `Matroid` defined on a ground type `E`... we
  collapse the hierarchy so that `Matroid` always has a carrier
  set."
- Rationale: avoids cascading type coercions during deletion and
  contraction operations.

### 4. Graphs — same carrier-set strategy
- Both matroid and graph case studies **converge on the same
  pattern**: explicit carrier set inside the structure, not type
  parameters.
- Pattern is broader than matroids: any structure with frequent
  deletion / restriction / subobject operations benefits from
  carrier-set-as-data.

## Design patterns extracted

| Pattern | What it solves | Examples in paper |
|---|---|---|
| **Junk values** | Type rigidity that blocks composition | CFC: bare `ℝ → ℝ` input |
| **Bundled vs unbundled trade-off** | Structural laws vs `rfl`-friendly equality | Graded rings sigma types |
| **Typeclass + `outParam` + `Prop`-valued classes** | Abstract uniqueness via proof irrelevance | CFC algebra-wide refactor |
| **Carrier set as data** | Avoid cascading coercions for sub-objects | Matroids, graphs |

The paper's methodology: **iterative formalization** — write
definitions, develop stress-test theorem proofs against them,
refactor based on the friction points that emerge. The cycle is
the empirical signal.

## Connection to `markov-semigroups`

Two of our own structural decisions directly mirror the paper's
case-study patterns:

- **`MarkovSemigroup` carrier refactor (2026-05-13)**: pointwise
  `(X → ℝ) → (X → ℝ)` → bounded operators on `L²(μ)`. Caught
  exactly the kind of friction the paper describes — Bochner junk
  values on non-integrable inputs broke an unconditional structural
  law. The Lp-carrier fix is a textbook application of the paper's
  "carrier set / canonical representative" pattern.

- **`DirichletMarkovSemigroup` bundle vs side hypotheses**: we
  considered both shapes (separate `MarkovSemigroup` + side
  hypothesis vs bundled structure with `energy_eq_deriv` field).
  Bundled won for soundness reasons identical to the paper's
  graded-ring case.

The paper would have saved us a Gemini pass or two if read earlier.

## What to take forward

For the operational rule already in
[`bundled-vs-unbundled.md`](bundled-vs-unbundled.md):

1. Adopt the paper's terminology where useful. "Cryptomorphic"
   for the matroid-style situation (multiple equivalent
   definitions, pick one), "junk value" for the CFC-style
   unbundling.
2. Add **"carrier set as data" pattern** as a third explicit
   design pattern to consider, alongside bundled/unbundled and
   junk values.
3. Reference this paper from the operational rule as supporting
   evidence; cite specific case studies when proposing a refactor.

## Reference

- Gusakov, Nelson, Watt, "Structuring Definitions in Mathematical
  Libraries," arXiv:2509.10828 (2025).
- All four case studies are about Mathlib (Lean 4); methodology
  applies to any proof-assistant / CAS library.
