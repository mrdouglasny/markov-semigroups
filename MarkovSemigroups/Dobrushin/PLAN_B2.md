# Plan: Phase B2 — Iterated-DLR Covariance Bound

*2026-04-15*

## Why this is worth doing

The Dobrushin covariance bound is a **foundational result in statistical
mechanics** with applications well beyond lattice gauge theory:

- **Classical spin systems.** Ising, Potts, O(n), any lattice model at
  high temperature / small coupling: proves exponential correlation decay,
  unique Gibbs measure, absence of phase transitions.
- **Constructive field theory.** Same estimate underlies cluster-expansion
  and mass-gap arguments for lattice φ⁴, abelian/non-abelian LGT, etc.
- **Algorithmic applications.** The coupling argument is exactly what
  makes Glauber dynamics mix rapidly at high temperature, so it feeds
  into MCMC mixing-time bounds and approximate counting.
- **Mathlib candidate.** The standard textbook theorem (Georgii §8,
  Dobrushin 1968); the sub-modules below are general-purpose probability
  infrastructure (single-site disintegration, iterated coupling along a
  path) worth having upstream in Mathlib regardless.

## Current state

`MarkovSemigroups/Dobrushin/NeumannSeries.lean` (working tree,
uncommitted) contains:

- `covariance_bound_from_conditional_bound` — proved helper
- `dobrushin_covariance_iterateInfluence_bound` — target statement
  with detailed proof-sketch docstring, body is `sorry`
- `dobrushin_correlation_decay_via_path` — proved (conditional on the
  sorry above); composes B2 with the existing `_direct` wrapper.

The single remaining `sorry` needs three independent pieces of
infrastructure, each worth its own focused session/PR:

## M1 — Single-site disintegration (~150–250 lines)

### Goal

Given a probability measure `μ` on `SpinConfig I S = I → S` and a site
`x : I`, produce the conditional measure `μ(· | σ(x) = a)` as a
`Kernel S (SpinConfig I S)` satisfying the disintegration identity:

```lean
∫ σ, f σ ∂μ = ∫ a, (∫ σ, f σ ∂(condMuAtSite μ x a)) ∂(μ.map (· x))
```

### Strategy

- For `[Countable S]` (a standard assumption in this file): use
  `Measure.condKernel` on the coordinate projection
  `eval_x : SpinConfig I S → S`.
- Alternative for `[MeasurableSingletonClass S]`: explicit construction
  via `μ.restrict ((· x) ⁻¹' {a})` rescaled by `1/μ((· x) ⁻¹' {a})`,
  with the atomic case handled separately.
- The proof essentially invokes Mathlib's existing conditional-kernel
  disintegration for the Polish / standard Borel setting.

### Mathlib tools

- `MeasureTheory.Measure.condKernel` (if the current context qualifies).
- `ProbabilityTheory.condKernel` for the product-space setting.
- `Measure.map_fst_prod`, `Measure.prod_apply` for the disintegration
  of marginals.
- `integral_condKernel` / `condKernel_compProd` style lemmas for the
  integral identity.

### Why it's standalone

This is a pure measure-theoretic primitive — has nothing to do with
Dobrushin. It would belong in
`MarkovSemigroups/Tools/SingleSiteDisintegration.lean` or
similar. Other projects (e.g. statistical mechanics at large) will use
it too.

### Known gotchas

- `IsGibbsMeasure` + `DLR` already gives us `μ(· | σ on Λᶜ)` as
  `γ.condDist Λ σ` — but that's the "fix everything outside Λ"
  conditional, not the "fix only σ(x)" conditional. M1 is the
  complementary direction.
- If Mathlib's `condKernel` requires `StandardBorelSpace`, we may
  need to assume that on `S` (it holds for finite / Polish `S`).

## M2 — n-fold iteration of `marginalTvDist_contraction` (~100 lines)

### Goal

Prove that along a path `x = x₀, x₁, ..., x_n = y`, the iterated
marginal-TV contraction bounds are controlled by
`iterateInfluence γ n x y`:

```lean
lemma marginalTvDist_iterate
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ₁ μ₂ : Measure (SpinConfig I S))
    (h₁ : IsGibbsMeasure γ μ₁) (h₂ : IsGibbsMeasure γ μ₂)
    (path : Fin (n+1) → I) (hpath_0 : path 0 = x) (hpath_n : path n = y) :
    marginalTvDist μ₁ μ₂ y ≤ iterateInfluence γ n x y * (μ₁ and μ₂ agree at x)
```

Exact form TBD once M1 is in place — this is where the path-indexed
conditional expectation machinery uses M1 to re-condition at each step.

### Strategy

Induction on `n`. Base case: `n = 0`, `x = y`, the bound is `μ(·) ≤ μ(·)`
(trivial). Inductive step: at each step, use `marginalTvDist_contraction`
(already proven) together with M1 to pass from `marginalTvDist μ₁ μ₂ x_i`
to `marginalTvDist μ₁ μ₂ x_{i+1}`, multiplied by one factor of
`influenceCoeff`.

### Why it depends on M1

The iteration re-conditions at each step. Without M1, there's no way
to express "the measures after fixing `σ(x_i) = a`" inside an induction.

### Size

~100 lines if M1 is clean.

## M3 — Path existence (~20 lines, nearly trivial on lattices)

### Goal

For general `I`, the B2 theorem should either (a) take `n` and a path
of length `n` as parameters, or (b) supply a path-existence hypothesis.
For the concrete case `I = LatticeSite d_lat`, a canonical shortest
path of length `latticeDist x y` exists.

### Strategy

```lean
def latticePath (x y : LatticeSite d_lat) : Fin (latticeDist x y + 1) → LatticeSite d_lat
```

Construct via coordinate-wise interpolation: at step i, move from x
toward y along the first coordinate where they disagree. Then the
path has length `latticeDist x y` by construction.

For the general-I case, just take the path as a parameter.

### Size

~20 lines for the lattice case. Abstract case is a hypothesis, not
a proof.

## M4 — Assemble the B2 theorem (~50 lines on top of M1+M2+M3)

Once M1/M2/M3 are in place:

1. Use M1 to write the covariance as an iterated conditional expectation.
2. Use M2 to bound each step by `marginalTvDist · influenceCoeff`.
3. Chain through the path from `x` to `y` via M3.
4. The iterated bound collapses to `iterateInfluence γ n x y`.
5. The `2·Bf·Bg` prefactor comes from the covariance-coupling identity
   `Cov(f,g) = ½ ∫∫ (f(σ) - f(τ))(g(σ) - g(τ)) dμ dμ` bounded by
   `‖f‖∞ · ‖g‖∞ · tvDist`.

Once assembled, replace the current `sorry` in
`dobrushin_covariance_iterateInfluence_bound`.

## Dependency graph

```
M1 (single-site disintegration) ──┐
                                  ├─→ M4 (B2 proof assembly) ──→ delete sorry
M2 (n-fold contraction iteration)─┤      ↓
                                  │    dobrushin_correlation_decay_via_path
M3 (path existence, lattice case) ┘    becomes unconditional
```

M1 and M2 can start in parallel (M2 uses M1's API, not its proof).
M3 is trivial and can be prototyped anytime.

## Suggested execution

Each Mi is its own focused session/PR. **Do not attempt all in one
agent session** — the prior attempt confirmed this is too much
context to hold at once.

1. **M1 first** — the hardest and most generally useful. A single
   specialist-agent session focused entirely on the single-site
   disintegration API + its disintegration-identity lemma.
2. **M3 next** (it's ~20 lines; can be done in a short session).
3. **M2 after M1** — uses M1's API. Induction along a path.
4. **M4 last** — the assembly is short once M1–M3 are in place.

## Effort estimate

| Module | Lines | Difficulty | Standalone Mathlib value |
|---|---|---|---|
| M1 | 150–250 | MEDIUM | High — general probability tool |
| M2 | 100 | MEDIUM | Medium — specific to Dobrushin |
| M3 | 20 | EASY | Low (trivial for lattice) |
| M4 | 50 | EASY (assembly) | Closes out B2 |
| **Total** | **~400** | | |

The 400-line total is larger than the "~250 lines" in the original
`PLAN.md`. The revision is because the prior attempt revealed that
M1 alone is a substantial sub-module, not a quick helper.

## References

- Dobrushin (1968), "Description of a random field by means of
  conditional probabilities and conditions of its regularity."
- Georgii (1988), *Gibbs Measures and Phase Transitions*, §8.
- Chatterjee (2026), *Gauge Theory Lecture Notes*, Ch 16.
- `MarkovSemigroups/Dobrushin/PLAN.md` — the overall Dobrushin plan.
- `MarkovSemigroups/Dobrushin/NeumannSeries.lean:723` — the current
  `sorry` that this plan closes.
