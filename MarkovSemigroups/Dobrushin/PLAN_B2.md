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

## 2026-04-16 update: Gemini-vetted diagnosis of the last gap

After M1, M2, M3/M4 scaffolding landed, the final remaining sorry
turned out to be more subtle than the plan anticipated. A first
attempt to axiomatize it at the **marginal-TV** level (i.e.,
`marginalTvDist μ₁ μ₂ z ≤ ∑ C(z,w) · marginalTvDist μ₁ μ₂ w`) was
shown **false by Gemini Deep Think** via an explicit counterexample:

> `I = {1,2,3}`, `S = {0,1}`, `γ({1},σ)(1) = ½ + ε(σ₂⊕σ₃−½)`.
> Two Gibbs measures with perfectly correlated vs perfectly
> anticorrelated `(σ₂, σ₃)` have identical single-site marginals at
> 2, 3 but differ by 1/4 at site 1, giving `1/4 ≤ 0 + 0`.

### Correct axiom (now in CondTVBridge.lean)

The correct Dobrushin contraction holds at the **joint-coupling** level:

```lean
axiom dobrushin_iterated_coupling_exists ... :
    ∃ (P : Measure (SpinConfig I S × SpinConfig I S))
      (_ : IsCoupling P μ₁ μ₂),
      ∀ z ∈ T,
        P{p.1 z ≠ p.2 z}.toReal ≤
          ∑' w, C(z,w) · P{p.1 w ≠ p.2 w}.toReal
```

The coupling `P` is the **site-wise iterated greedy coupling** of
Dobrushin 1968. The quantities `P{σ_w ≠ η_w}` strictly dominate
marginal TV and satisfy the self-consistency inequality (whereas
marginal TV does not, per the counterexample). Critically, this
property holds for the *specific* Dobrushin-constructed coupling, not
for maximal couplings at the full-TV level — the existing
`exists_maximal_coupling` in `Coupling/TVCoupling.lean` is the wrong
tool.

### The remaining formalization obligation

Replacing the axiom with a proof requires a new file
`MarkovSemigroups/Coupling/DobrushinCoupling.lean` (~500 lines):

1. Construct the iterated site-wise greedy coupling `P` of `(μ₁, μ₂)`:
   sequentially over sites, condition on the boundary so far and
   extend the coupling to maximize site-wise agreement.
2. Prove by construction that `P` satisfies the self-consistency
   inequality `P{σ_z ≠ η_z} ≤ ∑ C(z,w) · P{σ_w ≠ η_w}` for `z ∈ T`.

Both steps are standard in the Dobrushin-Shlosman / Georgii literature
but require non-trivial measure-theoretic infrastructure on
infinite-product spaces.

### Downstream wiring (also follow-on)

Closing the existing `condSingleSiteMeasure_marginalTvDist_contraction_at_nonX`
sorry using this axiom requires a refactor of the Neumann iteration
chain to propagate coupling disagreement `P{σ_w ≠ η_w}` instead of
`marginalTvDist μ₁ μ₂ w`. The final step uses `tvNorm_le_coupling`
(proved in `TVCoupling.lean`) to bound marginal TV by coupling
disagreement at site `y`, recovering the downstream statement shape.

### Alternative: Föllmer oscillation route

Föllmer (1982) bypasses joint couplings entirely by working with
function-oscillation semi-norms and bounding a contracting linear
operator on Lipschitz-local functions. This route is cleaner in
Lean (no product-space measure machinery) but requires redefining
the core quantities in the B2 chain. Pivot cost is similar to the
coupling construction (~500 lines).

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
