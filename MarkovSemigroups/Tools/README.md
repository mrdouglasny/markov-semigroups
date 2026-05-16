# `MarkovSemigroups/Tools/` — measure-theoretic primitives

Single-module support directory: generic, domain-neutral measure
theory used by the Dobrushin covariance-bound layer. Nothing
Dobrushin-specific lives here.

| Module | Role | Canonical source | Status |
|--------|------|------------------|--------|
| `SingleSiteDisintegration.lean` | Single-site conditional disintegration: for a probability measure `μ` on `SpinConfig I S = I → S` and a site `x : I`, builds `condSingleSiteMeasure μ x a := (μ(eval_x⁻¹{a}))⁻¹ • μ.restrict(eval_x⁻¹{a})` as a measurable family of probability measures (convention `0⁻¹ = 0` so null atoms give the zero measure), and proves the disintegration identity `∫ f ∂μ = ∫ a, (∫ f ∂(cond μ x a)) ∂(μ.map (·x))`. For `[Countable S] [MeasurableSingletonClass S]` the proof is the explicit fiber decomposition `μ = Measure.sum (a ↦ μ.restrict(eval_x⁻¹{a}))` via `integral_sum_measure`, `integral_smul_measure`, `integral_countable`. Module `M1` of `Dobrushin/PLAN_B2.md`. | **Utility — no direct textbook locus.** It is a pure measure-theoretic primitive in the spirit of Mathlib's `condKernel` disintegration. Conceptually adjacent (kernels vs. conditional probabilities): Friedli–Velenik 2017, §6.3 / Ch. 6; that book's Dobrushin-uniqueness content is the downstream math, not this primitive. | sorry-free, axiom-free (0 / 0). |

## Cross-refs

- Downstream consumer: `Dobrushin/CovarianceBoundMultisite.lean`
  (module `M4`, iterated-DLR covariance bound, used by `lgt`) and the
  rest of `Dobrushin/`.
- Plan: `Dobrushin/PLAN_B2.md` (this is module `M1`, Route B —
  explicit construction).
- Mathlib analog: `condKernel` disintegration (Giry monad / measure
  theory).
- Summaries: `refs/summaries/Friedli-Velenik/` (start at
  `refs/summaries/README.md`); Dobrushin uniqueness = Ch. 6 §6.5.2
  p. 268.
