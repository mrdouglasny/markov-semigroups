/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strong-`L²` difference-quotient limit for the Gaussian OU semigroup

G2 (a) of the Gross-discharge plan (`plans/gross-discharge.md`) — the
analytic core. For core `f`, the right difference quotient of the
`Lp`-carrier OU semigroup converges in `L²(γFin n)`-norm to the named
generator `ouGeneratorFin f = Δf − x·∇f`.

**This file is the Codex work item.** It contains exactly one
`sorry` (`ouSemigroupFinLp_diffQuot_tendsto`). It is deliberately
isolated so it can be filled in parallel with the γ-IBP / assembly
work in `EuclideanGeneratorCompat`.
-/

import MarkovSemigroups.Instances.WorkInProgress.EuclideanGeneratorLp

open MeasureTheory Filter
open scoped BigOperators Topology InnerProductSpace

noncomputable section

namespace GaussianFin

variable {n : ℕ}

/-- **G2 (a) — strong-`L²` difference-quotient limit.** For core `f`,
`t⁻¹ • (P_t [f] − [f]) → [ouGeneratorFin f]` in `Lp ℝ 2 (γFin n)` as
`t → 0⁺` (right limit, matching `GeneratorCompat`'s `𝓝[>] 0`).

Strategy (Gross-discharge plan, Gemini-vetted): the pointwise OU heat
equation `Gaussian1D.hasDerivAt_t_ouSemigroup'`, lifted coordinatewise
through the `ouSemigroupFin` tensor / `insertNth` structure, gives
`(P_t f(x) − f(x))/t → ouGeneratorFin f x` pointwise; the difference
quotient is dominated by a fixed `L²(γFin n)` function (core
`IsCoreFin` bounds + Mehler contraction `ouSemigroupFin_preserves_*`),
so `MeasureTheory.tendsto_Lp_of_…` / dominated convergence upgrades
the pointwise limit to the strong `L²` limit. Same DCT pattern as the
existing `ouSemigroupFin_l2_sq_hasDerivWithinAt` /
`gaussian1D_pairing_hasDerivWithinAt_zero` discharges. -/
theorem ouSemigroupFinLp_diffQuot_tendsto {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) :
    Tendsto
      (fun t : ℝ => t⁻¹ •
        ((stdGaussianFin_dirichletMarkovSemigroup n).P t
            ((stdGaussianFin_dirichletMarkovSemigroup n).coreToL2 hf)
          - (stdGaussianFin_dirichletMarkovSemigroup n).coreToL2 hf))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (ouGeneratorFinLp hf)) := by
  sorry

end GaussianFin

end
