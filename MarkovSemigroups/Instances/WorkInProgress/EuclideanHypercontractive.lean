/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hypercontractivity of the standard Gaussian OU semigroup

Discharges the per-instance hypotheses of `gross_lsi_implies_hypercontractive_of_hypotheses`
(`CoreSemigroupInvariant`, `GeneratorCompat`, `StroockVaropoulos`, `CoreLpL2Approx`)
for the multivariate standard Gaussian Bakry-Émery bundle
`stdGaussianFin_dirichletMarkovSemigroup`, and assembles the resulting
hypercontractivity statement. This eliminates the `gross_lsi_implies_hypercontractive`
axiom from the downstream `gaussian-hilbert` chain.
-/

import MarkovSemigroups.Abstract.GrossODE
import MarkovSemigroups.Instances.WorkInProgress.EuclideanFinBE

open MeasureTheory Filter

namespace GaussianFin

/-- **`CoreSemigroupInvariant` for the standard Gaussian OU semigroup.** The image
`P_t (coreToL2 g)` of a core element is again the `L²`-class of a core function,
namely `ouSemigroupFin t g`. Uses `ouSemigroupFin_preserves_IsCore` (core closure)
and `ouSemigroupFin_ae_eq_of_aeEq` (a.e.-equality respected by the kernel). -/
theorem stdGaussianFin_coreSemigroupInvariant (n : ℕ) :
    CoreSemigroupInvariant (stdGaussianFin_dirichletMarkovSemigroup n) := by
  set D := stdGaussianFin_dirichletMarkovSemigroup n with hD
  intro t ht g hg
  refine ⟨ouSemigroupFin t g, ouSemigroupFin_preserves_IsCore t ht hg, ?_⟩
  refine Lp.ext_iff.mpr ?_
  have hg_ae : ((D.coreToL2 hg : (Fin n → ℝ) → ℝ)) =ᵐ[γFin n] g :=
    (D.IsCore_memLp hg).coeFn_toLp
  have hP : ((D.P t (D.coreToL2 hg) : (Fin n → ℝ) → ℝ))
      =ᵐ[γFin n] ouSemigroupFin t ((D.coreToL2 hg : (Fin n → ℝ) → ℝ)) :=
    ouSemigroupFinLp_coeFn_ae t ht (D.coreToL2 hg)
  have hmid : ouSemigroupFin t ((D.coreToL2 hg : (Fin n → ℝ) → ℝ))
      =ᵐ[γFin n] ouSemigroupFin t g :=
    ouSemigroupFin_ae_eq_of_aeEq t ht hg_ae
  have hg'_ae : ((D.coreToL2 (ouSemigroupFin_preserves_IsCore t ht hg) : (Fin n → ℝ) → ℝ))
      =ᵐ[γFin n] ouSemigroupFin t g :=
    (D.IsCore_memLp (ouSemigroupFin_preserves_IsCore t ht hg)).coeFn_toLp
  exact hP.trans (hmid.trans hg'_ae.symm)

end GaussianFin
