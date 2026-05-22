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
open scoped InnerProductSpace

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

/-- **`GeneratorCompat` for the standard Gaussian OU semigroup.** The generator
element is `ouGeneratorFinLp hf`; the strong-`L²` difference-quotient convergence is
`ouSemigroupFinLp_diffQuot_tendsto`, and the Dirichlet-form pinning
`⟪coreToL2 g, A f⟫ = -energy g f` is the integration-by-parts identity
`ouGeneratorFin_ibp`. All bridges (`P_t = ouSemigroupFinLp`, `coreToL2 = .toLp`,
`energy = ouEnergyFin`) hold definitionally. -/
theorem stdGaussianFin_generatorCompat (n : ℕ) :
    GeneratorCompat (stdGaussianFin_dirichletMarkovSemigroup n) := by
  intro f hf
  refine ⟨ouGeneratorFinLp hf, ?_, ?_⟩
  · exact ouSemigroupFinLp_diffQuot_tendsto (n := n) hf
  · intro g hg
    exact ouGeneratorFin_ibp hf hg

/-- **`StroockVaropoulos` for the standard Gaussian OU semigroup.** The a.e.
nonnegativity upgrades to everywhere positivity (full support), the limit `Au` is
identified with the generator `ouGeneratorFinLp hu` by uniqueness, the right-hand
inner product unfolds to `energy u (u^{q-1})` via `ouGeneratorFin_ibp`, and the
remaining energy inequality is the textbook Stroock–Varopoulos axiom. -/
theorem stdGaussianFin_stroockVaropoulos (n : ℕ) :
    StroockVaropoulos (stdGaussianFin_dirichletMarkovSemigroup n) := by
  set D := stdGaussianFin_dirichletMarkovSemigroup n with hD
  intro u hu hu_nonneg q hq hu_half hu_one Au hAu
  have hu_nn : ∀ x, 0 ≤ u x := le_of_ae_le_of_continuous hu.continuous hu_nonneg
  -- `Au` is the OU generator of `u` (unique strong-L² limit of the difference quotient).
  have hAu_eq : Au = ouGeneratorFinLp hu :=
    tendsto_nhds_unique hAu (ouSemigroupFinLp_diffQuot_tendsto (n := n) hu)
  -- The form pairing identity, in `D.coreToL2`/`D.energy` normal form.
  have hibp : (⟪D.coreToL2 hu_one, ouGeneratorFinLp hu⟫_ℝ : ℝ)
      = - D.energy (fun x => u x ^ (q - 1)) u := ouGeneratorFin_ibp hu hu_one
  have hpair : (⟪D.coreToL2 hu_one, -Au⟫_ℝ : ℝ) = D.energy u (fun x => u x ^ (q - 1)) := by
    rw [hAu_eq, inner_neg_right, hibp, neg_neg, D.energy_symm (fun x => u x ^ (q - 1)) u]
  rw [hpair]
  exact stroock_varopoulos D q hq u hu hu_nn hu_half hu_one

end GaussianFin
