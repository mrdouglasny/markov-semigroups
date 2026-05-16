/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `GeneratorCompat` for the multivariate Gaussian OU instance

G2/G4 of the Gross-discharge plan (`plans/gross-discharge.md`):
discharge the `GeneratorCompat` hypothesis of
`gross_lsi_implies_hypercontractive_of_hypotheses` for the shipped
`stdGaussianFin_dirichletMarkovSemigroup n` instance.

Pieces (split for parallel development):
- base `EuclideanGeneratorLp` — `memLp_ouGeneratorFin`,
  `ouGeneratorFinLp`;
- `EuclideanGeneratorLimit` — the strong-`L²` difference-quotient
  limit (G2 (a), Codex work item);
- here — `ouGeneratorFin_ibp` (**= G4**, nD γ-IBP) and the assembling
  `generatorCompat_stdGaussianFin`.

Non-breaking: only *adds* a discharge theorem; the abstract structure
and the shipped instance are untouched.
-/

import MarkovSemigroups.Instances.WorkInProgress.EuclideanGeneratorLp
import MarkovSemigroups.Instances.WorkInProgress.EuclideanGeneratorLimit

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

namespace GaussianFin

variable {n : ℕ}

/-- **G4 — nD Gaussian integration by parts.** For core `f, g`:
`⟪g, ouGeneratorFin f⟫_{L²(γFin n)} = -ouEnergyFin g f`.

Strategy: tensor-lift of the proved 1D
`Gaussian1D.gaussian_generator_ibp` (`∫ g·(L f) dγ = -∫ g'·f' dγ`)
through the product Gaussian via the Fubini/`insertNth` machinery in
`EuclideanFinLp`: apply the 1D identity per coordinate, sum over
`i : Fin n`, recombining `∑ᵢ ∂ᵢg·∂ᵢf = ouGammaFin g f` whose integral
is `ouEnergyFin g f`. -/
theorem ouGeneratorFin_ibp {f g : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (hg : IsCoreFin g) :
    ⟪(stdGaussianFin_dirichletMarkovSemigroup n).coreToL2 hg,
        ouGeneratorFinLp hf⟫_ℝ
      = - ouEnergyFin g f := by
  sorry

/-- **G2 — `GeneratorCompat` discharged for the shipped Gaussian
instance.** Assembles the strong-`L²` limit
(`ouSemigroupFinLp_diffQuot_tendsto`) and the γ-IBP form identity
(`ouGeneratorFin_ibp`). This is exactly the `h_gen` argument the
gaussian-hilbert call-site supplies to
`gross_lsi_implies_hypercontractive_of_hypotheses`. -/
theorem generatorCompat_stdGaussianFin (n : ℕ) :
    GeneratorCompat (stdGaussianFin_dirichletMarkovSemigroup n) := by
  intro f hf
  exact ⟨ouGeneratorFinLp hf,
    ouSemigroupFinLp_diffQuot_tendsto hf,
    fun {g} hg => ouGeneratorFin_ibp hf hg⟩

end GaussianFin

end
