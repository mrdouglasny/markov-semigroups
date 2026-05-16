/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `GeneratorCompat` for the multivariate Gaussian OU instance (G2 + G4)

G2/G4 of the Gross-discharge plan (`plans/gross-discharge.md`):
discharge the `GeneratorCompat` hypothesis of
`gross_lsi_implies_hypercontractive_of_hypotheses` for the shipped
`stdGaussianFin_dirichletMarkovSemigroup n` instance, with the
generator value `Af := (ouGeneratorFin f : as L²)` (G1's named OU
generator). Non-breaking: the abstract structure and the shipped
instance are untouched; this only *adds* a discharge theorem.

Decomposition (skeleton — three documented sub-lemmas, filled
incrementally):

- `memLp_ouGeneratorFin` — `ouGeneratorFin f ∈ L²(γFin n)` for core
  `f` (core = `ContDiff ℝ ∞` + bounded derivatives ⇒ `Δf − x·∇f` has
  at most linear growth ⇒ square-integrable against the Gaussian).
- `ouGeneratorFin_ibp` (**= G4**) — nD Gaussian integration by parts
  `⟪g, ouGeneratorFin f⟫_{L²(γ)} = -ouEnergyFin g f`; tensor-lift of
  the proved 1D `Gaussian1D.gaussian_generator_ibp` via the product
  measure / Fubini machinery already in `EuclideanFinLp`.
- `ouSemigroupFinLp_diffQuot_tendsto` (**G2 (a), the hard one**) —
  the strong-`L²` right limit of the difference quotient equals
  `ouGeneratorFin f`; pointwise heat equation
  (`Gaussian1D.hasDerivAt_t_ouSemigroup'` lifted coordinatewise) +
  dominated convergence (the repo-standard pattern used for the
  quadratic/entropy discharges).

`generatorCompat_stdGaussianFin` then assembles these into
`GeneratorCompat (stdGaussianFin_dirichletMarkovSemigroup n)`.
-/

import MarkovSemigroups.Instances.WorkInProgress.EuclideanFinLp
import MarkovSemigroups.Instances.WorkInProgress.EuclideanGenerator

open MeasureTheory Filter
open scoped BigOperators Topology InnerProductSpace

noncomputable section

namespace GaussianFin

variable {n : ℕ}

/-- `ouGeneratorFin f = Δf − x·∇f` is `L²(γFin n)` for core `f`.

Strategy: `IsCoreFin` gives `f` `ContDiff ℝ ∞` with uniformly
bounded first/second partials, so `∑ᵢ ∂ᵢ²f` is bounded and
`∑ᵢ xᵢ ∂ᵢf` has at most linear growth in `x`; both are
square-integrable against the standard Gaussian `γFin n`
(`memLp_two_of_bound`-style + Gaussian polynomial moments). -/
theorem memLp_ouGeneratorFin {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    MemLp (ouGeneratorFin f) 2 (γFin n) := by
  sorry

/-- The `L²(γFin n)` element represented by `ouGeneratorFin f`. -/
def ouGeneratorFinLp {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    Lp ℝ 2 (γFin n) :=
  (memLp_ouGeneratorFin hf).toLp (ouGeneratorFin f)

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

/-- **G2 (a) — strong-`L²` difference-quotient limit.** For core `f`,
`t⁻¹ • (P_t [f] − [f]) → [ouGeneratorFin f]` in `L²(γFin n)` as
`t → 0⁺`.

Strategy: the pointwise OU heat equation
`Gaussian1D.hasDerivAt_t_ouSemigroup'` lifted coordinatewise gives
`(P_t f(x) − f(x))/t → ouGeneratorFin f x` pointwise; the difference
quotient is dominated (core bounds + Mehler contraction) by a fixed
`L²(γ)` function, so dominated convergence upgrades the pointwise
limit to the strong `L²` limit (the same DCT pattern used for the
quadratic/entropy `ouSemigroupFin_*` discharges). Right-derivative
only (`𝓝[>] 0`), matching `GeneratorCompat`. -/
theorem ouSemigroupFinLp_diffQuot_tendsto {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) :
    Tendsto
      (fun t : ℝ => t⁻¹ •
        ((stdGaussianFin_dirichletMarkovSemigroup n).P t
            ((stdGaussianFin_dirichletMarkovSemigroup n).coreToL2 hf)
          - (stdGaussianFin_dirichletMarkovSemigroup n).coreToL2 hf))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (ouGeneratorFinLp hf)) := by
  sorry

/-- **G2 — `GeneratorCompat` discharged for the shipped Gaussian
instance.** Assembles the three sub-lemmas. This is exactly the
`h_gen` argument that the gaussian-hilbert call-site will supply to
`gross_lsi_implies_hypercontractive_of_hypotheses`. -/
theorem generatorCompat_stdGaussianFin (n : ℕ) :
    GeneratorCompat (stdGaussianFin_dirichletMarkovSemigroup n) := by
  intro f hf
  exact ⟨ouGeneratorFinLp hf,
    ouSemigroupFinLp_diffQuot_tendsto hf,
    fun {g} hg => ouGeneratorFin_ibp hf hg⟩

end GaussianFin

end
