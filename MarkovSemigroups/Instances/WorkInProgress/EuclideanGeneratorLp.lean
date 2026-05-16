/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ouGeneratorFin` as an `L²(γFin n)` element (G2/G4 base)

Shared prerequisite for the `GeneratorCompat` discharge
(`plans/gross-discharge.md`, G2/G4): the named OU generator
`ouGeneratorFin f = Δf − x·∇f` (from `EuclideanGenerator`) is
square-integrable against the standard multivariate Gaussian for core
`f`, hence defines an element of `Lp ℝ 2 (γFin n)`.

Split out so the strong-`L²` limit (`EuclideanGeneratorLimit`) and the
γ-IBP / assembly (`EuclideanGeneratorCompat`) can be developed in
parallel against a common base.
-/

import MarkovSemigroups.Instances.WorkInProgress.EuclideanFinLp
import MarkovSemigroups.Instances.WorkInProgress.EuclideanGenerator

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace GaussianFin

variable {n : ℕ}

/-- `ouGeneratorFin f = Δf − x·∇f ∈ L²(γFin n)` for core `f`.

Strategy: `IsCoreFin` gives `f` `ContDiff ℝ ∞` with uniformly bounded
first/second partials, so `∑ᵢ ∂ᵢ²f` is bounded and `∑ᵢ xᵢ ∂ᵢf` has at
most linear growth in `x`; both are square-integrable against the
standard Gaussian `γFin n` (bounded part via `memLp_two_of_bound`;
linear-growth part via Gaussian polynomial moments). -/
theorem memLp_ouGeneratorFin {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    MemLp (ouGeneratorFin f) 2 (γFin n) := by
  sorry

/-- The `L²(γFin n)` element represented by `ouGeneratorFin f`
(`= Δf − x·∇f`), for core `f`. -/
def ouGeneratorFinLp {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    Lp ℝ 2 (γFin n) :=
  (memLp_ouGeneratorFin hf).toLp (ouGeneratorFin f)

end GaussianFin

end
