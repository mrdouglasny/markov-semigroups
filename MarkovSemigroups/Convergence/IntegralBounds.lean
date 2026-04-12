/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Integral Bounds for Probability Measures

Elementary bounds on integrals of bounded measurable functions.
These unify the integration plumbing for Doeblin's theorem.

## Main results

- `integral_ge_const_of_ge` — ∫f dμ ≥ c when f ≥ c (prob measure) [PROVEN]
- `tv_integral_bound` — |∫f dμ - ∫f dπ| ≤ C·δ (TV bound) [sorry]
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

noncomputable section

/-- For a probability measure, if f ≥ c pointwise then ∫f dμ ≥ c. -/
theorem integral_ge_const_of_ge {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Integrable f μ) {c : ℝ}
    (hc : ∀ x, c ≤ f x) :
    c ≤ ∫ x, f x ∂μ :=
  le_trans (by simp [integral_const, IsProbabilityMeasure.measure_univ])
    (integral_mono (integrable_const c) hf (fun x => hc x))

/-- **TV-integral bound.** |∫f dμ - ∫f dπ| ≤ C·δ when 0≤f≤C and
d_TV(μ,π) ≤ δ. Proof: layer cake gives ∫f dμ = ∫₀^C μ({f>t}) dt,
so |∫f d(μ-π)| ≤ ∫₀^C |μ({f>t})-π({f>t})| dt ≤ C·δ.

Uses: `Integrable.integral_eq_integral_meas_lt` from Mathlib
(MeasureTheory.Integral.Layercake). -/
theorem tv_integral_bound {X : Type*} [MeasurableSpace X]
    (μ π : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (f : X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf_nn : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ C)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgap : ∀ (A : Set X), MeasurableSet A →
      |(μ A).toReal - (π A).toReal| ≤ δ) :
    |∫ x, f x ∂μ - ∫ x, f x ∂π| ≤ C * δ := by
  sorry

end
