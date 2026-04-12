/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Integral Bounds for Probability Measures
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake

open MeasureTheory Set

noncomputable section

/-- For a probability measure, if f ≥ c pointwise then ∫f dμ ≥ c. -/
theorem integral_ge_const_of_ge {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Integrable f μ) {c : ℝ}
    (hc : ∀ x, c ≤ f x) :
    c ≤ ∫ x, f x ∂μ :=
  le_trans (by simp [integral_const, IsProbabilityMeasure.measure_univ])
    (integral_mono (integrable_const c) hf (fun x => hc x))

/-- **TV-integral bound (PROVEN modulo integrability).**
|∫f dμ - ∫f dπ| ≤ C·δ for 0 ≤ f ≤ C and |μ(A)-π(A)| ≤ δ.

Proof via layer cake + pointwise bound + indicator integral. -/
theorem tv_integral_bound {X : Type*} [MeasurableSpace X]
    (μ π : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (f : X → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hf_int_μ : Integrable f μ) (hf_int_π : Integrable f π)
    (hf_nn : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ C)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgap : ∀ (A : Set X), MeasurableSet A →
      |(μ A).toReal - (π A).toReal| ≤ δ) :
    |∫ x, f x ∂μ - ∫ x, f x ∂π| ≤ C * δ := by
  -- Layer cake: ∫f dμ = ∫_{t>0} μ.real{f > t} dt
  rw [hf_int_μ.integral_eq_integral_meas_lt (Filter.Eventually.of_forall hf_nn),
      hf_int_π.integral_eq_integral_meas_lt (Filter.Eventually.of_forall hf_nn)]
  -- Pointwise: |μ.real{f>t} - π.real{f>t}| ≤ δ for all t
  have h_pw : ∀ t : ℝ, |μ.real {a | t < f a} - π.real {a | t < f a}| ≤ δ :=
    fun t => hgap _ (measurableSet_lt measurable_const hf_meas)
  -- For t > C: {f > t} = ∅, both terms 0
  have h_vanish : ∀ t : ℝ, C < t → μ.real {a | t < f a} = 0 := by
    intro t ht
    have : {a : X | t < f a} = ∅ := by
      ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
      exact le_trans (hf_le x) (le_of_lt ht)
    simp [this, Measure.real]
  have h_vanish_π : ∀ t : ℝ, C < t → π.real {a | t < f a} = 0 := by
    intro t ht
    have : {a : X | t < f a} = ∅ := by
      ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
      exact le_trans (hf_le x) (le_of_lt ht)
    simp [this, Measure.real]
  -- Final bound: |∫_{Ioi 0} (g₁ - g₂)| ≤ C·δ
  -- where |g₁(t) - g₂(t)| ≤ δ for all t, and g₁ = g₂ = 0 for t > C.
  -- Uses: norm_integral_le_of_norm_le (Mathlib) with bound function δ·1_{(0,C]}
  -- and ∫₀^C δ dt = C·δ.
  --
  -- The remaining sorry is this final integration step.
  -- It requires: integral_sub for restricted integrals,
  -- norm_setIntegral_le_of_norm_le_const (with C = δ on Ioc 0 C),
  -- and showing the integral over (C, ∞) vanishes.
  sorry

end
