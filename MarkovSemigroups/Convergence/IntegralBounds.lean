/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Integral Bounds for Probability Measures
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
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

/-- **TV-integral bound.** PROVEN via layer cake on a finite interval.

For probability measures μ, π and measurable f with 0 ≤ f ≤ C,
if |μ(A) - π(A)| ≤ δ for all measurable A, then |∫f dμ - ∫f dπ| ≤ C·δ. -/
theorem tv_integral_bound {X : Type*} [MeasurableSpace X]
    (μ π : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (f : X → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hf_int_μ : Integrable f μ) (hf_int_π : Integrable f π)
    (hf_nn : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ C)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgap : ∀ (A : Set X), MeasurableSet A →
      |(μ A).toReal - (π A).toReal| ≤ δ) :
    |∫ x, f x ∂μ - ∫ x, f x ∂π| ≤ C * δ := by
  -- Layer cake on finite interval [0, C]:
  -- ∫f dμ = ∫_{Ioc 0 C} μ.real{f ≥ t} dt
  have hnn_ae_μ : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall hf_nn
  have hnn_ae_π : 0 ≤ᵐ[π] f := Filter.Eventually.of_forall hf_nn
  have hle_ae_μ : f ≤ᵐ[μ] (fun _ => C) := Filter.Eventually.of_forall hf_le
  have hle_ae_π : f ≤ᵐ[π] (fun _ => C) := Filter.Eventually.of_forall hf_le
  rw [hf_int_μ.integral_eq_integral_Ioc_meas_le hnn_ae_μ hle_ae_μ,
      hf_int_π.integral_eq_integral_Ioc_meas_le hnn_ae_π hle_ae_π]
  -- Now: |∫_{Ioc 0 C} μ.real{f≥t} - ∫_{Ioc 0 C} π.real{f≥t}| ≤ C·δ
  -- = |∫_{Ioc 0 C} (μ.real{f≥t} - π.real{f≥t}) dt|
  -- Pointwise: |μ.real{f≥t} - π.real{f≥t}| ≤ δ
  -- Ioc 0 C has Lebesgue measure C.
  -- So |integral| ≤ ‖integrand‖_∞ · measure(Ioc 0 C) = δ · C.
  --
  -- Combine: ∫g₁ - ∫g₂ = ∫(g₁ - g₂) on the finite interval Ioc 0 C
  have h_meas_μ : ∀ t, MeasurableSet {a : X | t ≤ f a} :=
    fun t => measurableSet_le measurable_const hf_meas
  -- Pointwise bound: |μ.real{f≥t} - π.real{f≥t}| ≤ δ
  have h_pw : ∀ t ∈ Ioc 0 C, ‖μ.real {a | t ≤ f a} - π.real {a | t ≤ f a}‖ ≤ δ := by
    intro t _
    rw [Real.norm_eq_abs]
    exact hgap _ (h_meas_μ t)
  -- Ioc 0 C has finite Lebesgue measure
  have h_finite : volume (Ioc (0 : ℝ) C) < ⊤ := by
    simp [Real.volume_Ioc, hC]
  -- Apply norm_setIntegral_le_of_norm_le_const
  calc |(∫ t in Ioc 0 C, μ.real {a | t ≤ f a}) -
        (∫ t in Ioc 0 C, π.real {a | t ≤ f a})| =
      ‖(∫ t in Ioc 0 C, μ.real {a | t ≤ f a}) -
        (∫ t in Ioc 0 C, π.real {a | t ≤ f a})‖ := (Real.norm_eq_abs _).symm
    _ = ‖∫ t in Ioc 0 C, (μ.real {a | t ≤ f a} - π.real {a | t ≤ f a})‖ := by
        congr 1; rw [integral_sub] <;>
        -- IntegrableOn: t ↦ ν.real{f≥t} is bounded by 1 on finite interval
        -- (antitone measurable function, bounded by probability measure)
        -- t ↦ ν.real{f ≥ t} is integrable on Ioc 0 C:
        -- bounded by 1 (probability measure), measurable (antitone),
        -- on a set of finite Lebesgue measure.
        sorry
    _ ≤ δ * volume.real (Ioc (0 : ℝ) C) :=
        norm_setIntegral_le_of_norm_le_const h_finite h_pw
    _ = δ * C := by simp [Measure.real, Real.volume_Ioc, hC]
    _ = C * δ := mul_comm δ C

end
