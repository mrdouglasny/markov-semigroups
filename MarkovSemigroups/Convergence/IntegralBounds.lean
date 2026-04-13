/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Integral Bounds for Probability Measures
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.LocallyIntegrable

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

/-- The layer cake integrand t ↦ ν.real{f ≥ t} is integrable on (0, C].
Proof: antitone on compact Icc 0 C → integrable, then restrict to Ioc. -/
theorem integrableOn_meas_le_Ioc {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (f : X → ℝ) (C : ℝ) :
    IntegrableOn (fun t => ν.real {a | t ≤ f a}) (Ioc 0 C) volume := by
  apply IntegrableOn.mono_set _ Ioc_subset_Icc_self
  apply AntitoneOn.integrableOn_isCompact isCompact_Icc
  intro s _ t _ hst
  exact ENNReal.toReal_mono (measure_ne_top ν _)
    (measure_mono (fun a ha => le_trans hst ha))

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
        congr 1
        exact (integral_sub (integrableOn_meas_le_Ioc μ f C) (integrableOn_meas_le_Ioc π f C)).symm
    _ ≤ δ * volume.real (Ioc (0 : ℝ) C) :=
        norm_setIntegral_le_of_norm_le_const h_finite h_pw
    _ = δ * C := by simp [Measure.real, Real.volume_Ioc, hC]
    _ = C * δ := mul_comm δ C

/-- TV-integral bound for functions bounded by B (possibly negative).
|∫f dμ - ∫f dπ| ≤ 2B·δ when |f| ≤ B. Reduces to `tv_integral_bound`
via the shift f ↦ f+B ∈ [0, 2B]. -/
theorem tv_integral_bound_abs {X : Type*} [MeasurableSpace X]
    (μ π : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (f : X → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hf_int_μ : Integrable f μ) (hf_int_π : Integrable f π)
    (hBf : ∀ x, |f x| ≤ B)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgap : ∀ A, MeasurableSet A → |(μ A).toReal - (π A).toReal| ≤ δ) :
    |∫ x, f x ∂μ - ∫ x, f x ∂π| ≤ 2 * B * δ := by
  have hshift : ∫ x, f x ∂μ - ∫ x, f x ∂π =
      ∫ x, (f x + B) ∂μ - ∫ x, (f x + B) ∂π := by
    simp [integral_add hf_int_μ (integrable_const B),
          integral_add hf_int_π (integrable_const B),
          integral_const, IsProbabilityMeasure.measure_univ]
  rw [hshift]
  exact tv_integral_bound μ π (fun x => f x + B) (hf.add measurable_const)
    (2 * B) (by linarith)
    (hf_int_μ.add (integrable_const B)) (hf_int_π.add (integrable_const B))
    (fun x => by have := (abs_le.mp (hBf x)).1; linarith)
    (fun x => by have := (abs_le.mp (hBf x)).2; linarith)
    δ hδ hgap

end
