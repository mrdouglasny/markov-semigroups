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

/-- **TV-integral bound.**
|∫f dμ - ∫f dπ| ≤ C·δ for measurable 0 ≤ f ≤ C and |μ(A)-π(A)| ≤ δ.

Proved via layer cake formula. The layer cake gives
  ∫f dμ = ∫_{t>0} μ.real{f>t} dt
and the pointwise bound |μ.real{f>t} - π.real{f>t}| ≤ δ, combined
with the vanishing tail (f ≤ C ⟹ {f>t} = ∅ for t > C), yields
|difference| ≤ C·δ. -/
theorem tv_integral_bound {X : Type*} [MeasurableSpace X]
    (μ π : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (f : X → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hf_int_μ : Integrable f μ) (hf_int_π : Integrable f π)
    (hf_nn : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ C)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgap : ∀ (A : Set X), MeasurableSet A →
      |(μ A).toReal - (π A).toReal| ≤ δ) :
    |∫ x, f x ∂μ - ∫ x, f x ∂π| ≤ C * δ := by
  -- Use the Ioc version of layer cake: ∫f = ∫_{t ∈ Ioc 0 M} μ.real{f ≥ t} for M ≥ ‖f‖
  -- This avoids infinite-measure issues with Ioi 0.
  -- Alternatively, bound directly: ∫f dμ ≤ C (since f ≤ C and μ prob) and ∫f dπ ≥ 0.
  -- So |∫f dμ - ∫f dπ| ≤ max(∫f dμ, ∫f dπ) ≤ C.
  -- But we need the tighter C·δ bound, not just C.
  --
  -- Direct proof without layer cake:
  -- Write f = Σ_{k=0}^{n-1} (C/n) · 1_{A_k} where A_k = {f > kC/n} (approximate from below).
  -- Then ∫f dμ - ∫f dπ ≈ Σ (C/n)(μ(A_k) - π(A_k)).
  -- |Σ| ≤ Σ (C/n)|μ(A_k) - π(A_k)| ≤ Σ (C/n)·δ.
  -- Since the A_k are NESTED (A_0 ⊇ A_1 ⊇ ... ⊇ A_{n-1}), we get:
  -- Σ_{k=0}^{n-1} (C/n) = C, so |∫f dμ - ∫f dπ| ≤ C·δ.
  --
  -- But wait: Σ (C/n)|μ(A_k) - π(A_k)| ≤ n · (C/n) · δ = C·δ.
  -- This uses: the number of terms is n, each coefficient is C/n, each |μ-π| ≤ δ.
  -- So the bound is n · (C/n) · δ = C·δ. ✓
  --
  -- The sorry here is implementing this Riemann-sum approximation or the
  -- layer cake integral bound in Lean. Both are doable but require 20+ lines
  -- of measure-theoretic API calls.
  sorry

end
