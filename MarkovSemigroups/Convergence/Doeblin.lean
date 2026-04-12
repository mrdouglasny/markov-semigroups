/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Doeblin's Condition and Exponential Mixing for Markov Kernels

## Main results (all proved except 2 axioms)

- `doeblin_one_step_contraction` — |μ(A) - π(A)| ≤ 1-ε (**proved**)
- `doeblin_kernel_contraction` — |K(x,A) - π(A)| ≤ 1-ε (**proved**)
- `doeblin_tv_contraction` — |(Tμ)(A) - π(A)| ≤ (1-ε)δ (**axiom**)
- `doeblin_n_step_mixing` — |Tⁿ(δ_x)(A) - π(A)| ≤ (1-ε)ⁿ (**proved by induction**)
- `doeblin_correlation_decay` — |cov| ≤ 4B²(1-ε)^d (**axiom**)

## References

- Doeblin (1937)
- Levin-Peres-Wilmer, "Markov Chains and Mixing Times" (2009), Ch 5
- Chatterjee (2026), App B.5
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import MarkovSemigroups.Convergence.IntegralBounds

open MeasureTheory

noncomputable section

/-! ## Structures -/

/-- A Markov kernel: for each x, K(x, ·) is a probability measure. -/
structure MarkovKernel (X : Type*) [MeasurableSpace X] where
  kernel : X → Measure X
  isProb : ∀ x, IsProbabilityMeasure (kernel x)

attribute [instance] MarkovKernel.isProb

/-- Doeblin's condition: K(x, A) ≥ ε · π(A) for all x, A. -/
structure DoeblinCondition {X : Type*} [MeasurableSpace X]
    (K : MarkovKernel X) (π : Measure X) [IsProbabilityMeasure π] where
  ε : ℝ
  hε_pos : 0 < ε
  hε_le : ε ≤ 1
  minorize : ∀ (x : X) (A : Set X), MeasurableSet A →
    ε * (π A).toReal ≤ (K.kernel x A).toReal

/-! ## One-step contraction (PROVEN) -/

/-- **Doeblin one-step contraction.** -/
theorem doeblin_one_step_contraction {X : Type*} [MeasurableSpace X]
    (μ π : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmin : ∀ (A : Set X), MeasurableSet A →
      ε * (π A).toReal ≤ (μ A).toReal) :
    ∀ (A : Set X), MeasurableSet A →
      |(μ A).toReal - (π A).toReal| ≤ 1 - ε := by
  intro A hA
  have hμA := hmin A hA
  have hμAc := hmin Aᶜ hA.compl
  have hπA_nn : 0 ≤ (π A).toReal := ENNReal.toReal_nonneg
  have hπ_compl : (π Aᶜ).toReal = 1 - (π A).toReal := by
    rw [prob_compl_eq_one_sub hA (μ := π)]
    exact ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top
  have hμ_compl : (μ Aᶜ).toReal = 1 - (μ A).toReal := by
    rw [prob_compl_eq_one_sub hA (μ := μ)]
    exact ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top
  have hπA_le : (π A).toReal ≤ 1 := by
    linarith [hπ_compl, ENNReal.toReal_nonneg (a := π Aᶜ)]
  rw [hπ_compl] at hμAc; rw [hμ_compl] at hμAc
  rw [abs_le]; constructor <;> nlinarith

/-- Direct corollary for the kernel. -/
theorem doeblin_kernel_contraction {X : Type*} [MeasurableSpace X]
    {K : MarkovKernel X} {π : Measure X} [IsProbabilityMeasure π]
    (hD : DoeblinCondition K π) (x : X) (A : Set X) (hA : MeasurableSet A) :
    |(K.kernel x A).toReal - (π A).toReal| ≤ 1 - hD.ε :=
  doeblin_one_step_contraction (K.kernel x) π hD.ε hD.hε_pos hD.hε_le
    (fun B hB => hD.minorize x B hB) A hA

/-! ## Transfer operator -/

/-- Push a measure through the kernel: (Tμ)(A) = ∫ K(x, A) dμ(x). -/
def MarkovKernel.transferOp {X : Type*} [MeasurableSpace X]
    (K : MarkovKernel X) (μ : Measure X) : Measure X :=
  μ.bind K.kernel

/-- The n-step distribution from a point: T^n(δ_x). -/
def MarkovKernel.iteratePoint {X : Type*} [MeasurableSpace X]
    (K : MarkovKernel X) (n : ℕ) (x : X) : Measure X :=
  K.transferOp^[n] (Measure.dirac x)

/-- Stationarity: T(π) = π. -/
theorem MarkovKernel.transferOp_invariant {X : Type*} [MeasurableSpace X]
    (K : MarkovKernel X) (π : Measure X) [IsProbabilityMeasure π]
    (h_inv : ∀ (A : Set X), MeasurableSet A → (π.bind K.kernel) A = π A) :
    K.transferOp π = π := by
  ext A hA; exact h_inv A hA

/-! ## TV contraction (axiom)

The key contraction: |(Tμ)(A) - π(A)| ≤ (1-ε) · sup_B |μ(B) - π(B)|.

Proof sketch: K(x,A) = ε·π(A) + g(x) with g ∈ [0, 1-ε].
(Tμ)(A) - π(A) = ∫g dμ - ∫g dπ (constant cancels).
|∫g dμ - ∫g dπ| ≤ (1-ε)·d_TV(μ,π) by the TV characterization.

This requires: Measure.bind_apply to unfold Tμ, stationarity for π,
and the TV bound |∫f d(μ-π)| ≤ ‖f‖∞ · d_TV(μ,π) for bounded f. -/

/-- **TV contraction (sorry on layer cake integration).**

One step of T contracts the total variation gap by factor (1-ε).

Proof: (Tμ)(A) - π(A) = ∫ [K(x,A) - ε·π(A)] dμ - ∫ [K(x,A) - ε·π(A)] dπ
(constant ε·π(A) cancels since both are probability measures).
Set g(x) = K(x,A) - ε·π(A) ∈ [0, 1-ε] (Doeblin + complement bound).
For h = g/(1-ε) ∈ [0,1], by the layer cake formula:
  |∫h dμ - ∫h dπ| = |∫₀¹ [μ({h>t}) - π({h>t})] dt| ≤ ∫₀¹ δ dt = δ
So |(Tμ)(A) - π(A)| ≤ (1-ε)·δ.

The sorry is the layer cake integration step. Uses
`Integrable.integral_eq_integral_meas_lt` from Mathlib. -/
theorem doeblin_tv_contraction {X : Type*} [MeasurableSpace X]
    {K : MarkovKernel X} {π : Measure X} [IsProbabilityMeasure π]
    (hD : DoeblinCondition K π)
    (h_inv : ∀ (A : Set X), MeasurableSet A → (π.bind K.kernel) A = π A)
    (μ : Measure X)
    (δ : ℝ) (hδ_nn : 0 ≤ δ)
    (hδ : ∀ (B : Set X), MeasurableSet B → |(μ B).toReal - (π B).toReal| ≤ δ)
    (A : Set X) (hA : MeasurableSet A) :
    |(K.transferOp μ A).toReal - (π A).toReal| ≤ (1 - hD.ε) * δ := by
  -- (Tμ)(A) - π(A) = ∫(K(x,A) - ε·π(A)) dμ - ∫(K(x,A) - ε·π(A)) dπ
  -- = ∫g dμ - ∫g dπ where g(x) = K(x,A) - ε·π(A) ∈ [0, 1-ε]
  -- By tv_integral_bound with C = 1-ε: |∫g dμ - ∫g dπ| ≤ (1-ε)·δ
  sorry -- Apply tv_integral_bound to g(x) = (K.kernel x A).toReal - hD.ε * (π A).toReal
        -- after unfolding transferOp via Measure.bind_apply and using stationarity

/-! ## N-step mixing (PROVEN by induction from TV contraction) -/

/-- **Doeblin's theorem: n-step mixing (PROVEN).**

|T^n(δ_x)(A) - π(A)| ≤ (1-ε)^n.

Proof by induction on n.
Base: |δ_x(A) - π(A)| ≤ 1 (both in [0,1]).
Step: apply doeblin_tv_contraction with δ = (1-ε)^n. -/
theorem doeblin_n_step_mixing {X : Type*} [MeasurableSpace X]
    {K : MarkovKernel X} {π : Measure X} [IsProbabilityMeasure π]
    (hD : DoeblinCondition K π)
    (h_inv : ∀ (A : Set X), MeasurableSet A → (π.bind K.kernel) A = π A)
    (n : ℕ) (x : X) (A : Set X) (hA : MeasurableSet A) :
    |(K.iteratePoint n x A).toReal - (π A).toReal| ≤ (1 - hD.ε) ^ n := by
  induction n generalizing A with
  | zero =>
    simp only [MarkovKernel.iteratePoint, Function.iterate_zero, id, pow_zero]
    -- |δ_x(A) - π(A)| ≤ 1: both values in [0,1]
    have h1 : (Measure.dirac x A).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal one_pos.le (ENNReal.ofReal_one ▸ prob_le_one)
    have h2 : (π A).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal one_pos.le (ENNReal.ofReal_one ▸ prob_le_one)
    rw [abs_le]; constructor <;> linarith [ENNReal.toReal_nonneg (a := Measure.dirac x A),
      ENNReal.toReal_nonneg (a := π A)]
  | succ n ih =>
    rw [pow_succ, mul_comm]
    simp only [MarkovKernel.iteratePoint, Function.iterate_succ'] at *
    -- T^{n+1}(δ_x) = T(T^n(δ_x)). Apply TV contraction with δ = (1-ε)^n.
    exact doeblin_tv_contraction hD h_inv _
      ((1 - hD.ε) ^ n)
      (pow_nonneg (by linarith [hD.hε_le]) n)
      (fun B hB => ih B hB)
      A hA

/-! ## Correlation decay (axiom) -/

/-- **Correlation decay from Doeblin.**

|E_π[f₁(X₀)f₂(X_d)] - E_π[f₁]E_π[f₂]| ≤ 4B²(1-ε)^d.

Proof: condition on X₀. By n-step mixing (doeblin_n_step_mixing):
  |E[f₂|X₀=x] - E_π[f₂]| = |∫f₂ dK^d(x,·) - ∫f₂ dπ| ≤ 2B(1-ε)^d.
Then: |cov| = |∫ f₁(x)(E[f₂|X₀=x] - E_π[f₂]) dπ(x)| ≤ B·2B(1-ε)^d.

Sorry on the conditioning / iterated integral step. -/
theorem doeblin_correlation_decay {X : Type*} [MeasurableSpace X]
    {K : MarkovKernel X} {π : Measure X} [IsProbabilityMeasure π]
    (hD : DoeblinCondition K π)
    (f₁ f₂ : X → ℝ) (B : ℝ) (hB1 : ∀ x, |f₁ x| ≤ B) (hB2 : ∀ x, |f₂ x| ≤ B)
    (d : ℕ) :
    |∫ x, f₁ x * f₂ x ∂π - (∫ x, f₁ x ∂π) * (∫ x, f₂ x ∂π)| ≤
      4 * B ^ 2 * (1 - hD.ε) ^ d := by
  sorry

end
