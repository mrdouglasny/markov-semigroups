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

/-- Convert Measure.bind to a real-valued integral:
(μ.bind f A).toReal = ∫ x, (f x A).toReal ∂μ. -/
theorem bind_toReal_eq_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → Measure X) [∀ x, IsProbabilityMeasure (f x)]
    (hf : AEMeasurable f μ)
    (A : Set X) (hA : MeasurableSet A) :
    (μ.bind f A).toReal = ∫ x, (f x A).toReal ∂μ := by
  rw [Measure.bind_apply hA hf, ← integral_toReal]
  · exact (Measure.measurable_coe hA).comp_aemeasurable hf
  · exact Filter.Eventually.of_forall (fun x => measure_lt_top (f x) A)

/-! ## Structures -/

/-- A Markov kernel: for each x, K(x, ·) is a probability measure. -/
structure MarkovKernel (X : Type*) [MeasurableSpace X] where
  kernel : X → Measure X
  isProb : ∀ x, IsProbabilityMeasure (kernel x)
  measurable : Measurable kernel

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
    (μ : Measure X) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ_nn : 0 ≤ δ)
    (hδ : ∀ (B : Set X), MeasurableSet B → |(μ B).toReal - (π B).toReal| ≤ δ)
    (A : Set X) (hA : MeasurableSet A) :
    |(K.transferOp μ A).toReal - (π A).toReal| ≤ (1 - hD.ε) * δ := by
  -- (Tμ)(A) - π(A) = ∫(K(x,A) - ε·π(A)) dμ - ∫(K(x,A) - ε·π(A)) dπ
  -- = ∫g dμ - ∫g dπ where g(x) = K(x,A) - ε·π(A) ∈ [0, 1-ε]
  -- By tv_integral_bound with C = 1-ε: |∫g dμ - ∫g dπ| ≤ (1-ε)·δ
  -- Step 1: Convert bind to integral
  have hK_meas : AEMeasurable K.kernel μ := K.measurable.aemeasurable
  have hK_meas_π : AEMeasurable K.kernel π := K.measurable.aemeasurable
  have h1 : (K.transferOp μ A).toReal = ∫ x, (K.kernel x A).toReal ∂μ :=
    bind_toReal_eq_integral μ K.kernel hK_meas A hA
  have h2 : (π A).toReal = ∫ x, (K.kernel x A).toReal ∂π := by
    have := h_inv A hA
    rw [← this]
    exact bind_toReal_eq_integral π K.kernel hK_meas_π A hA
  rw [h1, h2]
  -- Step 2: Set g(x) = (K.kernel x A).toReal - ε·(π A).toReal
  -- g ∈ [0, 1-ε] by Doeblin condition + complement
  -- The constant ε·(π A).toReal cancels (both prob measures).
  -- Apply tv_integral_bound to g with C = 1-ε.
  set f : X → ℝ := fun x => (K.kernel x A).toReal
  set c : ℝ := hD.ε * (π A).toReal
  have hf_asm : AEStronglyMeasurable f μ :=
    ((Measure.measurable_coe hA).comp K.measurable).ennreal_toReal.aestronglyMeasurable
  have hf_int : ∀ (ν : Measure X), IsProbabilityMeasure ν → Integrable f ν :=
    fun ν _ => (integrable_const (1:ℝ)).mono
      ((Measure.measurable_coe hA).comp K.measurable |>.ennreal_toReal.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        simp [f, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one ▸ prob_le_one))
  have hcancel : ∫ x, f x ∂μ - ∫ x, f x ∂π =
      (∫ x, (f x - c) ∂μ) - (∫ x, (f x - c) ∂π) := by
    rw [integral_sub (hf_int μ ‹_›) (integrable_const c),
        integral_sub (hf_int π ‹_›) (integrable_const c)]
    simp [integral_const, IsProbabilityMeasure.measure_univ]
  rw [hcancel]
  -- g(x) = f(x) - c ∈ [0, 1-ε]
  have hg_nn : ∀ x, 0 ≤ f x - c := fun x => by
    simp [f, c]; exact hD.minorize x A hA
  have hg_le : ∀ x, f x - c ≤ 1 - hD.ε := fun x => by
    simp [f, c]
    -- f(x) = K(x,A).toReal ≤ 1 - ε·(1-π(A).toReal) = 1-ε+ε·π(A).toReal
    -- i.e., f(x) - ε·π(A).toReal ≤ 1-ε
    -- From complement: K(x,Aᶜ) ≥ ε·π(Aᶜ), so K(x,A) ≤ 1-ε·π(Aᶜ) = 1-ε+ε·π(A)
    -- K(x,Aᶜ) ≥ ε·π(Aᶜ), so K(x,A) = 1 - K(x,Aᶜ) ≤ 1 - ε·π(Aᶜ) = 1 - ε + ε·π(A)
    -- f(x) - c = K(x,A).toReal - ε·π(A).toReal ≤ 1-ε
    -- K(x,Aᶜ) ≥ ε·π(Aᶜ) so K(x,A) ≤ 1-ε+ε·π(A), giving f(x)-c ≤ 1-ε
    have hAc := hD.minorize x Aᶜ hA.compl
    have hKA_le : (K.kernel x A).toReal ≤ 1 - hD.ε + hD.ε * (π A).toReal := by
      have hK_one : (K.kernel x A).toReal + (K.kernel x Aᶜ).toReal = 1 := by
        rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
            ← measure_union (disjoint_compl_right) hA.compl,
            Set.union_compl_self, measure_univ, ENNReal.toReal_one]
      have hπ_one : (π A).toReal + (π Aᶜ).toReal = 1 := by
        rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
            ← measure_union (disjoint_compl_right) hA.compl,
            Set.union_compl_self, measure_univ, ENNReal.toReal_one]
      -- K(x,Aᶜ) ≥ ε·π(Aᶜ) = ε·(1-π(A)), K(x,A) = 1-K(x,Aᶜ) ≤ 1-ε+ε·π(A)
      have h1 : (K.kernel x Aᶜ).toReal ≥ hD.ε * (1 - (π A).toReal) := by
        rw [← hπ_one]; linarith [hAc]
      linarith [hK_one]
    -- hKA_le : f x ≤ 1-ε+c, goal: f x - c ≤ 1-ε. Direct algebra.
    linarith [hKA_le]
  have hf_meas : Measurable f := (Measure.measurable_coe hA).comp K.measurable |>.ennreal_toReal
  exact tv_integral_bound μ π (fun x => f x - c) (hf_meas.sub measurable_const)
    (1 - hD.ε) (by linarith [hD.hε_le])
    ((hf_int μ ‹_›).sub (integrable_const c)) ((hf_int π ‹_›).sub (integrable_const c))
    hg_nn hg_le δ hδ_nn hδ

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
  -- Iterates of probability measures are probability measures
  -- (bind of prob measures is prob — standard but needs AEMeasurable K.kernel)
  have h_prob : ∀ m, IsProbabilityMeasure (K.transferOp^[m] (Measure.dirac x)) := by
    intro m; induction m with
    | zero => simp; infer_instance
    | succ k ih =>
        rw [Function.iterate_succ']
        have := ih
        constructor
        show ((K.transferOp ∘ K.transferOp^[k]) (Measure.dirac x)) Set.univ = 1
        simp only [Function.comp_apply, MarkovKernel.transferOp]
        rw [Measure.bind_apply MeasurableSet.univ K.measurable.aemeasurable]
        simp [measure_univ]
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
