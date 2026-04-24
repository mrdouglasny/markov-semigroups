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

set_option linter.unusedSimpArgs false

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
    (ε : ℝ) (_hε : 0 < ε) (hε1 : ε ≤ 1)
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

/-- Iterates of a Markov kernel applied to a Dirac measure are probability measures. -/
theorem iteratePoint_isProbabilityMeasure {X : Type*} [MeasurableSpace X]
    (K : MarkovKernel X) (n : ℕ) (x : X) :
    IsProbabilityMeasure (K.iteratePoint n x) := by
  induction n with
  | zero => simp [MarkovKernel.iteratePoint]; infer_instance
  | succ k ih =>
    simp only [MarkovKernel.iteratePoint, Function.iterate_succ', Function.comp_apply,
      MarkovKernel.transferOp]
    constructor
    change ((K.transferOp ∘ K.transferOp^[k]) (Measure.dirac x)) Set.univ = 1
    simp only [Function.comp_apply, MarkovKernel.transferOp,
      Measure.bind_apply MeasurableSet.univ K.measurable.aemeasurable]
    have : IsProbabilityMeasure (K.transferOp^[k] (Measure.dirac x)) := ih
    simp [measure_univ]

/-- Bounded measurable function is integrable on any probability measure. -/
theorem integrable_of_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    Integrable f μ :=
  (integrable_const B).mono hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact le_trans (hB x) (le_abs_self B))

/-! ## Correlation decay

For a stationary Markov chain (X_t) with transition kernel K and
invariant measure π, the time-separated correlation is:

  E_π[f₁(X₀) · f₂(X_d)] = ∫_x f₁(x) · (∫_y f₂(y) dK^d(x,·)) dπ(x)

The second integral uses the d-step kernel K.iteratePoint d x. -/

/-- The conditional expectation of f₂ at time d given X₀ = x:
  E[f₂(X_d) | X₀ = x] = ∫ f₂ d(K^d(x, ·)). -/
def conditionalExpectation {X : Type*} [MeasurableSpace X]
    (K : MarkovKernel X) (f : X → ℝ) (d : ℕ) (x : X) : ℝ :=
  ∫ y, f y ∂(K.iteratePoint d x)

/-- **Correlation decay for time-separated observables (PROVEN).**

For bounded f₁, f₂ and the Markov chain with kernel K:
|∫ f₁(x) · E[f₂|X_d=·](x) dπ - (∫f₁ dπ)(∫f₂ dπ)| ≤ 2B²(1-ε)^d.

Proof:
1. By n-step mixing: |E[f₂|X₀=x] - E_π[f₂]| ≤ 2B(1-ε)^d for all x.
   (Uses doeblin_n_step_mixing + tv_integral_bound on f₂.)
2. |∫ f₁(x)(E[f₂|X₀=x] - E_π[f₂]) dπ| ≤ ∫ |f₁(x)| · 2B(1-ε)^d dπ
   ≤ B · 2B(1-ε)^d = 2B²(1-ε)^d. -/
theorem doeblin_correlation_decay {X : Type*} [MeasurableSpace X]
    {K : MarkovKernel X} {π : Measure X} [IsProbabilityMeasure π]
    (hD : DoeblinCondition K π)
    (h_inv : ∀ (A : Set X), MeasurableSet A → (π.bind K.kernel) A = π A)
    (f₁ f₂ : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf1 : Measurable f₁) (hf2 : Measurable f₂)
    (hB1 : ∀ x, |f₁ x| ≤ B) (hB2 : ∀ x, |f₂ x| ≤ B)
    (d : ℕ) :
    |∫ x, f₁ x * conditionalExpectation K f₂ d x ∂π -
     (∫ x, f₁ x ∂π) * (∫ x, f₂ x ∂π)| ≤
      2 * B ^ 2 * (1 - hD.ε) ^ d := by
  -- Abbreviations
  set Ef₂ := ∫ y, f₂ y ∂π
  set CE := conditionalExpectation K f₂ d
  -- Step 1: Rewrite LHS = |∫ f₁(x) * (CE(x) - Ef₂) dπ|
  have h_rewrite : ∫ x, f₁ x * CE x ∂π - (∫ x, f₁ x ∂π) * Ef₂ =
      ∫ x, f₁ x * (CE x - Ef₂) ∂π := by
    simp only [mul_sub]
    rw [integral_sub
      (by -- Integrable (f₁ * CE) π: both bounded, product bounded by B²
          exact (integrable_const (B * B)).mono
            (by
              have h_iter_meas : Measurable (K.iteratePoint d) := by
                have h_transfer_meas : Measurable (K.transferOp^[d]) := by
                  induction d with
                  | zero => simpa using measurable_id
                  | succ d ih =>
                      simpa [MarkovKernel.transferOp, Function.iterate_succ] using
                        ih.comp (Measure.measurable_bind' K.measurable)
                simpa [MarkovKernel.iteratePoint] using
                  h_transfer_meas.comp Measure.measurable_dirac
              have h_plus : Measurable fun x =>
                  ENNReal.toReal (∫⁻ y, ENNReal.ofReal (f₂ y) ∂(K.iteratePoint d x)) :=
                Measurable.ennreal_toReal <|
                  (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf2)).comp
                    h_iter_meas
              have h_minus : Measurable fun x =>
                  ENNReal.toReal (∫⁻ y, ENNReal.ofReal (-f₂ y) ∂(K.iteratePoint d x)) :=
                Measurable.ennreal_toReal <|
                  (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf2.neg)).comp
                    h_iter_meas
              have hCE_meas : Measurable fun x => ∫ y, f₂ y ∂(K.iteratePoint d x) := by
                convert h_plus.sub h_minus using 1
                funext x
                letI := iteratePoint_isProbabilityMeasure K d x
                rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part
                  (integrable_of_bound hf2 hB2)]
              exact (hf1.mul hCE_meas).stronglyMeasurable.aestronglyMeasurable) -- AEStronglyMeasurable of f₁ * conditionalExpectation
                       -- (measurability of parametric integral x ↦ ∫f₂ dK^d(x,·))
            (Filter.Eventually.of_forall fun x => by
              rw [Real.norm_eq_abs]; simp [abs_mul]
              have hCE_bound : |CE x| ≤ B := by
                simp only [CE, conditionalExpectation]
                have := iteratePoint_isProbabilityMeasure K d x
                calc |∫ y, f₂ y ∂(K.iteratePoint d x)|
                    ≤ ∫ y, |f₂ y| ∂(K.iteratePoint d x) := abs_integral_le_integral_abs
                  _ ≤ ∫ _, B ∂(K.iteratePoint d x) :=
                      integral_mono (integrable_of_bound hf2 hB2).norm
                        (integrable_const B) hB2
                  _ = B := by simp [integral_const, IsProbabilityMeasure.measure_univ]
              exact mul_le_mul (hB1 x) hCE_bound (abs_nonneg _) hB))
      (Integrable.mul_const ((integrable_const B).mono hf1.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact le_trans (hB1 x) (le_abs_self B))) Ef₂)]
    congr 1
    rw [integral_mul_const]
  rw [h_rewrite]
  -- Step 2: Pointwise bound |CE(x) - Ef₂| ≤ 2B(1-ε)^d
  -- This uses tv_integral_bound on (f₂+B) ∈ [0,2B] shifted,
  -- or directly from doeblin_n_step_mixing.
  have h_pw : ∀ x, |CE x - Ef₂| ≤ 2 * B * (1 - hD.ε) ^ d := by
    intro x
    -- IsProbabilityMeasure of K^d(x,·) — same proof as in doeblin_n_step_mixing
    have : IsProbabilityMeasure (K.iteratePoint d x) := iteratePoint_isProbabilityMeasure K d x
    -- Apply tv_integral_bound_abs with |f₂| ≤ B and TV gap (1-ε)^d
    simp only [conditionalExpectation, CE]
    exact tv_integral_bound_abs (K.iteratePoint d x) π f₂ hf2 B hB
      (integrable_of_bound hf2 hB2) (integrable_of_bound hf2 hB2)
      hB2
      ((1 - hD.ε)^d) (pow_nonneg (by linarith [hD.hε_le]) d)
      (doeblin_n_step_mixing hD h_inv d x)
  -- Step 3: |∫ f₁ * (CE - Ef₂) dπ| ≤ ∫ |f₁| * |CE - Ef₂| dπ ≤ B * 2B(1-ε)^d
  calc |∫ x, f₁ x * (CE x - Ef₂) ∂π|
      ≤ ∫ x, |f₁ x * (CE x - Ef₂)| ∂π :=
        abs_integral_le_integral_abs
    _ = ∫ x, |f₁ x| * |CE x - Ef₂| ∂π := by
        congr 1; ext x; exact abs_mul (f₁ x) (CE x - Ef₂)
    _ ≤ ∫ x, B * (2 * B * (1 - hD.ε) ^ d) ∂π := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun x => by positivity)
        · exact integrable_const _
        · exact Filter.Eventually.of_forall (fun x => by
            exact mul_le_mul (hB1 x) (h_pw x) (abs_nonneg _) hB)
    _ = 2 * B ^ 2 * (1 - hD.ε) ^ d := by
        simp [integral_const, IsProbabilityMeasure.measure_univ]
        ring

end
