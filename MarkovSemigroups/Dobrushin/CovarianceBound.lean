/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dobrushin Covariance Bound -- Building Blocks

Proves key lemmas for the Dobrushin covariance bound using the
single-site disintegration (M1).

## References

- Georgii (1988), Gibbs Measures and Phase Transitions, section 8
- Dobrushin (1968), uniqueness via influence matrix
-/

import MarkovSemigroups.Dobrushin.NeumannSeries
import MarkovSemigroups.Tools.SingleSiteDisintegration

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MeasureTheory SingleSiteDisintegration

noncomputable section

variable {I : Type*} [DecidableEq I] {S : Type*} [MeasurableSpace S]

/-! ## Basic integral bounds -/

/-- |integral f dmu| <= B for bounded integrable f on probability space. -/
lemma abs_integral_le_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (B : ℝ) (hB : ∀ x, |f x| ≤ B) (hf : Integrable f μ) :
    |∫ x, f x ∂μ| ≤ B := by
  calc |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := norm_integral_le_integral_norm f
    _ ≤ ∫ x, B ∂μ := by
        apply integral_mono (hf.abs) (integrable_const B); exact fun x => hB x
    _ = B := by simp

/-! ## Conditional measure support -/

/-- On condSingleSiteMeasure mu x a, sigma(x) = a a.e. -/
lemma ae_mem_fiber_condSingleSite
    [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) (x : I) (a : S) :
    ∀ᵐ σ ∂(condSingleSiteMeasure μ x a), σ x = a := by
  suffices h : condSingleSiteMeasure μ x a {σ : SpinConfig I S | σ x = a}ᶜ = 0 by exact h
  simp only [condSingleSiteMeasure, Measure.smul_apply, smul_eq_mul]
  suffices h : μ.restrict (fiber x a) {σ : SpinConfig I S | σ x = a}ᶜ = 0 by rw [h, mul_zero]
  rw [Measure.restrict_apply' (measurableSet_fiber x a)]
  convert measure_empty (α := SpinConfig I S) (μ := μ)
  ext σ; simp [fiber, evalAt, Set.mem_preimage, Set.mem_compl_iff]

/-- x-local f = f(sigma_0) a.e. under condSingleSiteMeasure. -/
lemma local_fn_ae_const
    [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) (x : I) (a : S)
    (f : SpinConfig I S → ℝ)
    (hf_local : ∀ σ τ : SpinConfig I S, σ x = τ x → f σ = f τ)
    (σ₀ : SpinConfig I S) (hσ₀ : σ₀ x = a) :
    ∀ᵐ σ ∂(condSingleSiteMeasure μ x a), f σ = f σ₀ := by
  filter_upwards [ae_mem_fiber_condSingleSite μ x a] with σ hσ
  exact hf_local σ σ₀ (by rw [hσ, hσ₀])

/-- Integral of x-local function on conditional = f(sigma_0). -/
lemma integral_local_eq_const
    [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) [IsFiniteMeasure μ]
    (x : I) (a : S) (f : SpinConfig I S → ℝ)
    (hf_local : ∀ σ τ : SpinConfig I S, σ x = τ x → f σ = f τ)
    (σ₀ : SpinConfig I S) (hσ₀ : σ₀ x = a)
    (hpos : μ (fiber x a) ≠ 0) :
    ∫ σ, f σ ∂(condSingleSiteMeasure μ x a) = f σ₀ := by
  have hne_top : μ (fiber x a) ≠ ⊤ := (measure_lt_top μ (fiber x a)).ne
  have _ := isProbabilityMeasure_condSingleSiteMeasure μ x a hpos hne_top
  rw [integral_congr_ae (local_fn_ae_const μ x a f hf_local σ₀ hσ₀)]
  simp [measure_univ]

/-- integral(f*g)(cond) = f(sigma_0) * integral(g)(cond) for f x-local. -/
lemma integral_local_mul
    [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) [IsFiniteMeasure μ]
    (x : I) (a : S) (f g : SpinConfig I S → ℝ)
    (hf_local : ∀ σ τ : SpinConfig I S, σ x = τ x → f σ = f τ)
    (σ₀ : SpinConfig I S) (hσ₀ : σ₀ x = a)
    (hpos : μ (fiber x a) ≠ 0)
    (hg_int : Integrable g (condSingleSiteMeasure μ x a)) :
    ∫ σ, f σ * g σ ∂(condSingleSiteMeasure μ x a) =
      f σ₀ * ∫ σ, g σ ∂(condSingleSiteMeasure μ x a) := by
  have hne_top : μ (fiber x a) ≠ ⊤ := (measure_lt_top μ (fiber x a)).ne
  have _ := isProbabilityMeasure_condSingleSiteMeasure μ x a hpos hne_top
  have hae : ∀ᵐ σ ∂(condSingleSiteMeasure μ x a), f σ * g σ = f σ₀ * g σ := by
    filter_upwards [local_fn_ae_const μ x a f hf_local σ₀ hσ₀] with σ hσ; rw [hσ]
  rw [integral_congr_ae hae, integral_const_mul]

/-! ## Fiber mass summation -/

/-- fiber_toReal_tsum_eq_one: sum w(a) = 1 for probability measure. -/
lemma fiber_toReal_tsum_eq_one
    [Countable S] [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (x : I) :
    ∑' a : S, (μ (fiber x a)).toReal = 1 := by
  have h := tsum_integral_condSingleSiteMeasure μ x (integrable_const (1 : ℝ))
  -- LHS of h: integral of 1 wrt mu = 1 (probability measure)
  -- RHS of h: sum_a w(a) * (integral of 1 wrt cond_a)
  -- For positive-mass fibers, cond_a is a probability measure so integral of 1 = 1.
  -- For zero-mass fibers, w(a) = 0 so the term is 0.
  -- Therefore sum = sum_a w(a).
  have hlhs : ∫ σ, (1 : ℝ) ∂μ = 1 := by simp
  rw [hlhs] at h
  rw [h]
  apply tsum_congr; intro a
  by_cases ha : μ (fiber x a) = 0
  · simp [ha, ENNReal.toReal_eq_zero_iff]
  · have hne_top : μ (fiber x a) ≠ ⊤ := (measure_lt_top μ (fiber x a)).ne
    have hprob := isProbabilityMeasure_condSingleSiteMeasure μ x a ha hne_top
    have : ∫ σ, (1 : ℝ) ∂(condSingleSiteMeasure μ x a) = 1 := by simp
    rw [this, smul_eq_mul, mul_one]

/-! ## Covariance bound -/

/-- **Covariance bound via bridge hypothesis.**

For f x-local with |f| <= Bf:

    |Cov(f,g)| <= Bf * K

whenever |E[g|sigma(x)=a] - E[g]| <= K for all positive-mass fibers. -/
lemma covariance_bound_via_bridge
    [Countable S] [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (f g : SpinConfig I S → ℝ)
    (Bf : ℝ) (hBf_nn : 0 ≤ Bf) (hBf : ∀ σ, |f σ| ≤ Bf)
    (x : I) (hf_local : ∀ σ τ : SpinConfig I S, σ x = τ x → f σ = f τ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun σ => f σ * g σ) μ)
    (K : ℝ) (hK_nn : 0 ≤ K)
    (hcond_bound : ∀ a : S, μ (fiber x a) ≠ 0 →
      |∫ σ, g σ ∂(condSingleSiteMeasure μ x a) - ∫ σ, g σ ∂μ| ≤ K)
    (choose_σ : S → SpinConfig I S) (h_choose : ∀ a, (choose_σ a) x = a)
    (hg_cond : ∀ a, μ (fiber x a) ≠ 0 →
      Integrable g (condSingleSiteMeasure μ x a)) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)| ≤ Bf * K := by
  -- Use the norm bound: |Cov(f,g)| = |E[f*(g-Eg)]| ≤ E[|f|*|g-Eg|]
  --                     ≤ Bf * E[|g - Eg|]
  -- But we need a tighter bound using the conditional structure.
  --
  -- Alternative: bound directly from the M1 decomposition.
  -- E[f*g] - E[f]*E[g] = E[f*(g-Eg)]
  -- = sum_a w(a) * integral(f*(g-Eg))(cond_a)           [M1]
  -- = sum_a w(a) * f_a * (E_a[g] - Eg)                  [f x-local]
  --
  -- |Cov| ≤ sum_a w(a) * |f_a| * |E_a[g] - Eg|
  --       ≤ sum_a w(a) * Bf * K = Bf * K * sum w = Bf * K
  --
  -- The difficulty is proving |tsum h| ≤ tsum |h|. Instead of
  -- doing this at the tsum level, we bound the integral directly.

  set Eg := ∫ σ, g σ ∂μ

  -- Step 1: |Cov(f,g)| = |E[f*(g - Eg)]| (centering identity)
  have hfEg : Integrable (fun σ => f σ * Eg) μ := by
    have : (fun σ => f σ * Eg) = fun σ => Eg * f σ := by ext σ; ring
    rw [this]; exact hf.const_mul Eg
  have hfgc : Integrable (fun σ => f σ * (g σ - Eg)) μ := by
    have : (fun σ => f σ * (g σ - Eg)) = fun σ => f σ * g σ - Eg * f σ := by
      ext σ; ring
    rw [this]; exact hfg.sub (hf.const_mul Eg)
  have cov_eq : ∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * Eg =
      ∫ σ, f σ * (g σ - Eg) ∂μ := by
    have h1 : ∫ σ, f σ * (g σ - Eg) ∂μ =
        ∫ σ, (f σ * g σ - Eg * f σ) ∂μ := by
      apply integral_congr_ae; filter_upwards with σ; ring
    rw [h1, integral_sub hfg (hf.const_mul Eg)]
    have h2 : ∫ σ, Eg * f σ ∂μ = Eg * ∫ σ, f σ ∂μ := integral_const_mul Eg f
    linarith
  rw [cov_eq]

  -- Step 2: Decompose via M1 and factor f out on each fiber.
  have hfgc_dec := tsum_integral_condSingleSiteMeasure μ x hfgc

  have hterm : ∀ a : S,
      (μ (fiber x a)).toReal •
        ∫ σ, f σ * (g σ - Eg) ∂(condSingleSiteMeasure μ x a) =
      (μ (fiber x a)).toReal *
        (f (choose_σ a) * (∫ σ, g σ ∂(condSingleSiteMeasure μ x a) - Eg)) := by
    intro a
    by_cases ha : μ (fiber x a) = 0
    · simp [condSingleSiteMeasure, ha]
    · rw [smul_eq_mul]
      have hne_top : μ (fiber x a) ≠ ⊤ := (measure_lt_top μ (fiber x a)).ne
      have _ := isProbabilityMeasure_condSingleSiteMeasure μ x a ha hne_top
      have hae : ∀ᵐ σ ∂(condSingleSiteMeasure μ x a),
          f σ * (g σ - Eg) = f (choose_σ a) * (g σ - Eg) := by
        filter_upwards [local_fn_ae_const μ x a f hf_local (choose_σ a) (h_choose a)]
          with σ hσ; rw [hσ]
      rw [integral_congr_ae hae, integral_const_mul]
      congr 1
      rw [integral_sub (hg_cond a ha) (integrable_const Eg)]
      simp
  rw [hfgc_dec]; simp_rw [hterm]

  -- Step 3: Bound |tsum T| <= tsum |T| <= Bf * K.
  set T : S → ℝ := fun a => (μ (fiber x a)).toReal *
    (f (choose_σ a) * (∫ σ, g σ ∂(condSingleSiteMeasure μ x a) - Eg))

  -- Each |T(a)| <= w(a) * Bf * K
  have hTB : ∀ a, ‖T a‖ ≤ (μ (fiber x a)).toReal * (Bf * K) := by
    intro a; rw [Real.norm_eq_abs]
    by_cases ha : μ (fiber x a) = 0
    · simp [T, show (μ (fiber x a)).toReal = 0 from by
        rw [ENNReal.toReal_eq_zero_iff]; exact Or.inl ha]
    · rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      rw [abs_mul]
      exact mul_le_mul (hBf _) (hcond_bound a ha) (abs_nonneg _) hBf_nn

  -- Summability: fiber weights are summable as reals.
  have hw_summ : Summable (fun a => (μ (fiber x a)).toReal) := by
    apply ENNReal.summable_toReal
    -- Disjoint fibers: tsum mu(fiber) = mu(Union fiber) = mu(univ) = 1.
    have hdisj := pairwise_disjoint_fiber (I := I) (S := S) x
    have hmeas : ∀ a : S, MeasurableSet (fiber (I := I) (S := S) x a) := measurableSet_fiber x
    have heq : ∑' (a : S), μ (fiber x a) = μ Set.univ := by
      rw [← iUnion_fiber (I := I) (S := S) x]
      exact (measure_iUnion hdisj hmeas).symm
    rw [heq, measure_univ]; exact ENNReal.one_ne_top
  have hB_summ : Summable (fun a => (μ (fiber x a)).toReal * (Bf * K)) :=
    hw_summ.mul_right _
  have hT_summ : Summable T := Summable.of_norm_bounded hB_summ hTB
  have hTnorm_summ : Summable (fun a => ‖T a‖) :=
    Summable.of_nonneg_of_le (fun a => norm_nonneg _) hTB hB_summ

  calc |∑' a, T a|
      = ‖∑' a, T a‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' a, ‖T a‖ := norm_tsum_le_tsum_norm hTnorm_summ
    _ ≤ ∑' a, (μ (fiber x a)).toReal * (Bf * K) :=
        Summable.tsum_le_tsum hTB hTnorm_summ hB_summ
    _ = (∑' a, (μ (fiber x a)).toReal) * (Bf * K) := by
        rw [← tsum_mul_right]
    _ = 1 * (Bf * K) := by rw [fiber_toReal_tsum_eq_one μ x]
    _ = Bf * K := one_mul _

/-! ## Main theorem -/

/-- **Covariance bound with Neumann-series coefficient.**

    |Cov(f,g)| <= 2 * Bf * Bg * neumannSeriesCoeff gamma x y

assuming the conditional TV propagation bridge. -/
theorem covariance_le_neumannSeriesCoeff
    [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (f g : SpinConfig I S → ℝ)
    (Bf Bg : ℝ) (hBf_nn : 0 ≤ Bf) (hBg_nn : 0 ≤ Bg)
    (hBf : ∀ σ, |f σ| ≤ Bf) (hBg : ∀ σ, |g σ| ≤ Bg)
    (x y : I)
    (hf_local : ∀ σ τ, σ x = τ x → f σ = f τ)
    (hg_local : ∀ σ τ, σ y = τ y → g σ = g τ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun σ => f σ * g σ) μ)
    (choose_σ : S → SpinConfig I S) (h_choose : ∀ a, (choose_σ a) x = a)
    (hg_cond : ∀ a, μ (fiber x a) ≠ 0 →
      Integrable g (condSingleSiteMeasure μ x a))
    (hCondTV : ∀ a : S, μ (fiber x a) ≠ 0 →
      |∫ σ, g σ ∂(condSingleSiteMeasure μ x a) - ∫ σ, g σ ∂μ| ≤
        2 * Bg * neumannSeriesCoeff γ x y) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)| ≤
      2 * Bf * Bg * neumannSeriesCoeff γ x y := by
  have hK_nn : 0 ≤ 2 * Bg * neumannSeriesCoeff γ x y :=
    mul_nonneg (mul_nonneg (by norm_num) hBg_nn) (neumannSeriesCoeff_nonneg γ x y)
  calc |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)|
      ≤ Bf * (2 * Bg * neumannSeriesCoeff γ x y) :=
        covariance_bound_via_bridge μ f g Bf hBf_nn hBf x hf_local
          hf hg hfg _ hK_nn hCondTV choose_σ h_choose hg_cond
    _ = 2 * Bf * Bg * neumannSeriesCoeff γ x y := by ring

end
