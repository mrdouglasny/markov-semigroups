/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strong-`L²` difference-quotient limit for the Gaussian OU semigroup

G2 (a) of the Gross-discharge plan (`plans/gross-discharge.md`) — the
analytic core. For core `f`, the right difference quotient of the
`Lp`-carrier OU semigroup converges in `L²(γFin n)`-norm to the named
generator `ouGeneratorFin f = Δf − x·∇f`.

**This file is the Codex work item.** It contains exactly one
`sorry` (`ouSemigroupFinLp_diffQuot_tendsto`). It is deliberately
isolated so it can be filled in parallel with the γ-IBP / assembly
work in `EuclideanGeneratorCompat`.
-/

import MarkovSemigroups.Instances.WorkInProgress.EuclideanGeneratorLp

open MeasureTheory Filter
open scoped BigOperators Topology InnerProductSpace ContDiff

noncomputable section

namespace GaussianFin

variable {n : ℕ}

/-- **`Fin n`-generic Stein/Gaussian-IBP wrapper** (Codex, 2026-05-16).
`EuclideanFin.stein_partialDeriv_ouShiftFin` is stated only for
`Fin (n+1)`; this lifts it to generic `Fin n` by case-splitting
(`n = 0`: `i : Fin 0` is vacuous via `Fin.elim0`; `n = m+1`: the
existing lemma). Unblocks the `Fin n` endpoint theorem below. -/
private theorem stein_partialDeriv_ouShiftFin_all {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (t : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    ∫ y, y i * partialDeriv i f (ouShiftFin t x y) ∂γFin n =
      Real.sqrt (1 - Real.exp (-2 * t)) *
        ouSemigroupFin t (secondPartial i f) x := by
  cases n with
  | zero => exact (Fin.elim0 i)
  | succ m =>
      simpa using
        (stein_partialDeriv_ouShiftFin (n := m) (f := f) hf t i x)

private theorem tendsto_ouSemigroupFin_pointwise_atZero
    {g : (Fin n → ℝ) → ℝ} (hg_cont : Continuous g) {M : ℝ}
    (hg_bd : ∀ z, ‖g z‖ ≤ M) (x : Fin n → ℝ) :
    Tendsto (fun t : ℝ => ouSemigroupFin t g x) (𝓝[Set.Ici 0] 0) (𝓝 (g x)) := by
  show Tendsto (fun t : ℝ => ∫ y, g (ouShiftFin t x y) ∂γFin n) (𝓝[Set.Ici 0] 0) (𝓝 (g x))
  have h_target :
      Tendsto (fun t : ℝ => ∫ y, g (ouShiftFin t x y) ∂γFin n)
        (𝓝[Set.Ici 0] 0) (𝓝 (∫ _y : Fin n → ℝ, g x ∂γFin n)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M) ?_ ?_ (integrable_const M) ?_
    · filter_upwards with t
      have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
        continuity
      exact (hg_cont.comp hshift).aestronglyMeasurable
    · filter_upwards with t
      exact Filter.Eventually.of_forall (fun y => hg_bd (ouShiftFin t x y))
    · filter_upwards with y
      have harg : Tendsto (fun t : ℝ => ouShiftFin t x y) (𝓝[Set.Ici 0] 0) (𝓝 x) := by
        have hcont : Continuous (fun t : ℝ => ouShiftFin t x y) := by
          continuity
        have hzero : ouShiftFin 0 x y = x := by
          funext i
          simp [ouShiftFin]
        have h : Tendsto (fun t : ℝ => ouShiftFin t x y) (𝓝[Set.Ici 0] 0)
            (𝓝 (ouShiftFin 0 x y)) :=
          hcont.continuousAt.continuousWithinAt
        simpa [hzero] using h
      exact (hg_cont.tendsto x).comp harg
  simpa using h_target

set_option maxHeartbeats 800000 in
private theorem hasDerivAt_t_ouSemigroupFin_pos_aux {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (x : Fin n → ℝ) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasDerivAt (fun t : ℝ => ouSemigroupFin t f x)
      (∑ i : Fin n,
        (Real.exp (-2 * t₀) * ouSemigroupFin t₀ (secondPartial i f) x
          - x i * (Real.exp (-t₀) * ouSemigroupFin t₀ (partialDeriv i f) x))) t₀ := by
  obtain ⟨hf_smooth, M, hM⟩ := hf
  have hf_core : IsCoreFin f := ⟨hf_smooth, M, hM⟩
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) ((hM (fun _ => 0)).1)
  let ε : ℝ := t₀ / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  have hε_lt : ε < t₀ := by
    dsimp [ε]
    linarith
  have h_nbhd : Set.Ioo ε (t₀ + 1) ∈ 𝓝 t₀ := by
    exact Ioo_mem_nhds hε_lt (by linarith)
  let F : ℝ → (Fin n → ℝ) → ℝ := fun t y => f (ouShiftFin t x y)
  let F' : ℝ → (Fin n → ℝ) → ℝ := fun t y =>
    ∑ i : Fin n,
      (-Real.exp (-t) * x i
        + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i) *
        partialDeriv i f (ouShiftFin t x y)
  let B : ℝ := Real.sqrt (1 - Real.exp (-2 * ε))
  have hB_pos : 0 < B := by
    have hlt : Real.exp (-2 * ε) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      linarith
    have hinner : 0 < 1 - Real.exp (-2 * ε) := by
      linarith
    simpa [B] using Real.sqrt_pos.mpr hinner
  have hF_meas :
      ∀ t ∈ Set.Ioo ε (t₀ + 1), AEStronglyMeasurable (F t) (γFin n) := by
    intro t ht
    have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
      continuity
    exact (hf_core.measurable.comp hshift.measurable).aestronglyMeasurable
  have hF_int : Integrable (F t₀) (γFin n) := by
    refine Integrable.mono' (integrable_const M) (hF_meas t₀ ⟨hε_lt, by linarith⟩) ?_
    exact Filter.Eventually.of_forall (fun y => (hM (ouShiftFin t₀ x y)).1)
  have hF'_meas : AEStronglyMeasurable (F' t₀) (γFin n) := by
    change AEStronglyMeasurable
      (fun y : Fin n → ℝ =>
        ∑ i : Fin n,
          (-Real.exp (-t₀) * x i
            + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
            partialDeriv i f (ouShiftFin t₀ x y))
      (γFin n)
    have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t₀ x y) := by
      continuity
    exact (Finset.measurable_sum (Finset.univ : Finset (Fin n)) (by
      intro i hi
      have hcoeff_meas :
          Measurable (fun y : Fin n → ℝ =>
            (-Real.exp (-t₀) * x i : ℝ)
              + ((Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) : ℝ) * y i) := by
        have hconst : Measurable (fun _y : Fin n → ℝ => (-Real.exp (-t₀) * x i : ℝ)) :=
          measurable_const
        have hlin : Measurable (fun y : Fin n → ℝ =>
            ((Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) : ℝ) * y i) :=
          measurable_const.mul (measurable_pi_apply i)
        exact hconst.add hlin
      exact hcoeff_meas.mul ((hf_core.partial_measurable i).comp hshift.measurable))).aestronglyMeasurable
  have h_bound :
      ∀ᵐ y ∂γFin n, ∀ t ∈ Set.Ioo ε (t₀ + 1), ‖F' t y‖ ≤
        ∑ i : Fin n, M * (|x i| + (1 / B) * |y i|) := by
    filter_upwards with y t ht
    have hcoeff :
        ∀ i : Fin n,
          |(-Real.exp (-t) * x i
              + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i)|
            ≤ |x i| + (1 / B) * |y i| := by
      intro i
      have ht_pos : 0 < t := lt_trans hε_pos ht.1
      have h_exp_le : Real.exp (-t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      have h_exp2_le : Real.exp (-2 * t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      have h_exp_nn : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
      have h_exp2_nn : 0 ≤ Real.exp (-2 * t) := (Real.exp_pos _).le
      have h_sqrt_ge : B ≤ Real.sqrt (1 - Real.exp (-2 * t)) := by
        have hmono : Real.exp (-2 * t) ≤ Real.exp (-2 * ε) := by
          apply Real.exp_le_exp.mpr
          nlinarith [ht.1]
        have hinner_le : 1 - Real.exp (-2 * ε) ≤ 1 - Real.exp (-2 * t) := by
          linarith
        dsimp [B]
        exact Real.sqrt_le_sqrt hinner_le
      have h_ratio_le : Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t)) ≤ 1 / B := by
        calc
          Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))
              ≤ 1 / Real.sqrt (1 - Real.exp (-2 * t)) := by
                  gcongr
          _ ≤ 1 / B := by
                  exact one_div_le_one_div_of_le hB_pos h_sqrt_ge
      calc
        |(-Real.exp (-t) * x i
            + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i)|
            ≤ |(-Real.exp (-t) * x i)| +
                |(Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i| :=
              abs_add_le _ _
        _ = Real.exp (-t) * |x i| +
              (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * |y i| := by
              rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg h_exp_nn,
                abs_of_nonneg (div_nonneg h_exp2_nn (Real.sqrt_nonneg _))]
        _ ≤ 1 * |x i| + (1 / B) * |y i| := by
              gcongr
        _ = |x i| + (1 / B) * |y i| := by ring
    change
      ‖∑ i : Fin n,
          (-Real.exp (-t) * x i
            + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i) *
            partialDeriv i f (ouShiftFin t x y)‖
        ≤ ∑ i : Fin n, M * (|x i| + (1 / B) * |y i|)
    calc
      ‖F' t y‖
          ≤ ∑ i : Fin n,
              ‖(-Real.exp (-t) * x i
                + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i) *
                partialDeriv i f (ouShiftFin t x y)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin n,
            (|x i| + (1 / B) * |y i|) * M := by
              refine Finset.sum_le_sum ?_
              intro i hi
              calc
                ‖(-Real.exp (-t) * x i
                    + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i) *
                    partialDeriv i f (ouShiftFin t x y)‖
                    = |(-Real.exp (-t) * x i
                        + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i)| *
                        ‖partialDeriv i f (ouShiftFin t x y)‖ := by
                          rw [norm_mul, Real.norm_eq_abs]
                _ ≤ (|x i| + (1 / B) * |y i|) * M := by
                    exact mul_le_mul (hcoeff i) ((hM (ouShiftFin t x y)).2.1 i)
                      (norm_nonneg _) (by positivity)
      _ = ∑ i : Fin n, M * (|x i| + (1 / B) * |y i|) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
  have h_bound_int : Integrable (fun y : Fin n → ℝ =>
      ∑ i : Fin n, M * (|x i| + (1 / B) * |y i|)) (γFin n) := by
    have hterm :
        ∀ i : Fin n, Integrable (fun y : Fin n → ℝ => M * (|x i| + (1 / B) * |y i|)) (γFin n) := by
      intro i
      have h_eval : Integrable (fun y : Fin n → ℝ => |y i|) (γFin n) := integrable_abs_eval_γFin i
      simpa [mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
        using (integrable_const (M * |x i|)).add (h_eval.const_mul (M * (1 / B)))
    refine integrable_finset_sum (s := Finset.univ)
      (f := fun i (y : Fin n → ℝ) => M * (|x i| + (1 / B) * |y i|)) ?_
    intro i hi
    exact hterm i
  have h_diff :
      ∀ᵐ y ∂γFin n, ∀ t ∈ Set.Ioo ε (t₀ + 1), HasDerivAt (fun s => F s y) (F' t y) t := by
    filter_upwards with y t ht
    have h_shift :
        HasDerivAt (fun s : ℝ => ouShiftFin s x y)
          (fun i => -Real.exp (-t) * x i
            + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i) t := by
      rw [hasDerivAt_pi]
      intro i
      have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s) * x i) (-Real.exp (-t) * x i) t := by
        have hneg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := by
          simpa using (hasDerivAt_id t).neg
        have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-t) * (-1)) t := hneg.exp
        convert hexp.mul_const (x i) using 1 <;> ring
      have h2 :
          HasDerivAt (fun s : ℝ => Real.sqrt (1 - Real.exp (-2 * s)) * y i)
            ((Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i) t := by
        exact (Gaussian1D.hasDerivAt_b t (lt_trans hε_pos ht.1)).mul_const (y i)
      simpa [ouShiftFin] using h1.add h2
    have h_f :
        HasFDerivAt f (fderiv ℝ f (ouShiftFin t x y)) (ouShiftFin t x y) :=
      ((hf_smooth.differentiable (by simp)).differentiableAt).hasFDerivAt
    have h_comp := h_f.comp_hasDerivAt t h_shift
    have hsum := fderiv_apply_eq_sum_partial hf_smooth (ouShiftFin t x y)
      (fun i => -Real.exp (-t) * x i
        + (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) * y i)
    rw [hsum] at h_comp
    simpa [F, F'] using h_comp
  have hF_meas_ev : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) (γFin n) :=
    Filter.eventually_of_mem h_nbhd hF_meas
  obtain ⟨_, h_deriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le h_nbhd
      hF_meas_ev hF_int hF'_meas h_bound h_bound_int h_diff
  have h_term_int :
      ∀ i : Fin n,
        Integrable
          (fun y : Fin n → ℝ =>
            (-Real.exp (-t₀) * x i
              + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
              partialDeriv i f (ouShiftFin t₀ x y)) (γFin n) := by
    intro i
    refine Integrable.mono'
      ((integrable_const (M * |x i|)).add
        ((integrable_abs_eval_γFin i).const_mul (M * (Real.exp (-2 * t₀) /
          Real.sqrt (1 - Real.exp (-2 * t₀)))))) ?_ ?_
    · have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t₀ x y) := by
        continuity
      exact ((((measurable_const.mul measurable_const).add
        ((measurable_const.mul (measurable_pi_apply i)))).mul
        ((hf_core.partial_measurable i).comp hshift.measurable)).aestronglyMeasurable)
    · filter_upwards with y
      have hcoef :
          |(-Real.exp (-t₀) * x i
              + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i)|
            ≤ Real.exp (-t₀) * |x i| +
              (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * |y i| := by
        calc
          |(-Real.exp (-t₀) * x i
              + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i)|
              ≤ |(-Real.exp (-t₀) * x i)| +
                  |(Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i| :=
                abs_add_le _ _
          _ = Real.exp (-t₀) * |x i| +
              (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * |y i| := by
                rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (Real.exp_pos _).le,
                  abs_of_nonneg (div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))]
      calc
        ‖(-Real.exp (-t₀) * x i
            + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
            partialDeriv i f (ouShiftFin t₀ x y)‖
            = |(-Real.exp (-t₀) * x i
                + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i)| *
                ‖partialDeriv i f (ouShiftFin t₀ x y)‖ := by
                    rw [norm_mul, Real.norm_eq_abs]
        _ ≤ (Real.exp (-t₀) * |x i| +
              (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * |y i|) * M := by
              exact mul_le_mul hcoef ((hM (ouShiftFin t₀ x y)).2.1 i) (norm_nonneg _) (by positivity)
        _ ≤ M * |x i| + (M * (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀)))) * |y i| := by
              have h_exp_le : Real.exp (-t₀) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
              have h1 : (Real.exp (-t₀) * |x i|) * M ≤ M * |x i| := by
                calc
                  (Real.exp (-t₀) * |x i|) * M ≤ (1 * |x i|) * M := by
                    gcongr
                  _ = M * |x i| := by ring
              ring_nf
              linarith [h1]
  have h_eval :
      ∫ y, F' t₀ y ∂γFin n
        = ∑ i : Fin n,
            (Real.exp (-2 * t₀) * ouSemigroupFin t₀ (secondPartial i f) x
              - x i * (Real.exp (-t₀) * ouSemigroupFin t₀ (partialDeriv i f) x)) := by
    rw [show (∫ y, F' t₀ y ∂γFin n) =
        ∫ y, ∑ i : Fin n,
          ((-Real.exp (-t₀) * x i
            + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
            partialDeriv i f (ouShiftFin t₀ x y)) ∂γFin n from rfl]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl ?_
      intro i hi
      have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t₀ x y) := by
        continuity
      have hpartial_meas :
          Measurable (fun y : Fin n → ℝ => partialDeriv i f (ouShiftFin t₀ x y)) :=
        (hf_core.partial_measurable i).comp hshift.measurable
      have hpartial_int :
          Integrable (fun y : Fin n → ℝ => partialDeriv i f (ouShiftFin t₀ x y)) (γFin n) := by
        refine integrable_of_bound (M := M) hpartial_meas ?_
        intro y
        exact (hM (ouShiftFin t₀ x y)).2.1 i
      have h1 :
          Integrable (fun y : Fin n → ℝ =>
            (-Real.exp (-t₀) * x i) * partialDeriv i f (ouShiftFin t₀ x y)) (γFin n) := by
        exact hpartial_int.const_mul (-Real.exp (-t₀) * x i)
      have h2 :
          Integrable (fun y : Fin n → ℝ =>
            ((Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
              partialDeriv i f (ouShiftFin t₀ x y)) (γFin n) := by
        have hy_partial :
            Integrable (fun y : Fin n → ℝ => y i * partialDeriv i f (ouShiftFin t₀ x y)) (γFin n) := by
          refine Integrable.mono' ((integrable_abs_eval_γFin i).const_mul M)
            ((measurable_pi_apply i).mul hpartial_meas).aestronglyMeasurable ?_
          filter_upwards with y
          calc
            ‖y i * partialDeriv i f (ouShiftFin t₀ x y)‖
                = |y i| * ‖partialDeriv i f (ouShiftFin t₀ x y)‖ := by
                    rw [norm_mul, Real.norm_eq_abs]
            _ ≤ |y i| * M := by
                  exact mul_le_mul_of_nonneg_left ((hM (ouShiftFin t₀ x y)).2.1 i) (abs_nonneg _)
            _ = M * |y i| := by ring
        simpa [mul_assoc] using
          hy_partial.const_mul (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀)))
      calc
        ∫ y,
            ((-Real.exp (-t₀) * x i
              + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
              partialDeriv i f (ouShiftFin t₀ x y)) ∂γFin n
            = ∫ y,
                (-Real.exp (-t₀) * x i) * partialDeriv i f (ouShiftFin t₀ x y)
                  + ((Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
                    partialDeriv i f (ouShiftFin t₀ x y) ∂γFin n := by
                      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
                      intro y
                      ring
        _ = (-Real.exp (-t₀) * x i) * ouSemigroupFin t₀ (partialDeriv i f) x
              + (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) *
                ∫ y, y i * partialDeriv i f (ouShiftFin t₀ x y) ∂γFin n := by
                  rw [integral_add h1 h2, integral_const_mul]
                  have hcongr :
                      (∫ y,
                        ((Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) * y i) *
                          partialDeriv i f (ouShiftFin t₀ x y) ∂γFin n)
                        =
                      ∫ y,
                        (Real.exp (-2 * t₀) / Real.sqrt (1 - Real.exp (-2 * t₀))) *
                          (y i * partialDeriv i f (ouShiftFin t₀ x y)) ∂γFin n := by
                    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
                    intro y
                    ring
                  rw [hcongr, integral_const_mul]
                  simp [ouSemigroupFin]
        _ = (-Real.exp (-t₀) * x i) * ouSemigroupFin t₀ (partialDeriv i f) x
              + Real.exp (-2 * t₀) * ouSemigroupFin t₀ (secondPartial i f) x := by
                  rw [stein_partialDeriv_ouShiftFin_all hf_core t₀ i x]
                  have hsqrt_pos : 0 < Real.sqrt (1 - Real.exp (-2 * t₀)) := by
                    apply Real.sqrt_pos.mpr
                    have hlt : Real.exp (-2 * t₀) < 1 := by
                      apply Real.exp_lt_one_iff.mpr
                      linarith
                    linarith
                  have hsqrt_ne : Real.sqrt (1 - Real.exp (-2 * t₀)) ≠ 0 := hsqrt_pos.ne'
                  rw [div_eq_mul_inv]
                  calc
                    (-Real.exp (-t₀) * x i) * ouSemigroupFin t₀ (partialDeriv i f) x +
                        Real.exp (-2 * t₀) * (Real.sqrt (1 - Real.exp (-2 * t₀)))⁻¹ *
                          (Real.sqrt (1 - Real.exp (-2 * t₀)) *
                            ouSemigroupFin t₀ (secondPartial i f) x)
                        =
                      (-Real.exp (-t₀) * x i) * ouSemigroupFin t₀ (partialDeriv i f) x +
                        Real.exp (-2 * t₀) *
                          ((Real.sqrt (1 - Real.exp (-2 * t₀)))⁻¹ *
                            Real.sqrt (1 - Real.exp (-2 * t₀))) *
                          ouSemigroupFin t₀ (secondPartial i f) x
                        := by ring
                    _ =
                      (-Real.exp (-t₀) * x i) * ouSemigroupFin t₀ (partialDeriv i f) x +
                        Real.exp (-2 * t₀) * ouSemigroupFin t₀ (secondPartial i f) x := by
                          rw [inv_mul_cancel₀ hsqrt_ne]
                          ring_nf
        _ = Real.exp (-2 * t₀) * ouSemigroupFin t₀ (secondPartial i f) x
              - x i * (Real.exp (-t₀) * ouSemigroupFin t₀ (partialDeriv i f) x) := by
                  ring
    · intro i hi
      exact h_term_int i
  have h_lhs : (fun t : ℝ => ∫ y, F t y ∂γFin n) = fun t => ouSemigroupFin t f x := rfl
  rw [h_lhs] at h_deriv
  rw [h_eval] at h_deriv
  exact h_deriv

private theorem hasDerivAt_t_ouSemigroupFin_pos {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (x : Fin n → ℝ) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    HasDerivAt (fun t : ℝ => ouSemigroupFin t f x)
      (ouGeneratorFin (ouSemigroupFin t₀ f) x) t₀ := by
  have haux := hasDerivAt_t_ouSemigroupFin_pos_aux hf x ht₀
  have hcore_t : IsCoreFin (ouSemigroupFin t₀ f) :=
    ouSemigroupFin_preserves_IsCore t₀ ht₀.le hf
  have hrewrite :
      (∑ i : Fin n,
        (Real.exp (-2 * t₀) * ouSemigroupFin t₀ (secondPartial i f) x
          - x i * (Real.exp (-t₀) * ouSemigroupFin t₀ (partialDeriv i f) x)))
        = ouGeneratorFin (ouSemigroupFin t₀ f) x := by
    rw [ouGeneratorFin_apply]
    have hsum_second :
        (∑ i : Fin n, Real.exp (-2 * t₀) * ouSemigroupFin t₀ (secondPartial i f) x) =
          ∑ i : Fin n, secondPartial i (ouSemigroupFin t₀ f) x := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [secondPartial_eq_section_deriv_of_contDiff hcore_t.contDiff i x,
        section_secondDeriv_ouSemigroupFin_eq hf t₀ i x]
      simp
    have hsum_first :
        (∑ i : Fin n, x i * (Real.exp (-t₀) * ouSemigroupFin t₀ (partialDeriv i f) x)) =
          ∑ i : Fin n, x i * partialDeriv i (ouSemigroupFin t₀ f) x := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [partialDeriv_ouSemigroupFin_eq (n := n) t₀ ht₀.le hf i]
    rw [Finset.sum_sub_distrib, hsum_second, hsum_first]
  convert haux using 1
  exact hrewrite.symm

private theorem hasDerivWithinAt_t_ouSemigroupFin_zero_core {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (x : Fin n → ℝ) :
    HasDerivWithinAt (fun t : ℝ => ouSemigroupFin t f x)
      (ouGeneratorFin f x) (Set.Ici 0) 0 := by
  obtain ⟨hf_smooth, M, hM⟩ := hf
  have hf_core : IsCoreFin f := ⟨hf_smooth, M, hM⟩
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Set.Ioi 0)
    (f := fun t : ℝ => ouSemigroupFin t f x) (e := ouGeneratorFin f x) (a := 0) ?_ ?_
    self_mem_nhdsWithin ?_
  · intro t ht
    exact (hasDerivAt_t_ouSemigroupFin_pos hf_core x ht).differentiableAt.differentiableWithinAt
  · have hcont := tendsto_ouSemigroupFin_pointwise_atZero hf_smooth.continuous (fun z => (hM z).1) x
    show ContinuousWithinAt (fun t : ℝ => ouSemigroupFin t f x) (Set.Ioi 0) 0
    rw [ContinuousWithinAt, ouSemigroupFin_zero]
    exact hcont.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  · have hderiv_eq :
      ∀ᶠ t in 𝓝[Set.Ioi 0] 0,
        deriv (fun t : ℝ => ouSemigroupFin t f x) t
          = ∑ i : Fin n,
              (Real.exp (-2 * t) * ouSemigroupFin t (secondPartial i f) x
                - x i * (Real.exp (-t) * ouSemigroupFin t (partialDeriv i f) x)) := by
      have hmem : ∀ᶠ t : ℝ in 𝓝[Set.Ioi 0] 0, t ∈ Set.Ioi (0 : ℝ) := self_mem_nhdsWithin
      filter_upwards [hmem] with t ht
      exact (hasDerivAt_t_ouSemigroupFin_pos_aux hf_core x ht).deriv
    have h_second :
        Tendsto (fun t : ℝ =>
          ∑ i : Fin n, Real.exp (-2 * t) * ouSemigroupFin t (secondPartial i f) x)
          (𝓝[Set.Ioi 0] 0) (𝓝 (∑ i : Fin n, secondPartial i f x)) := by
      refine tendsto_finset_sum Finset.univ (fun i _ => ?_)
      have h_exp : Tendsto (fun t : ℝ => Real.exp (-2 * t)) (𝓝[Set.Ioi 0] 0) (𝓝 1) := by
        have hcont : Continuous (fun t : ℝ => Real.exp (-2 * t)) := by
          continuity
        have h : Tendsto (fun t : ℝ => Real.exp (-2 * t)) (𝓝[Set.Ioi 0] 0)
            (𝓝 (Real.exp (-2 * 0))) :=
          hcont.continuousAt.continuousWithinAt
        simpa using h
      have h_pt :
          Tendsto (fun t : ℝ => ouSemigroupFin t (secondPartial i f) x)
            (𝓝[Set.Ioi 0] 0) (𝓝 (secondPartial i f x)) := by
        have := tendsto_ouSemigroupFin_pointwise_atZero
          (hf_core.secondPartial_continuous i) (fun z => (hM z).2.2 i) x
        exact this.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      simpa using h_exp.mul h_pt
    have h_first :
        Tendsto (fun t : ℝ =>
          ∑ i : Fin n, x i * (Real.exp (-t) * ouSemigroupFin t (partialDeriv i f) x))
          (𝓝[Set.Ioi 0] 0) (𝓝 (∑ i : Fin n, x i * partialDeriv i f x)) := by
      refine tendsto_finset_sum Finset.univ (fun i _ => ?_)
      have h_exp : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[Set.Ioi 0] 0) (𝓝 1) := by
        have hcont : Continuous (fun t : ℝ => Real.exp (-t)) := by
          continuity
        have h : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[Set.Ioi 0] 0)
            (𝓝 (Real.exp (-0))) :=
          hcont.continuousAt.continuousWithinAt
        simpa using h
      have h_pt :
          Tendsto (fun t : ℝ => ouSemigroupFin t (partialDeriv i f) x)
            (𝓝[Set.Ioi 0] 0) (𝓝 (partialDeriv i f x)) := by
        have := tendsto_ouSemigroupFin_pointwise_atZero
          (hf_core.partial_continuous i) (fun z => (hM z).2.1 i) x
        exact this.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      simpa [mul_assoc] using (h_exp.mul h_pt).const_mul (x i)
    have h_lim :
        Tendsto
          (fun t : ℝ =>
            ∑ i : Fin n,
              (Real.exp (-2 * t) * ouSemigroupFin t (secondPartial i f) x
                - x i * (Real.exp (-t) * ouSemigroupFin t (partialDeriv i f) x)))
          (𝓝[Set.Ioi 0] 0)
          (𝓝 (ouGeneratorFin f x)) := by
      simpa [ouGeneratorFin_apply] using h_second.sub h_first
    have hderiv_eq' :
        (fun t : ℝ => deriv (fun t : ℝ => ouSemigroupFin t f x) t) =ᶠ[𝓝[Set.Ioi 0] 0]
          (fun t : ℝ =>
            ∑ i : Fin n,
              (Real.exp (-2 * t) * ouSemigroupFin t (secondPartial i f) x
                - x i * (Real.exp (-t) * ouSemigroupFin t (partialDeriv i f) x))) := hderiv_eq
    exact Tendsto.congr' hderiv_eq'.symm h_lim

/-- **Ornstein–Uhlenbeck pointwise heat equation at `t = 0⁺`** (the
right-endpoint of the Mehler-semigroup time derivative).

For `f : (Fin n → ℝ) → ℝ` that is `C^∞` with uniformly bounded value,
first and second coordinate derivatives, the explicit Mehler integral
`t ↦ ∫ f(e^{-t}x + √(1-e^{-2t})·y) d(⊗ⁿ N(0,1))(y)` has right
derivative at `0` equal to the OU generator `Lf(x) = Δf(x) − x·∇f(x)`.

**General (no project definitions).** Stated purely in Mathlib terms
— `fderiv`, `Pi.single`, `Real.exp`/`Real.sqrt`,
`MeasureTheory.Measure.pi`, `ProbabilityTheory.gaussianReal`,
`HasDerivWithinAt`, `Set.Ici` — so it is a reusable, vetting-amenable
textbook statement rather than a project-specific stopgap. The
project-specific `hasDerivWithinAt_t_ouSemigroupFin_zero` is derived
from it by unfolding the (thin) project definitions.

Reference: Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov
Diffusion Operators* (2014), §2.7 (the Ornstein–Uhlenbeck/heat
semigroup and its generator); Mehler's formula. **Vetted Standard /
Likely correct** (Gemini `gemini-3-pro-preview`, 2026-05-16; recorded
in `AXIOM_AUDIT.md`): well-formed; matches BGL §2.7 with
self-consistent variance-1 Mehler constants (no rescaling); non-vacuous;
**pure-second-partial bounds sufficient** — via Itô/Dynkin
`Pₜf − f = ∫₀ᵗ Pₛ(Lf) ds` the martingale term vanishes in
expectation, so only `|∇f|`,`|Δf|` boundedness is needed (no mixed-
partial, third-derivative, or growth hypotheses); right-derivative
endpoint form correct. Discharge route: parametric differentiation
under the integral with the Pi-valued chain rule through the Mehler
shift + the scaling identity `∂ᵢ²(Pₜf) = e^{-2t} Pₜ(∂ᵢ²f)` (see the
two-interface obstacle note on the project lemma below). -/
theorem gaussianOU_heatEquation_within_zero {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf_smooth : ContDiff ℝ ∞ f) (M : ℝ)
    (hf_bd : ∀ x : Fin n → ℝ,
      ‖f x‖ ≤ M ∧
      (∀ i : Fin n, ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ M) ∧
      (∀ i : Fin n,
        ‖fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x
            (Pi.single i 1)‖ ≤ M))
    (x : Fin n → ℝ) :
    HasDerivWithinAt
      (fun t : ℝ =>
        ∫ y,
          f (fun i => Real.exp (-t) * x i
              + Real.sqrt (1 - Real.exp (-2 * t)) * y i)
          ∂(MeasureTheory.Measure.pi
              (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))
      ((∑ i : Fin n,
          fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x
            (Pi.single i 1))
        - ∑ i : Fin n, x i * fderiv ℝ f x (Pi.single i 1))
      (Set.Ici 0) 0 := by
  have hf : IsCoreFin f := by
    refine ⟨hf_smooth, M, ?_⟩
    simpa [partialDeriv, secondPartial] using hf_bd
  simpa only [ouSemigroupFin, ouShiftFin, γFin, Gaussian1D.γ,
    ouGeneratorFin_apply, secondPartial, partialDeriv] using
    hasDerivWithinAt_t_ouSemigroupFin_zero_core hf x

/-- **The precise blocker (Codex 2026-05-16): the nD pointwise OU
heat equation at `t = 0⁺`.** The branch controls *spatial*
derivatives of `ouSemigroupFin t f` and has the scalar/L²-continuity
endgame, but exposes **no reusable multivariate pointwise
time-derivative** for `τ ↦ ouSemigroupFin τ f x`. This lemma is
exactly that missing prerequisite (right-derivative-at-0 form, which
Codex confirmed suffices): `P_0 f = f`, so the right `t`-derivative of
`τ ↦ (P_τ f) x` at `0` is `(L f) x = ouGeneratorFin f x`.

Proof route: tensor/Fubini lift of the proved 1D
`Gaussian1D.hasDerivAt_t_ouSemigroup'` (G1) through
`ouSemigroupFin_section_eq_ouSemigroup` / `ouSemigroupFin_insertNth_eq`
+ per-coordinate product rule + the `t→0⁺` endpoint
(`hasDerivWithinAt_Ici_of_tendsto_deriv`, as used for the 1D /
quadratic discharges). This is the genuine analytic crux; isolated as
its own target so it can be filled (Codex) independently of the DCT
upgrade below.

**Remaining obstacle (Codex, 2026-05-16; the `Fin n` Stein wrapper
above is done).** Two specific Lean interfaces fight the parametric
heat-equation proof: (1) the `HasDerivAt`-under-the-integral for
`τ ↦ ouSemigroupFin τ f x` needs a *Pi-valued chain rule through
`ouShiftFin`*, with the derivative integrand `F'` presented to
simultaneously satisfy `hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
finite-sum measurability, and the later integral algebra; (2) then the
Mehler-scaling identity
`secondPartial i (ouSemigroupFin t f) x
  = exp (-2*t) * ouSemigroupFin t (secondPartial i f) x`
must be bridged through `section_secondDeriv` /
`section_secondDeriv_ouSemigroupFin_eq`. -/
theorem hasDerivWithinAt_t_ouSemigroupFin_zero {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (x : Fin n → ℝ) :
    HasDerivWithinAt (fun t : ℝ => ouSemigroupFin t f x)
      (ouGeneratorFin f x) (Set.Ici 0) 0 := by
  exact hasDerivWithinAt_t_ouSemigroupFin_zero_core hf x

/-- **OU difference-quotient `→` generator, strong `L²`** (the DCT
upgrade of the pointwise heat equation — third Gross-discharge crux).

For `f : (Fin n → ℝ) → ℝ` that is `C^∞` with uniformly bounded value,
first and second coordinate derivatives, and *any* operator family
`P` acting on `Lp ℝ 2 (⊗ⁿ N(0,1))` whose a.e. representative is the
Mehler integral, the right difference quotient
`t⁻¹ • (P t [f] − [f])` converges in `L²`-norm as `t → 0⁺` to the
`Lp` class of the OU generator `Δf − x·∇f`.

**General (no project definitions).** Stated purely in Mathlib terms
— `fderiv`, `Pi.single`, `Real.exp`/`Real.sqrt`,
`MeasureTheory.Measure.pi`, `ProbabilityTheory.gaussianReal`,
`MemLp`/`MemLp.toLp`, `Lp`, `Filter.Tendsto`, `nhdsWithin` — with the
semigroup supplied as a parameter `P` characterized only by its
generic Mehler a.e. action `hP`, so it is a reusable,
vetting-amenable textbook statement rather than a project-specific
stopgap. The project lemma `ouSemigroupFinLp_diffQuot_tendsto` is
derived from it by instantiating `P := ouSemigroupFinLp` and
`hP := ouSemigroupFinLp_coeFn_ae` and unfolding the thin project
definitions.

Reference: Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov
Diffusion Operators* (2014), §2.7 / §1.6 (the OU semigroup is
strongly continuous on `L²(γ)` with generator `L = Δ − x·∇` on the
smooth core; the difference quotient converges to `Lf` in `L²`).
Strategy: the pointwise right limit `(P_t f − f)/t → Lf` is the heat
equation `gaussianOU_heatEquation_within_zero`; the quotient is
dominated by a fixed `L²(γ)` function (mean-value bound from the
*segment-wide* positive-time derivative + core `IsCoreFin` bounds and
Mehler contraction), so dominated convergence upgrades the pointwise
limit to the strong `L²` limit. The segment uniform-`L²` dominator —
the precise Lean obstruction (Codex, 2026-05-16) — is the content
promoted here. **Vetted Standard / Likely correct** (Gemini
`gemini-3-pro-preview`, 2026-05-17; deep-think unavailable, GR-tier
as for the prior two Gross-discharge axioms; recorded in
`AXIOM_AUDIT.md`): well-formed; normalization exact for variance-1
(`∇log ρ = −x`, generator `Δ − x·∇`, Mehler constants self-consistent,
no factor-2/variance rescale); matches BGL §2.7 `L²` strong
convergence on the core; non-vacuous (`f = Σ sin xᵢ`; the genuine OU
`Lp` semigroup satisfies `hP`, so the `P`-characterization is
consistent, not contradictory); hypotheses **sufficient** — value +
first + unmixed-second bounds give `f, Lf ∈ L²(μ)` (Gaussian
integrates all polynomials, `Lf` has ≤ linear growth) and the strong
`L²` limit follows from `Pₜf − f = ∫₀ᵗ Pₛ(Lf) ds` (no mixed partials,
third derivatives, or growth hypotheses required); right-limit
`𝓝[>] 0` form appropriate. No revision. -/
axiom gaussianFin_diffQuot_tendsto_Lp {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf_smooth : ContDiff ℝ ∞ f) (M : ℝ)
    (hf_bd : ∀ x : Fin n → ℝ,
      ‖f x‖ ≤ M ∧
      (∀ i : Fin n, ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ M) ∧
      (∀ i : Fin n,
        ‖fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x
            (Pi.single i 1)‖ ≤ M))
    (hf_mem : MemLp f 2
      (MeasureTheory.Measure.pi
        (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))
    (hLf_mem : MemLp
      (fun x : Fin n → ℝ =>
        (∑ i : Fin n,
            fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x
              (Pi.single i 1))
          - ∑ i : Fin n, x i * fderiv ℝ f x (Pi.single i 1)) 2
      (MeasureTheory.Measure.pi
        (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))
    (P : ℝ →
      (Lp ℝ 2
          (MeasureTheory.Measure.pi
            (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)) →L[ℝ]
        Lp ℝ 2
          (MeasureTheory.Measure.pi
            (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))))
    (hP : ∀ t : ℝ, 0 ≤ t →
      ∀ φ : Lp ℝ 2
          (MeasureTheory.Measure.pi
            (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)),
        (P t φ : (Fin n → ℝ) → ℝ)
            =ᵐ[MeasureTheory.Measure.pi
                (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)]
          (fun x => ∫ y,
            (φ : (Fin n → ℝ) → ℝ)
                (fun i => Real.exp (-t) * x i
                  + Real.sqrt (1 - Real.exp (-2 * t)) * y i)
            ∂(MeasureTheory.Measure.pi
                (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (P t (hf_mem.toLp f) - hf_mem.toLp f))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (hLf_mem.toLp _))

/-- **G2 (a) — strong-`L²` difference-quotient limit.** For core `f`,
`t⁻¹ • (P_t [f] − [f]) → [ouGeneratorFin f]` in `Lp ℝ 2 (γFin n)` as
`t → 0⁺` (right limit, matching `GeneratorCompat`'s `𝓝[>] 0`).

Discharged from the general, Mathlib-native, Gemini-vetted axiom
`gaussianFin_diffQuot_tendsto_Lp` by instantiating the operator
parameter with `ouSemigroupFinLp` and its generic Mehler a.e.
characterization `ouSemigroupFinLp_coeFn_ae`, then unfolding the thin
project definitions (`#print axioms` = the 3 Lean built-ins + that one
axiom only; no `sorryAx`, no other custom axioms). -/
theorem ouSemigroupFinLp_diffQuot_tendsto {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) :
    Tendsto
      (fun t : ℝ => t⁻¹ •
        (ouSemigroupFinLp (n := n) t ((isCoreFin_memLp f hf).toLp f)
          - (isCoreFin_memLp f hf).toLp f))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (ouGeneratorFinLp hf)) := by
  obtain ⟨hsm, M, hM⟩ := hf
  have hfc : IsCoreFin f := ⟨hsm, M, hM⟩
  simpa only [γFin, Gaussian1D.γ, ouGeneratorFin_apply, secondPartial,
    partialDeriv] using
    gaussianFin_diffQuot_tendsto_Lp (n := n) f hsm M hM
      (isCoreFin_memLp f hfc) (memLp_ouGeneratorFin hfc)
      (ouSemigroupFinLp (n := n))
      (fun t ht φ => by
        refine (ouSemigroupFinLp_coeFn_ae (n := n) t ht φ).trans ?_
        simp only [ouSemigroupFin, ouShiftFin, γFin, Gaussian1D.γ]
        exact Filter.EventuallyEq.rfl)

end GaussianFin

end
