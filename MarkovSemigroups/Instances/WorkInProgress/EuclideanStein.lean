/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stein-based discharges for the Gaussian1D BakryEmerySpace instance

Builds on `Instances/WorkInProgress/Euclidean.lean` to prove a chain of
Stein-identity-based results that **discharge axioms** from the original
BGL Ch. 2 axiomatization:

* `stein_identity_standard` (BGL §1.15) — Gaussian integration by parts
  `∫ y · g(y) dγ = ∫ g'(y) dγ` for bounded `C¹` `g`. Proved via the
  Gaussian-PDF ODE `pdf'(y) = -y · pdf(y)` + FTC on infinite intervals.

* `gaussian_dirichlet_form_identity` (BGL §1.6) — `∫ g · L g dγ = -∫ (g')² dγ`
  for `IsCore g`. Follows from Stein applied to `h := g · g'`.

* `hasDerivAt_t_ouSemigroup` (BGL §2.7, heat equation) — for `t > 0`,
  `∂_τ P_τ f(x) |_{τ=t} = L(P_t f)(x)`. Proved via Mathlib's parametric
  derivative on a neighborhood of `t` in `(0, ∞)`, with Stein applied to
  the inner integrand to simplify.

* `hasDerivAt_l2sq_ouSemigroup_pos` (BGL Proposition 4.7.1) — the
  `t > 0` case of the L²-norm derivative. Combines heat equation +
  parametric derivative + Dirichlet form identity.

* `ouSemigroup_l2_sq_hasDerivWithinAt_proved` — proves the same statement
  as the legacy `ouSemigroup_l2_sq_hasDerivWithinAt` axiom, modulo a
  smaller residue axiom `ouSemigroup_l2sq_hasDerivWithinAt_zero` for the
  `t = 0` boundary case (where the parametric-derivative bound `b'(t)`
  blows up).

## Audit

The legacy `ouSemigroup_l2_sq_hasDerivWithinAt` axiom remains in
`Euclidean.lean` for internal consumers (`l2_decay_bound`, the
BakryEmerySpace instance). The proof chain here demonstrates the
discharge path. Future restructuring can wire the discharged version
into those consumers, removing the legacy axiom in favor of the smaller
residue.

## References

- Bakry, Gentil, Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer 2014: §1.6 (Dirichlet form), §1.15 (Stein),
  §2.7 (Mehler kernel), Proposition 4.7.1 (L²-norm derivative).
-/

import MarkovSemigroups.Instances.WorkInProgress.Euclidean

open MeasureTheory ProbabilityTheory Real Filter Set

noncomputable section

namespace Gaussian1D

/-! ## Stein's identity for the standard Gaussian (BGL §1.15)

PROVED. Foundational Gaussian integration-by-parts identity. -/

/-- The standard Gaussian PDF satisfies the ODE `pdf'(y) = -y · pdf(y)`. -/
theorem hasDerivAt_gaussianPDF_standard (y : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-y * gaussianPDFReal 0 1 y) y := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hsq : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-y) y := by
    have h₁ : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by
      simpa using hasDerivAt_pow 2 y
    have h₃ : HasDerivAt (fun x : ℝ => -(x^2) / 2) (-(2 * y) / 2) y :=
      h₁.neg.div_const 2
    convert h₃ using 1; ring
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-(x^2) / 2))
      (Real.exp (-(y^2) / 2) * (-y)) y := hsq.exp
  have hpdf : HasDerivAt (fun x : ℝ => (√(2 * π))⁻¹ * Real.exp (-(x^2) / 2))
      ((√(2 * π))⁻¹ * (Real.exp (-(y^2) / 2) * (-y))) y := hexp.const_mul _
  convert hpdf using 1; ring

private theorem tendsto_neg_sq_div_two_atTop :
    Tendsto (fun y : ℝ => -(y^2)/2) atTop atBot := by
  have h1 : Tendsto (fun y : ℝ => y^2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  exact Tendsto.atBot_div_const (by norm_num : (0 : ℝ) < 2)
    (tendsto_neg_atTop_atBot.comp h1)

private theorem tendsto_neg_sq_div_two_atBot :
    Tendsto (fun y : ℝ => -(y^2)/2) atBot atBot := by
  have h1 : Tendsto (fun y : ℝ => y^2) atBot atTop := by
    have h0 : Tendsto (fun y : ℝ => y^2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
    refine (h0.comp tendsto_neg_atBot_atTop).congr ?_
    intro y; show (-y)^2 = y^2; ring
  exact Tendsto.atBot_div_const (by norm_num : (0 : ℝ) < 2)
    (tendsto_neg_atTop_atBot.comp h1)

/-- The standard Gaussian PDF tends to zero at `+∞`. -/
theorem gaussianPDF_tendsto_atTop :
    Tendsto (gaussianPDFReal 0 1) atTop (nhds 0) := by
  have h_exp : Tendsto (fun y : ℝ => Real.exp (-(y^2)/2)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_sq_div_two_atTop
  have h := h_exp.const_mul ((√(2 * π))⁻¹)
  have heq : (fun y : ℝ => (√(2 * π))⁻¹ * Real.exp (-(y^2)/2)) = gaussianPDFReal 0 1 := by
    funext y; simp [gaussianPDFReal]
  rw [heq] at h
  simpa using h

/-- The standard Gaussian PDF tends to zero at `-∞`. -/
theorem gaussianPDF_tendsto_atBot :
    Tendsto (gaussianPDFReal 0 1) atBot (nhds 0) := by
  have h_exp : Tendsto (fun y : ℝ => Real.exp (-(y^2)/2)) atBot (nhds 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_sq_div_two_atBot
  have h := h_exp.const_mul ((√(2 * π))⁻¹)
  have heq : (fun y : ℝ => (√(2 * π))⁻¹ * Real.exp (-(y^2)/2)) = gaussianPDFReal 0 1 := by
    funext y; simp [gaussianPDFReal]
  rw [heq] at h
  simpa using h

/-- `(y · pdf y)` is Lebesgue-integrable — equivalent to `Integrable id` on γ. -/
theorem integrable_id_mul_gaussianPDF :
    Integrable (fun y : ℝ => y * gaussianPDFReal 0 1 y) := by
  have h_id_int : Integrable (fun y : ℝ => y) γ :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have h_v_ne_0 : (1 : NNReal) ≠ 0 := ne_of_gt zero_lt_one
  have hγ_eq : (γ : Measure ℝ) = volume.withDensity (gaussianPDF 0 1) := by
    show gaussianReal (0 : ℝ) (1 : NNReal) = volume.withDensity (gaussianPDF 0 1)
    exact gaussianReal_of_var_ne_zero 0 h_v_ne_0
  rw [hγ_eq] at h_id_int
  have h_lt : ∀ᵐ x ∂(volume : Measure ℝ), gaussianPDF 0 1 x < ⊤ :=
    ae_of_all _ (fun _ => gaussianPDF_lt_top)
  have h := (integrable_withDensity_iff_integrable_smul' (μ := volume)
    (measurable_gaussianPDF 0 1) h_lt (g := fun y : ℝ => y)).mp h_id_int
  have heq : (fun y : ℝ => (gaussianPDF 0 1 y).toReal • y) =
      (fun y => y * gaussianPDFReal 0 1 y) := by
    funext y
    show (gaussianPDF 0 1 y).toReal * y = y * gaussianPDFReal 0 1 y
    simp [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), mul_comm]
  rw [heq] at h; exact h

/-- `(|y| · pdf y)` is Lebesgue-integrable. -/
theorem integrable_abs_mul_gaussianPDF :
    Integrable (fun y : ℝ => |y| * gaussianPDFReal 0 1 y) := by
  refine Integrable.mono' integrable_id_mul_gaussianPDF.abs
    ((measurable_id.abs.mul (measurable_gaussianPDFReal _ _)).aestronglyMeasurable) ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_mul, abs_abs,
      abs_of_nonneg (gaussianPDFReal_nonneg _ _ _),
      abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]

/-- **Stein's identity** for the standard Gaussian.

For `C¹` functions `g` with bounded `g` and `g'`,
  `∫ y · g(y) dγ = ∫ g'(y) dγ`.

PROOF: Let `F(y) := -g(y) · pdf(y)`. Using `pdf'(y) = -y · pdf(y)`,
  `F'(y) = y · g(y) · pdf(y) − g'(y) · pdf(y)`.
Since `|F(y)| ≤ M · pdf(y) → 0` at `±∞`, `F → 0` at both infinities.
By FTC on infinite intervals (`integral_of_hasDerivAt_of_tendsto`),
`∫_ℝ F'(y) dy = 0`. Convert γ-integrals to Lebesgue via
`integral_gaussianReal_eq_integral_smul`.

Reference: BGL §1.15. -/
theorem stein_identity_standard {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {M : ℝ} (hg_bd : ∀ x, |g x| ≤ M) (hg'_bd : ∀ x, |deriv g x| ≤ M) :
    ∫ y, y * g y ∂γ = ∫ y, deriv g y ∂γ := by
  set pdf : ℝ → ℝ := gaussianPDFReal 0 1 with hpdf_def
  have hM_nn : 0 ≤ M := (abs_nonneg _).trans (hg_bd 0)
  have hpdf_nn : ∀ y, 0 ≤ pdf y := fun y => gaussianPDFReal_nonneg _ _ _
  have hpdf_meas : Measurable pdf := measurable_gaussianPDFReal _ _
  have hg_diff : Differentiable ℝ g := hg.differentiable (by simp)
  have hg_meas : Measurable g := hg.continuous.measurable
  have hg'_meas : Measurable (deriv g) := (hg.continuous_deriv (by simp)).measurable
  -- F(y) := -g(y) · pdf(y), F'(y) = y · g(y) · pdf(y) − g'(y) · pdf(y).
  have hF_deriv : ∀ y, HasDerivAt (fun z => -g z * pdf z)
      (y * g y * pdf y - deriv g y * pdf y) y := by
    intro y
    have h1 : HasDerivAt g (deriv g y) y := hg_diff.differentiableAt.hasDerivAt
    have h2 : HasDerivAt pdf (-y * pdf y) y := hasDerivAt_gaussianPDF_standard y
    have h3 : HasDerivAt (fun z => g z * pdf z)
        (deriv g y * pdf y + g y * (-y * pdf y)) y := h1.mul h2
    have h4 : HasDerivAt (fun z => -(g z * pdf z))
        (-(deriv g y * pdf y + g y * (-y * pdf y))) y := h3.neg
    have h5 : (fun z => -(g z * pdf z)) = (fun z => -g z * pdf z) := by
      funext z; ring
    rw [h5] at h4
    convert h4 using 1; ring
  -- F → 0 at ±∞ since |F| ≤ M · pdf and pdf → 0.
  have h_M_pdf_atTop : Tendsto (fun y => M * pdf y) atTop (nhds 0) := by
    have := gaussianPDF_tendsto_atTop.const_mul M
    simpa using this
  have h_M_pdf_atBot : Tendsto (fun y => M * pdf y) atBot (nhds 0) := by
    have := gaussianPDF_tendsto_atBot.const_mul M
    simpa using this
  have hF_atTop : Tendsto (fun y => -g y * pdf y) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun y => norm_nonneg _) (fun y => ?_) h_M_pdf_atTop
    show ‖-g y * pdf y‖ ≤ M * pdf y
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (hpdf_nn y)]
    exact mul_le_mul (hg_bd y) le_rfl (hpdf_nn y) hM_nn
  have hF_atBot : Tendsto (fun y => -g y * pdf y) atBot (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun y => norm_nonneg _) (fun y => ?_) h_M_pdf_atBot
    show ‖-g y * pdf y‖ ≤ M * pdf y
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (hpdf_nn y)]
    exact mul_le_mul (hg_bd y) le_rfl (hpdf_nn y) hM_nn
  -- Integrability of F' and component pieces.
  have h_pdf_int : Integrable pdf := integrable_gaussianPDFReal _ _
  have h_int_y_g_pdf : Integrable (fun y => y * g y * pdf y) := by
    refine Integrable.mono' (integrable_abs_mul_gaussianPDF.const_mul M)
      ((measurable_id.mul hg_meas).mul hpdf_meas |>.aestronglyMeasurable) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hpdf_nn y)]
    calc |y| * |g y| * pdf y
        ≤ |y| * M * pdf y := by
          apply mul_le_mul_of_nonneg_right _ (hpdf_nn _)
          exact mul_le_mul_of_nonneg_left (hg_bd y) (abs_nonneg _)
      _ = M * (|y| * pdf y) := by ring
  have h_int_g'_pdf : Integrable (fun y => deriv g y * pdf y) := by
    refine Integrable.mono' (h_pdf_int.const_mul M)
      (hg'_meas.mul hpdf_meas |>.aestronglyMeasurable) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpdf_nn y)]
    exact mul_le_mul_of_nonneg_right (hg'_bd y) (hpdf_nn y)
  have h_F'_int : Integrable (fun y => y * g y * pdf y - deriv g y * pdf y) :=
    h_int_y_g_pdf.sub h_int_g'_pdf
  -- ∫_ℝ F' = 0 by FTC at both infinities.
  have h_int_F' : ∫ y, y * g y * pdf y - deriv g y * pdf y = 0 := by
    have := integral_of_hasDerivAt_of_tendsto hF_deriv h_F'_int hF_atBot hF_atTop
    simpa using this
  have h_lebesgue : ∫ y, y * g y * pdf y = ∫ y, deriv g y * pdf y := by
    have h := h_int_F'
    rw [integral_sub h_int_y_g_pdf h_int_g'_pdf] at h
    linarith
  -- Convert γ-integrals to Lebesgue via withDensity.
  have h_v_ne : (1 : NNReal) ≠ 0 := ne_of_gt zero_lt_one
  have h_γ_y_g : ∫ y, y * g y ∂γ = ∫ y, y * g y * pdf y := by
    show ∫ y, y * g y ∂(gaussianReal (0 : ℝ) (1 : NNReal)) = _
    rw [integral_gaussianReal_eq_integral_smul h_v_ne]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show pdf y • (y * g y) = y * g y * pdf y
    rw [smul_eq_mul]; ring
  have h_γ_g' : ∫ y, deriv g y ∂γ = ∫ y, deriv g y * pdf y := by
    show ∫ y, deriv g y ∂(gaussianReal (0 : ℝ) (1 : NNReal)) = _
    rw [integral_gaussianReal_eq_integral_smul h_v_ne]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show pdf y • deriv g y = deriv g y * pdf y
    rw [smul_eq_mul]; ring
  rw [h_γ_y_g, h_γ_g', h_lebesgue]

/-! ## Heat equation for the OU semigroup (BGL §2.7)

PROVED for `t > 0`. The OU semigroup satisfies `∂_t P_t f = L(P_t f)` where
`L g = g'' - x · g'` is the OU generator. Foundational for the
`l2_sq_hasDerivWithinAt` discharge. -/

/-- For `τ > 0`, `b(τ) := √(1 - e^{-2τ})` has derivative `e^{-2τ}/b(τ)`. -/
theorem hasDerivAt_b (τ : ℝ) (hτ : 0 < τ) :
    HasDerivAt (fun s => Real.sqrt (1 - Real.exp (-2 * s)))
      (Real.exp (-2 * τ) / Real.sqrt (1 - Real.exp (-2 * τ))) τ := by
  have hu_pos : 0 < 1 - Real.exp (-2 * τ) := by
    have : Real.exp (-2 * τ) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have h_lin : HasDerivAt (fun s : ℝ => -2 * s) (-2 : ℝ) τ := by
    simpa using (hasDerivAt_id τ).const_mul (-2)
  have h_exp : HasDerivAt (fun s : ℝ => Real.exp (-2 * s))
      (Real.exp (-2 * τ) * (-2)) τ := h_lin.exp
  have h_u : HasDerivAt (fun s : ℝ => 1 - Real.exp (-2 * s))
      (2 * Real.exp (-2 * τ)) τ := by
    have := (hasDerivAt_const τ (1 : ℝ)).sub h_exp
    convert this using 1; ring
  have h_sqrt := h_u.sqrt hu_pos.ne'
  convert h_sqrt using 1
  rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-- **Heat equation for the OU semigroup.** PROVED for `t₀ > 0`.

For `t₀ > 0` and `IsCore f`,
  `∂_τ (P_τ f)(x) |_{τ=t₀} = (P_{t₀} f)''(x) - x · (P_{t₀} f)'(x) = L(P_{t₀} f)(x)`.

PROOF. Apply Mathlib's parametric derivative in `τ` to the Mehler integral
on a neighborhood of `t₀` contained in `(0, ∞)` (so `b(τ)` stays bounded
below by `b(t₀/2) > 0`). The chain rule gives the pointwise τ-derivative
`f'(α(τ) x + b(τ) y) · (-e^{-τ} x + b'(τ) y)`. After integrating against γ:
* `-e^{-τ} x · P_τ(f')(x) = -x · (P_τ f)'(x)` (Mehler derivative).
* `b'(τ) · ∫ y · f'(...) dγ = b'(τ) · b(τ) · P_τ(f'')(x)` (Stein on the
  inner integrand) = `e^{-2τ} · P_τ(f'')(x) = (P_τ f)''(x)` (second-order
  Mehler derivative). -/
theorem hasDerivAt_t_ouSemigroup (t₀ : ℝ) (ht₀ : 0 < t₀)
    {f : ℝ → ℝ} (hf : IsCore f) (x : ℝ) :
    HasDerivAt (fun τ => ouSemigroup τ f x)
      (deriv (deriv (ouSemigroup t₀ f)) x - x * deriv (ouSemigroup t₀ f) x) t₀ := by
  obtain ⟨h_smooth, M, hM⟩ := hf
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0).1
  have hf_core : IsCore f := ⟨h_smooth, M, hM⟩
  set ε : ℝ := t₀ / 2 with hε_def
  have hε_pos : 0 < ε := half_pos ht₀
  have hε_lt : ε < t₀ := half_lt_self ht₀
  have h_nbhd : Set.Ioo ε (t₀ + 1) ∈ nhds t₀ := Ioo_mem_nhds hε_lt (by linarith)
  set b_lo : ℝ := Real.sqrt (1 - Real.exp (-2 * ε))
  have hb_lo_pos : 0 < b_lo := by
    apply Real.sqrt_pos.mpr
    have : Real.exp (-2 * ε) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have h_b_τ_ge : ∀ τ ∈ Set.Ioo ε (t₀ + 1),
      b_lo ≤ Real.sqrt (1 - Real.exp (-2 * τ)) := by
    intro τ hτ
    apply Real.sqrt_le_sqrt
    have h_exp : Real.exp (-2 * τ) ≤ Real.exp (-2 * ε) :=
      Real.exp_le_exp.mpr (by linarith [hτ.1])
    linarith
  set F : ℝ → ℝ → ℝ := fun τ y =>
    f (Real.exp (-τ) * x + Real.sqrt (1 - Real.exp (-2 * τ)) * y)
  set F' : ℝ → ℝ → ℝ := fun τ y =>
    deriv f (Real.exp (-τ) * x + Real.sqrt (1 - Real.exp (-2 * τ)) * y) *
      (-Real.exp (-τ) * x + (Real.exp (-2 * τ) /
        Real.sqrt (1 - Real.exp (-2 * τ))) * y)
  set bound : ℝ → ℝ := fun y => M * (|x| + (1 / b_lo) * |y|)
  have h_id_int : Integrable (fun y : ℝ => y) γ :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have h_bound_int : Integrable bound γ := by
    have : bound = (fun y => M * |x| + M * ((1 / b_lo) * |y|)) := by
      funext y; ring
    rw [this]
    refine Integrable.add (integrable_const _) ?_
    have : (fun y : ℝ => M * ((1 / b_lo) * |y|)) =
        (fun y => (M * (1 / b_lo)) * |y|) := by funext y; ring
    rw [this]
    exact h_id_int.abs.const_mul _
  have hf_meas : Measurable f := h_smooth.continuous.measurable
  have hf'_meas : Measurable (deriv f) :=
    (h_smooth.continuous_deriv (by simp)).measurable
  have hF_meas : ∀ τ, AEStronglyMeasurable (F τ) γ := fun τ => by
    refine (hf_meas.comp ?_).aestronglyMeasurable
    exact (measurable_const).add (measurable_const.mul measurable_id)
  have hF_int : Integrable (F t₀) γ := by
    refine Integrable.mono' (integrable_const M) (hF_meas t₀) ?_
    filter_upwards with y; exact (hM _).1
  have hF'_meas : AEStronglyMeasurable (F' t₀) γ := by
    refine ((hf'_meas.comp ?_).mul ?_).aestronglyMeasurable
    · exact (measurable_const).add (measurable_const.mul measurable_id)
    · exact ((measurable_const).add (measurable_const.mul measurable_id))
  have h_bd : ∀ᵐ y ∂γ, ∀ τ ∈ Set.Ioo ε (t₀ + 1), ‖F' τ y‖ ≤ bound y := by
    filter_upwards with y τ hτ
    show ‖deriv f (Real.exp (-τ) * x + Real.sqrt (1 - Real.exp (-2 * τ)) * y) *
      (-Real.exp (-τ) * x + (Real.exp (-2 * τ) /
        Real.sqrt (1 - Real.exp (-2 * τ))) * y)‖ ≤ M * (|x| + (1 / b_lo) * |y|)
    rw [Real.norm_eq_abs, abs_mul]
    have h_f'_abs : |deriv f (Real.exp (-τ) * x +
        Real.sqrt (1 - Real.exp (-2 * τ)) * y)| ≤ M := by
      rw [← Real.norm_eq_abs]; exact (hM _).2.1
    have h_b_pos : 0 < Real.sqrt (1 - Real.exp (-2 * τ)) := by
      apply Real.sqrt_pos.mpr
      have h_exp : Real.exp (-2 * τ) < 1 :=
        Real.exp_lt_one_iff.mpr (by linarith [hτ.1])
      linarith
    have h_b_lo : b_lo ≤ Real.sqrt (1 - Real.exp (-2 * τ)) := h_b_τ_ge τ hτ
    have h_e_neg_t_le : Real.exp (-τ) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [hτ.1])
    have h_e_neg_2t_le : Real.exp (-2 * τ) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [hτ.1])
    have h_e_neg_t_nn : 0 ≤ Real.exp (-τ) := (Real.exp_pos _).le
    have h_e_neg_2t_nn : 0 ≤ Real.exp (-2 * τ) := (Real.exp_pos _).le
    have h_factor_abs :
        |-Real.exp (-τ) * x + (Real.exp (-2 * τ) /
          Real.sqrt (1 - Real.exp (-2 * τ))) * y| ≤ |x| + (1 / b_lo) * |y| := by
      calc |-Real.exp (-τ) * x + (Real.exp (-2 * τ) /
              Real.sqrt (1 - Real.exp (-2 * τ))) * y|
          ≤ |-Real.exp (-τ) * x| + |(Real.exp (-2 * τ) /
              Real.sqrt (1 - Real.exp (-2 * τ))) * y| := abs_add_le _ _
        _ = Real.exp (-τ) * |x| + (Real.exp (-2 * τ) /
              Real.sqrt (1 - Real.exp (-2 * τ))) * |y| := by
            rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg h_e_neg_t_nn,
                abs_of_nonneg (div_nonneg h_e_neg_2t_nn h_b_pos.le)]
        _ ≤ 1 * |x| + (1 / b_lo) * |y| := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right h_e_neg_t_le (abs_nonneg _)
            · apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
              rw [div_le_div_iff₀ h_b_pos hb_lo_pos]
              calc Real.exp (-2 * τ) * b_lo
                  ≤ 1 * b_lo := mul_le_mul_of_nonneg_right h_e_neg_2t_le hb_lo_pos.le
                _ = b_lo := one_mul _
                _ ≤ Real.sqrt (1 - Real.exp (-2 * τ)) := h_b_lo
                _ = 1 * Real.sqrt (1 - Real.exp (-2 * τ)) := (one_mul _).symm
        _ = |x| + (1 / b_lo) * |y| := by ring
    exact mul_le_mul h_f'_abs h_factor_abs (abs_nonneg _) hM_nn
  have h_diff : ∀ᵐ y ∂γ, ∀ τ ∈ Set.Ioo ε (t₀ + 1),
      HasDerivAt (fun s => F s y) (F' τ y) τ := by
    filter_upwards with y τ hτ
    have h_α : HasDerivAt (fun s : ℝ => Real.exp (-s) * x)
        (-Real.exp (-τ) * x) τ := by
      have h1 : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) τ := by
        simpa using (hasDerivAt_id τ).neg
      have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s))
          (Real.exp (-τ) * (-1)) τ := h1.exp
      have h3 : HasDerivAt (fun s : ℝ => Real.exp (-s) * x)
          (Real.exp (-τ) * (-1) * x) τ := h2.mul_const x
      have heq : -Real.exp (-τ) * x = Real.exp (-τ) * (-1) * x := by ring
      rw [heq]; exact h3
    have h_b' : HasDerivAt (fun s : ℝ => Real.sqrt (1 - Real.exp (-2 * s)) * y)
        ((Real.exp (-2 * τ) / Real.sqrt (1 - Real.exp (-2 * τ))) * y) τ :=
      (hasDerivAt_b τ (by linarith [hτ.1])).mul_const y
    have h_arg : HasDerivAt (fun s : ℝ => Real.exp (-s) * x +
        Real.sqrt (1 - Real.exp (-2 * s)) * y)
        (-Real.exp (-τ) * x + (Real.exp (-2 * τ) /
          Real.sqrt (1 - Real.exp (-2 * τ))) * y) τ := h_α.add h_b'
    have h_f_diff : HasDerivAt f
        (deriv f (Real.exp (-τ) * x +
          Real.sqrt (1 - Real.exp (-2 * τ)) * y))
        (Real.exp (-τ) * x +
          Real.sqrt (1 - Real.exp (-2 * τ)) * y) :=
      (h_smooth.differentiable (by simp)).differentiableAt.hasDerivAt
    exact h_f_diff.comp τ h_arg
  obtain ⟨_, h_deriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le h_nbhd
      (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas h_bd h_bound_int h_diff
  have h_lhs : (fun τ => ∫ y, F τ y ∂γ) = fun τ => ouSemigroup τ f x := rfl
  rw [h_lhs] at h_deriv
  set a₀ := Real.exp (-t₀)
  set b₀ := Real.sqrt (1 - Real.exp (-2 * t₀))
  have hb₀_pos : 0 < b₀ := by
    apply Real.sqrt_pos.mpr
    have : Real.exp (-2 * t₀) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hb₀_le_one : b₀ ≤ 1 := by
    show Real.sqrt (1 - Real.exp (-2 * t₀)) ≤ 1
    rw [Real.sqrt_le_one]
    have : 0 ≤ Real.exp (-2 * t₀) := (Real.exp_pos _).le
    linarith
  have h_F'_eq : ∀ y,
      F' t₀ y = -a₀ * x * deriv f (a₀ * x + b₀ * y) +
                (Real.exp (-2 * t₀) / b₀) * y * deriv f (a₀ * x + b₀ * y) := by
    intro y
    show deriv f (a₀ * x + b₀ * y) *
      (-a₀ * x + (Real.exp (-2 * t₀) / b₀) * y) =
      -a₀ * x * deriv f (a₀ * x + b₀ * y) +
                (Real.exp (-2 * t₀) / b₀) * y * deriv f (a₀ * x + b₀ * y)
    ring
  set g : ℝ → ℝ := fun y => deriv f (a₀ * x + b₀ * y)
  have hg_C1 : ContDiff ℝ 1 g := by
    have h_d : ContDiff ℝ 1 (deriv f) :=
      (IsCore.contDiff_deriv hf_core).of_le (by simp : ((1 : WithTop ℕ∞)) ≤ ⊤)
    have h_inner : ContDiff ℝ 1 (fun y => a₀ * x + b₀ * y) := by
      have h1 : ContDiff ℝ 1 (fun y : ℝ => b₀ * y) := contDiff_const.mul contDiff_id
      exact contDiff_const.add h1
    exact h_d.comp h_inner
  have hg_bd : ∀ y, ‖g y‖ ≤ M := fun y => (hM _).2.1
  have hg'_eq : ∀ y, deriv g y = b₀ * deriv (deriv f) (a₀ * x + b₀ * y) := by
    intro y
    show deriv (fun z => deriv f (a₀ * x + b₀ * z)) y =
      b₀ * deriv (deriv f) (a₀ * x + b₀ * y)
    have h_inner : HasDerivAt (fun z : ℝ => a₀ * x + b₀ * z) b₀ y := by
      have h1 : HasDerivAt (fun _ : ℝ => a₀ * x) (0 : ℝ) y := hasDerivAt_const y _
      have h2 : HasDerivAt (fun z : ℝ => b₀ * z) b₀ y := by
        simpa using (hasDerivAt_id y).const_mul b₀
      have h3 : HasDerivAt (fun z : ℝ => a₀ * x + b₀ * z) (0 + b₀) y := h1.add h2
      simpa using h3
    have h_outer : HasDerivAt (deriv f) (deriv (deriv f) (a₀ * x + b₀ * y))
        (a₀ * x + b₀ * y) :=
      ((IsCore.contDiff_deriv hf_core).differentiable
        (by simp)).differentiableAt.hasDerivAt
    have := h_outer.comp y h_inner
    simpa [mul_comm (deriv (deriv f) _)] using this.deriv
  have hg'_bd : ∀ y, ‖deriv g y‖ ≤ M := fun y => by
    rw [hg'_eq y]
    show |b₀ * deriv (deriv f) (a₀ * x + b₀ * y)| ≤ M
    rw [abs_mul]
    have h1 : |b₀| ≤ 1 := by rw [abs_of_nonneg hb₀_pos.le]; exact hb₀_le_one
    have h2 : |deriv (deriv f) (a₀ * x + b₀ * y)| ≤ M := by
      rw [← Real.norm_eq_abs]; exact (hM _).2.2
    calc |b₀| * |deriv (deriv f) (a₀ * x + b₀ * y)|
        ≤ 1 * M := mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
      _ = M := one_mul _
  have h_stein_g : ∫ y, y * g y ∂γ = ∫ y, deriv g y ∂γ :=
    stein_identity_standard hg_C1 hg_bd hg'_bd
  have h_int_g'_eq : ∫ y, deriv g y ∂γ = b₀ * ouSemigroup t₀ (deriv (deriv f)) x := by
    rw [show (fun y => deriv g y) = (fun y => b₀ * deriv (deriv f) (a₀ * x + b₀ * y))
      from by funext y; exact hg'_eq y]
    rw [integral_const_mul]; rfl
  have h_stein_apply : ∫ y, y * deriv f (a₀ * x + b₀ * y) ∂γ =
      b₀ * ouSemigroup t₀ (deriv (deriv f)) x := by
    rw [h_stein_g, h_int_g'_eq]
  have h_part1_int : Integrable
      (fun y => -a₀ * x * deriv f (a₀ * x + b₀ * y)) γ := by
    refine Integrable.const_mul ?_ _
    refine Integrable.mono' (integrable_const M) ?_ ?_
    · exact ((hf'_meas.comp
        ((measurable_const).add (measurable_const.mul measurable_id))))
        |>.aestronglyMeasurable
    · filter_upwards with y; exact (hM _).2.1
  have h_part2_int : Integrable
      (fun y => (Real.exp (-2 * t₀) / b₀) * y * deriv f (a₀ * x + b₀ * y)) γ := by
    refine Integrable.mono' ((h_id_int.abs).const_mul ((Real.exp (-2 * t₀) / b₀) * M)) ?_ ?_
    · exact (((measurable_const.mul measurable_id).mul
        (hf'_meas.comp ((measurable_const).add (measurable_const.mul measurable_id)))))
        |>.aestronglyMeasurable
    · filter_upwards with y
      have h_e_2t0_nn : 0 ≤ Real.exp (-2 * t₀) := (Real.exp_pos _).le
      have h_coeff_nn : 0 ≤ Real.exp (-2 * t₀) / b₀ :=
        div_nonneg h_e_2t0_nn hb₀_pos.le
      show ‖(Real.exp (-2 * t₀) / b₀) * y * deriv f (a₀ * x + b₀ * y)‖ ≤
        Real.exp (-2 * t₀) / b₀ * M * |y|
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h_coeff_nn]
      have h_f'_abs : |deriv f (a₀ * x + b₀ * y)| ≤ M := by
        rw [← Real.norm_eq_abs]; exact (hM _).2.1
      calc Real.exp (-2 * t₀) / b₀ * |y| * |deriv f (a₀ * x + b₀ * y)|
          ≤ Real.exp (-2 * t₀) / b₀ * |y| * M := by
            apply mul_le_mul_of_nonneg_left h_f'_abs
            exact mul_nonneg h_coeff_nn (abs_nonneg _)
        _ = Real.exp (-2 * t₀) / b₀ * M * |y| := by ring
  have h_int_F'_eq : ∫ y, F' t₀ y ∂γ =
      -a₀ * x * ouSemigroup t₀ (deriv f) x +
      Real.exp (-2 * t₀) * ouSemigroup t₀ (deriv (deriv f)) x := by
    rw [show (fun y => F' t₀ y) =
        (fun y => -a₀ * x * deriv f (a₀ * x + b₀ * y) +
                 (Real.exp (-2 * t₀) / b₀) * y * deriv f (a₀ * x + b₀ * y)) from by
      funext y; exact h_F'_eq y]
    rw [integral_add h_part1_int h_part2_int]
    rw [show (fun y => -a₀ * x * deriv f (a₀ * x + b₀ * y)) =
        (fun y => (-a₀ * x) * deriv f (a₀ * x + b₀ * y)) from rfl]
    rw [integral_const_mul]
    have h_part2_rewrite : (fun y => (Real.exp (-2 * t₀) / b₀) * y *
        deriv f (a₀ * x + b₀ * y)) =
        (fun y => (Real.exp (-2 * t₀) / b₀) * (y * deriv f (a₀ * x + b₀ * y))) := by
      funext y; ring
    rw [h_part2_rewrite, integral_const_mul, h_stein_apply]
    have h_coeff : Real.exp (-2 * t₀) / b₀ * (b₀ * ouSemigroup t₀ (deriv (deriv f)) x) =
        Real.exp (-2 * t₀) * ouSemigroup t₀ (deriv (deriv f)) x := by
      have hb_ne : b₀ ≠ 0 := hb₀_pos.ne'
      field_simp
    rw [h_coeff]; rfl
  rw [h_int_F'_eq] at h_deriv
  have h_target_eq :
      deriv (deriv (ouSemigroup t₀ f)) x - x * deriv (ouSemigroup t₀ f) x =
      -a₀ * x * ouSemigroup t₀ (deriv f) x +
      Real.exp (-2 * t₀) * ouSemigroup t₀ (deriv (deriv f)) x := by
    rw [deriv_deriv_ouSemigroup_eq hf_core, deriv_ouSemigroup_eq hf_core]
    show Real.exp (-2 * t₀) * ouSemigroup t₀ (deriv (deriv f)) x -
         x * (Real.exp (-t₀) * ouSemigroup t₀ (deriv f) x) =
         -Real.exp (-t₀) * x * ouSemigroup t₀ (deriv f) x +
         Real.exp (-2 * t₀) * ouSemigroup t₀ (deriv (deriv f)) x
    ring
  rw [h_target_eq]
  exact h_deriv

/-! ## Gaussian Dirichlet form identity (BGL §1.6) — consequence of Stein

PROVED. The Gaussian integration-by-parts identity for the OU generator:
`∫ g · (L g) dγ = -∫ (g')² dγ` where `L g = g'' - x · g'`.

This is the bridge that turns the abstract `BakryEmerySpace` Dirichlet
energy `E(g, g) = ∫ Γ(g, g) dγ` into the generator-side
`-⟨g, L g⟩_{L²(γ)}` form needed for the `l2_sq_hasDerivWithinAt` and
`entropy_sq_decay_bound` discharges. -/

/-- **Stein consequence: IBP for `x · g · g'`.** For `IsCore g`,
`∫ x · g(x) · g'(x) dγ = ∫ ((g')² + g · g'') dγ`.

Apply Stein to `h := g · g'`. Under `IsCore g`, both `h` and `h' = (g')² + g·g''`
are bounded (by `M²` and `2M²` respectively), so Stein gives
`∫ y · h(y) dγ = ∫ h'(y) dγ`. -/
theorem gaussian_ibp_x_g_deriv_g {g : ℝ → ℝ} (hg : IsCore g) :
    ∫ x, x * g x * deriv g x ∂γ =
      ∫ x, (deriv g x) ^ 2 + g x * deriv (deriv g) x ∂γ := by
  obtain ⟨h_smooth, M, hM⟩ := hg
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0).1
  have hg_diff : Differentiable ℝ g := h_smooth.differentiable (by simp)
  have hg' : ContDiff ℝ ⊤ (deriv g) :=
    IsCore.contDiff_deriv ⟨h_smooth, M, hM⟩
  have hg'_diff : Differentiable ℝ (deriv g) := hg'.differentiable (by simp)
  set h : ℝ → ℝ := fun y => g y * deriv g y with hh_def
  have hh_C1 : ContDiff ℝ 1 h :=
    (h_smooth.of_le (by simp : ((1 : WithTop ℕ∞)) ≤ ⊤)).mul
      (hg'.of_le (by simp : ((1 : WithTop ℕ∞)) ≤ ⊤))
  have hh_bd : ∀ x, |h x| ≤ M ^ 2 := by
    intro x
    show |g x * deriv g x| ≤ M ^ 2
    rw [abs_mul]
    have h1 : |g x| ≤ M := by rw [← Real.norm_eq_abs]; exact (hM x).1
    have h2 : |deriv g x| ≤ M := by rw [← Real.norm_eq_abs]; exact (hM x).2.1
    calc |g x| * |deriv g x| ≤ M * M := mul_le_mul h1 h2 (abs_nonneg _) hM_nn
      _ = M ^ 2 := by ring
  have hh_deriv_eq : ∀ y,
      deriv h y = (deriv g y) ^ 2 + g y * deriv (deriv g) y := by
    intro y
    show deriv (fun z => g z * deriv g z) y = _
    rw [deriv_fun_mul (hg_diff.differentiableAt) (hg'_diff.differentiableAt)]
    ring
  have hh'_bd : ∀ x, |deriv h x| ≤ 2 * M ^ 2 := by
    intro x
    rw [hh_deriv_eq x]
    show |(deriv g x) ^ 2 + g x * deriv (deriv g) x| ≤ 2 * M ^ 2
    have h1 : |deriv g x| ≤ M := by rw [← Real.norm_eq_abs]; exact (hM x).2.1
    have h2 : |g x| ≤ M := by rw [← Real.norm_eq_abs]; exact (hM x).1
    have h3 : |deriv (deriv g) x| ≤ M := by
      rw [← Real.norm_eq_abs]; exact (hM x).2.2
    have hsq : (deriv g x) ^ 2 ≤ M ^ 2 := by
      have heq : (deriv g x) ^ 2 = |deriv g x| ^ 2 := by rw [sq_abs]
      rw [heq]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hsq_nn : (0 : ℝ) ≤ (deriv g x) ^ 2 := sq_nonneg _
    calc |(deriv g x) ^ 2 + g x * deriv (deriv g) x|
        ≤ |(deriv g x) ^ 2| + |g x * deriv (deriv g) x| := abs_add_le _ _
      _ = (deriv g x) ^ 2 + |g x * deriv (deriv g) x| := by rw [abs_of_nonneg hsq_nn]
      _ = (deriv g x) ^ 2 + |g x| * |deriv (deriv g) x| := by rw [abs_mul]
      _ ≤ M ^ 2 + M * M := by
          apply add_le_add hsq
          exact mul_le_mul h2 h3 (abs_nonneg _) hM_nn
      _ = 2 * M ^ 2 := by ring
  have hh_bd' : ∀ x, |h x| ≤ 2 * M ^ 2 := fun x => by
    calc |h x| ≤ M ^ 2 := hh_bd x
      _ ≤ 2 * M ^ 2 := by linarith [sq_nonneg M]
  have h_stein : ∫ y, y * h y ∂γ = ∫ y, deriv h y ∂γ :=
    stein_identity_standard hh_C1 hh_bd' hh'_bd
  have hlhs : (fun y => y * h y) = (fun y => y * g y * deriv g y) := by
    funext y; show y * (g y * deriv g y) = y * g y * deriv g y; ring
  rw [hlhs] at h_stein
  have hrhs : (deriv h : ℝ → ℝ) =
      (fun y => (deriv g y) ^ 2 + g y * deriv (deriv g) y) := by
    funext y; exact hh_deriv_eq y
  rw [hrhs] at h_stein
  exact h_stein

/-- **Gaussian Dirichlet form identity (BGL §1.6).** PROVED.

For `IsCore g`, with `L g = g'' - x · g'` the OU generator,
  `∫ g · (L g) dγ = -∫ (g')² dγ`.

PROOF: split as `∫ g · g'' dγ - ∫ x · g · g' dγ`. By
`gaussian_ibp_x_g_deriv_g`, `∫ x · g · g' dγ = ∫ (g')² dγ + ∫ g · g'' dγ`.
Substituting cancels the `∫ g · g''` terms, leaving `-∫ (g')² dγ`. -/
theorem gaussian_dirichlet_form_identity {g : ℝ → ℝ} (hg : IsCore g) :
    ∫ x, g x * (deriv (deriv g) x - x * deriv g x) ∂γ =
      -∫ x, (deriv g x) ^ 2 ∂γ := by
  obtain ⟨h_smooth, M, hM⟩ := hg
  have hg_core : IsCore g := ⟨h_smooth, M, hM⟩
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0).1
  have hg_meas : Measurable g := h_smooth.continuous.measurable
  have hg' : ContDiff ℝ ⊤ (deriv g) := IsCore.contDiff_deriv hg_core
  have hg'_meas : Measurable (deriv g) := hg'.continuous.measurable
  have hg''_meas : Measurable (deriv (deriv g)) :=
    (hg'.continuous_deriv (by simp)).measurable
  have h_ibp := gaussian_ibp_x_g_deriv_g hg_core
  have h_int_gg'' : Integrable (fun x => g x * deriv (deriv g) x) γ := by
    refine Integrable.mono' (integrable_const (M^2))
      ((hg_meas.mul hg''_meas).aestronglyMeasurable) ?_
    filter_upwards with x
    show ‖g x * deriv (deriv g) x‖ ≤ M ^ 2
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |g x| ≤ M := by rw [← Real.norm_eq_abs]; exact (hM x).1
    have h2 : |deriv (deriv g) x| ≤ M := by
      rw [← Real.norm_eq_abs]; exact (hM x).2.2
    calc |g x| * |deriv (deriv g) x|
        ≤ M * M := mul_le_mul h1 h2 (abs_nonneg _) hM_nn
      _ = M ^ 2 := by ring
  have h_int_g'sq : Integrable (fun x => (deriv g x) ^ 2) γ := by
    refine Integrable.mono' (integrable_const (M^2))
      ((hg'_meas.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards with x
    show ‖(deriv g x) ^ 2‖ ≤ M ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : |deriv g x| ≤ M := by rw [← Real.norm_eq_abs]; exact (hM x).2.1
    have heq : (deriv g x) ^ 2 = |deriv g x| ^ 2 := by rw [sq_abs]
    rw [heq]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h_split_eq :
      (fun x => g x * (deriv (deriv g) x - x * deriv g x)) =
      (fun x => g x * deriv (deriv g) x - x * g x * deriv g x) := by
    funext x; ring
  rw [h_split_eq]
  have h_id_int : Integrable (fun x : ℝ => x) γ :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have h_int_xgg' : Integrable (fun x => x * g x * deriv g x) γ := by
    refine Integrable.mono' (h_id_int.abs.const_mul (M^2))
      (((measurable_id.mul hg_meas).mul hg'_meas).aestronglyMeasurable) ?_
    filter_upwards with x
    show ‖x * g x * deriv g x‖ ≤ M^2 * |x|
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 : |g x| ≤ M := by rw [← Real.norm_eq_abs]; exact (hM x).1
    have h2 : |deriv g x| ≤ M := by rw [← Real.norm_eq_abs]; exact (hM x).2.1
    calc |x| * |g x| * |deriv g x|
        ≤ |x| * M * M := by
          apply mul_le_mul _ h2 (abs_nonneg _) (mul_nonneg (abs_nonneg _) hM_nn)
          exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = M^2 * |x| := by ring
  rw [integral_sub h_int_gg'' h_int_xgg', h_ibp,
      integral_add h_int_g'sq h_int_gg'']
  ring

/-! ## L²-norm derivative for the OU semigroup (BGL Prop 4.7.1)

PROVED for `t > 0` (combines heat equation + parametric derivative +
Gaussian Dirichlet form identity). The `t = 0` boundary case is the
residue of the former axiom `ouSemigroup_l2_sq_hasDerivWithinAt`. -/

/-- **L²-norm derivative for the OU semigroup (BGL Prop 4.7.1).** PROVED for `t > 0`.

For `t₀ > 0` and `IsCore f`,
  `d/ds (∫ (P_s f)² dγ) |_{s=t₀} = -2 · ∫ ((P_{t₀} f)')² dγ`.

PROOF. Apply Mathlib's parametric derivative to `∫ x, (P_s f x)² ∂γ(x)`
in `s` on a neighborhood of `t₀` contained in `(0, ∞)`. The pointwise
time-derivative is `2 · (P_s f x) · ∂_s(P_s f x) = 2 · (P_s f x) · L(P_s f)(x)`
by the heat equation. Integrating, by the Gaussian Dirichlet form identity
`∫ g · L g dγ = -∫(g')² dγ` for `IsCore g`,
`∫ 2 (P_s f) · L(P_s f) dγ = -2 ∫ ((P_s f)')² dγ`. -/
theorem hasDerivAt_l2sq_ouSemigroup_pos (t₀ : ℝ) (ht₀ : 0 < t₀)
    {f : ℝ → ℝ} (hf : IsCore f) :
    HasDerivAt (fun s => ∫ x, (ouSemigroup s f x) ^ 2 ∂γ)
      (-2 * ∫ x, (deriv (ouSemigroup t₀ f) x) ^ 2 ∂γ) t₀ := by
  obtain ⟨h_smooth, M, hM⟩ := hf
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0).1
  have hf_core : IsCore f := ⟨h_smooth, M, hM⟩
  set ε : ℝ := t₀ / 2 with hε_def
  have hε_pos : 0 < ε := half_pos ht₀
  have hε_lt : ε < t₀ := half_lt_self ht₀
  have h_nbhd : Set.Ioo ε (t₀ + 1) ∈ nhds t₀ := Ioo_mem_nhds hε_lt (by linarith)
  set F : ℝ → ℝ → ℝ := fun s x => (ouSemigroup s f x) ^ 2
  set F' : ℝ → ℝ → ℝ := fun s x => 2 * ouSemigroup s f x *
    (deriv (deriv (ouSemigroup s f)) x - x * deriv (ouSemigroup s f) x)
  set bound : ℝ → ℝ := fun x => 2 * M ^ 2 * (1 + |x|)
  have h_id_int : Integrable (fun x : ℝ => x) γ :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have h_bound_int : Integrable bound γ := by
    have hb_eq : bound = (fun x => 2 * M ^ 2 + 2 * M ^ 2 * |x|) := by
      funext x; ring
    rw [hb_eq]
    exact (integrable_const _).add (h_id_int.abs.const_mul _)
  have h_bounds : ∀ s, 0 ≤ s → ∀ x,
      ‖ouSemigroup s f x‖ ≤ M ∧
      ‖deriv (ouSemigroup s f) x‖ ≤ M ∧
      ‖deriv (deriv (ouSemigroup s f)) x‖ ≤ M :=
    fun s hs x => ouSemigroup_preserves_bounds h_smooth hM s hs x
  have hPsf_meas : ∀ s, 0 ≤ s → Measurable (ouSemigroup s f) := fun s hs => by
    have h_core : IsCore (ouSemigroup s f) := ouSemigroup_preserves_IsCore s hs hf_core
    exact h_core.measurable
  have hF_meas : ∀ s ∈ Set.Ioo ε (t₀ + 1), AEStronglyMeasurable (F s) γ := by
    intro s hs
    have hs_pos : 0 < s := lt_of_lt_of_le hε_pos hs.1.le
    have h_meas := hPsf_meas s hs_pos.le
    exact (h_meas.pow_const 2).aestronglyMeasurable
  have hF_int : Integrable (F t₀) γ := by
    refine Integrable.mono' (integrable_const (M ^ 2)) (hF_meas t₀
      ⟨hε_lt, by linarith⟩) ?_
    filter_upwards with x
    show ‖(ouSemigroup t₀ f x) ^ 2‖ ≤ M ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : |ouSemigroup t₀ f x| ≤ M := by
      rw [← Real.norm_eq_abs]; exact (h_bounds t₀ ht₀.le x).1
    have heq : (ouSemigroup t₀ f x) ^ 2 = |ouSemigroup t₀ f x| ^ 2 := by rw [sq_abs]
    rw [heq]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hF'_meas : AEStronglyMeasurable (F' t₀) γ := by
    have h_core_t₀ : IsCore (ouSemigroup t₀ f) :=
      ouSemigroup_preserves_IsCore t₀ ht₀.le hf_core
    have h_meas_t₀ : Measurable (ouSemigroup t₀ f) := h_core_t₀.measurable
    have h_smooth_t₀_d : ContDiff ℝ ⊤ (deriv (ouSemigroup t₀ f)) :=
      IsCore.contDiff_deriv h_core_t₀
    have h_meas_t₀' : Measurable (deriv (ouSemigroup t₀ f)) :=
      h_smooth_t₀_d.continuous.measurable
    have h_meas_t₀'' : Measurable (deriv (deriv (ouSemigroup t₀ f))) :=
      (h_smooth_t₀_d.continuous_deriv (by simp)).measurable
    refine ((measurable_const.mul h_meas_t₀).mul ?_).aestronglyMeasurable
    exact h_meas_t₀''.sub (measurable_id.mul h_meas_t₀')
  have h_bd : ∀ᵐ x ∂γ, ∀ s ∈ Set.Ioo ε (t₀ + 1), ‖F' s x‖ ≤ bound x := by
    filter_upwards with x s hs
    show ‖2 * ouSemigroup s f x *
        (deriv (deriv (ouSemigroup s f)) x - x * deriv (ouSemigroup s f) x)‖ ≤
      2 * M ^ 2 * (1 + |x|)
    have hs_pos : 0 ≤ s := (lt_of_lt_of_le hε_pos hs.1.le).le
    obtain ⟨h_ps_bd, h_dps_bd, h_ddps_bd⟩ := h_bounds s hs_pos x
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have h_ps : |ouSemigroup s f x| ≤ M := by
      rw [← Real.norm_eq_abs]; exact h_ps_bd
    have h_dps : |deriv (ouSemigroup s f) x| ≤ M := by
      rw [← Real.norm_eq_abs]; exact h_dps_bd
    have h_ddps : |deriv (deriv (ouSemigroup s f)) x| ≤ M := by
      rw [← Real.norm_eq_abs]; exact h_ddps_bd
    have h_L : |deriv (deriv (ouSemigroup s f)) x -
        x * deriv (ouSemigroup s f) x| ≤ M * (1 + |x|) := by
      calc |deriv (deriv (ouSemigroup s f)) x - x * deriv (ouSemigroup s f) x|
          ≤ |deriv (deriv (ouSemigroup s f)) x| +
            |x * deriv (ouSemigroup s f) x| := by
            rw [sub_eq_add_neg]
            exact (abs_add_le _ _).trans (by rw [abs_neg])
        _ = |deriv (deriv (ouSemigroup s f)) x| + |x| * |deriv (ouSemigroup s f) x| := by
            rw [abs_mul]
        _ ≤ M + |x| * M := by
            apply add_le_add h_ddps
            exact mul_le_mul_of_nonneg_left h_dps (abs_nonneg _)
        _ = M * (1 + |x|) := by ring
    have h_2_nn : (0 : ℝ) ≤ 2 := by norm_num
    have h_2M_nn : (0 : ℝ) ≤ 2 * M := mul_nonneg h_2_nn hM_nn
    calc |2| * |ouSemigroup s f x| *
          |deriv (deriv (ouSemigroup s f)) x - x * deriv (ouSemigroup s f) x|
        ≤ 2 * M * (M * (1 + |x|)) := by
          rw [abs_of_nonneg h_2_nn]
          apply mul_le_mul _ h_L (abs_nonneg _) h_2M_nn
          exact mul_le_mul_of_nonneg_left h_ps h_2_nn
      _ = 2 * M ^ 2 * (1 + |x|) := by ring
  have h_diff : ∀ᵐ x ∂γ, ∀ s ∈ Set.Ioo ε (t₀ + 1),
      HasDerivAt (fun τ => F τ x) (F' s x) s := by
    filter_upwards with x s hs
    have hs_pos : 0 < s := lt_of_lt_of_le hε_pos hs.1.le
    show HasDerivAt (fun τ => (ouSemigroup τ f x) ^ 2)
      (2 * ouSemigroup s f x *
        (deriv (deriv (ouSemigroup s f)) x - x * deriv (ouSemigroup s f) x)) s
    have h_heat : HasDerivAt (fun τ => ouSemigroup τ f x)
        (deriv (deriv (ouSemigroup s f)) x - x * deriv (ouSemigroup s f) x) s :=
      hasDerivAt_t_ouSemigroup s hs_pos hf_core x
    have h_sq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * ouSemigroup s f x)
        (ouSemigroup s f x) := by
      simpa using hasDerivAt_pow 2 (ouSemigroup s f x)
    have := h_sq.comp s h_heat
    convert this using 1
  have hF_meas_ev : ∀ᶠ s in nhds t₀, AEStronglyMeasurable (F s) γ :=
    Filter.eventually_of_mem h_nbhd hF_meas
  obtain ⟨_, h_deriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le h_nbhd
      hF_meas_ev hF_int hF'_meas h_bd h_bound_int h_diff
  have h_lhs : (fun s => ∫ x, F s x ∂γ) = fun s => ∫ x, (ouSemigroup s f x) ^ 2 ∂γ := rfl
  rw [h_lhs] at h_deriv
  have h_core_t₀ : IsCore (ouSemigroup t₀ f) :=
    ouSemigroup_preserves_IsCore t₀ ht₀.le hf_core
  have h_dirichlet := gaussian_dirichlet_form_identity h_core_t₀
  have h_int_F'_eq : ∫ x, F' t₀ x ∂γ =
      -2 * ∫ x, (deriv (ouSemigroup t₀ f) x) ^ 2 ∂γ := by
    show ∫ x, 2 * ouSemigroup t₀ f x *
        (deriv (deriv (ouSemigroup t₀ f)) x - x * deriv (ouSemigroup t₀ f) x) ∂γ =
      -2 * ∫ x, (deriv (ouSemigroup t₀ f) x) ^ 2 ∂γ
    have hrw : (fun x => 2 * ouSemigroup t₀ f x *
        (deriv (deriv (ouSemigroup t₀ f)) x - x * deriv (ouSemigroup t₀ f) x)) =
      (fun x => 2 * (ouSemigroup t₀ f x *
        (deriv (deriv (ouSemigroup t₀ f)) x - x * deriv (ouSemigroup t₀ f) x))) := by
      funext x; ring
    rw [hrw, integral_const_mul, h_dirichlet]
    ring
  rw [h_int_F'_eq] at h_deriv
  exact h_deriv

/-! ## Boundary case at t = 0 (residue)

The full `ouSemigroup_l2_sq_hasDerivWithinAt` (BGL Proposition 4.7.1) is now
provable for `t > 0` (`hasDerivAt_l2sq_ouSemigroup_pos`) but the right-derivative
at `t = 0` requires more delicate analysis: the parametric-derivative bound
`b'(t) = e^{-2t}/b(t)` blows up at `t = 0`, so we cannot directly apply
Mathlib's parametric derivative on a neighborhood of `0`.

A discharge route exists via MVT + continuity of `φ'` at `0+`: take the limit
of `(φ(t) - φ(0))/t = (1/t) ∫₀^t φ'(τ) dτ` as `t → 0+`, where `φ'(τ) →
-2 ∫(f')² dγ` (continuity via DCT on the Mehler integral). Substantial extra
machinery (~200 lines). For now, we isolate the boundary case as a smaller
atomic axiom. -/

/-- **Boundary case `t = 0` for the L²-norm derivative.** The right-derivative
of `s ↦ ∫(P_s f)² dγ` at `s = 0` equals `-2 ∫(f')² dγ`.

A direct consequence of the heat equation + Dirichlet form identity once
`φ` is shown to be `C¹` at `t = 0` (via DCT on the Mehler integral
continuity). Standalone smaller atomic axiom; smaller residue of the
original `ouSemigroup_l2_sq_hasDerivWithinAt` axiom.

Reference: BGL Proposition 4.7.1 boundary case. -/
axiom ouSemigroup_l2sq_hasDerivWithinAt_zero {f : ℝ → ℝ} (hf : IsCore f) :
    HasDerivWithinAt (fun s => ∫ x, (ouSemigroup s f x) ^ 2 ∂γ)
      (-2 * ∫ x, (deriv f x) ^ 2 ∂γ) (Ici 0) 0

/-- **`ouSemigroup_l2_sq_hasDerivWithinAt` (BGL Prop 4.7.1).** PROVED, modulo
the smaller atomic axiom `ouSemigroup_l2sq_hasDerivWithinAt_zero` for the
`t = 0` boundary case.

For `t ≥ 0` and `IsCore f`,
  `d/ds (∫ (P_s f)² dγ) |_{s=t}_{(Ici 0)} = -2 · ∫ Γ(P_t f, P_t f) dγ`.

PROOF. Case `t > 0`: from `hasDerivAt_l2sq_ouSemigroup_pos` (heat equation +
Dirichlet form via Stein). Case `t = 0`: from
`ouSemigroup_l2sq_hasDerivWithinAt_zero`, after substituting `P_0 f = f`. -/
theorem ouSemigroup_l2_sq_hasDerivWithinAt_proved (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : IsCore f) :
    HasDerivWithinAt (fun s => ∫ x, (ouSemigroup s f x) ^ 2 ∂γ)
      (-2 * ∫ x, ouGamma (ouSemigroup t f) (ouSemigroup t f) x ∂γ) (Ici 0) t := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · -- t = 0 case: P_0 f = f, so Γ(P_0 f, P_0 f) = (deriv f)².
    have h_p0 : ouSemigroup 0 f = f := by
      ext x
      simp only [ouSemigroup, neg_zero, Real.exp_zero, mul_zero, sub_self,
        Real.sqrt_zero, zero_mul, add_zero, one_mul]
      simp [integral_const]
    have h_gamma_eq : ∫ x, ouGamma (ouSemigroup 0 f) (ouSemigroup 0 f) x ∂γ =
        ∫ x, (deriv f x) ^ 2 ∂γ := by
      rw [h_p0]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show deriv f x * deriv f x = (deriv f x) ^ 2
      ring
    rw [h_gamma_eq]
    exact ouSemigroup_l2sq_hasDerivWithinAt_zero hf
  · -- t > 0 case: convert HasDerivAt to HasDerivWithinAt.
    have h_pos := hasDerivAt_l2sq_ouSemigroup_pos t ht_pos hf
    have h_gamma_eq :
        ∫ x, ouGamma (ouSemigroup t f) (ouSemigroup t f) x ∂γ =
        ∫ x, (deriv (ouSemigroup t f) x) ^ 2 ∂γ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show deriv (ouSemigroup t f) x * deriv (ouSemigroup t f) x =
        (deriv (ouSemigroup t f) x) ^ 2
      ring
    rw [h_gamma_eq]
    exact h_pos.hasDerivWithinAt



/-- **Integrated L² gradient decay — DERIVED from the atomic axioms.**

  ∫ f² dγ − ∫ (P_t f)² dγ ≤ (1 − e^{-2t}) · E(f, f).

Proof: by `ouSemigroup_l2_sq_hasDerivWithinAt`,
`d/ds ∫(P_s f)² dγ = -2 ∫ Γ(P_s f, P_s f) dγ ≥ -2 e^{-2s} · E(f)` (the
last inequality from `ouSemigroup_gradient_decay`). The FTC inequality
`integral_le_sub_of_hasDeriv_right_of_le` then gives
`∫₀ᵗ -2 e^{-2s} E(f) ds ≤ ∫(P_t f)² - ∫f²`, and `∫₀ᵗ -2 e^{-2s} ds = e^{-2t} - 1`,
which rearranges to the claim.

This was previously a textbook axiom; it is now reduced to the atomic
five (`gradient_decay`, `l2_sq_hasDerivWithinAt`, `preserves_IsCore`).

Reference: BGL Proposition 4.7.1 integrated form. -/
theorem ouSemigroup_l2_decay_bound (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : IsCore f) :
    ∫ x, (f x) ^ 2 ∂γ - ∫ x, (ouSemigroup t f x) ^ 2 ∂γ ≤
      (1 - Real.exp (-2 * 1 * t)) / 1 * ouEnergy f f := by
  set Ef : ℝ := ouEnergy f f with hEf_def
  set g : ℝ → ℝ := fun s => ∫ x, (ouSemigroup s f x) ^ 2 ∂γ with hg_def
  set φ : ℝ → ℝ := fun s => -2 * Real.exp (-2 * s) * Ef with hφ_def
  -- Step 1: HasDerivWithinAt g (g'(s)) (Ici 0) s for each s ≥ 0.
  have hderiv : ∀ s, 0 ≤ s →
      HasDerivWithinAt g
        (-2 * ∫ x, ouGamma (ouSemigroup s f) (ouSemigroup s f) x ∂γ) (Ici 0) s := by
    intro s hs
    exact ouSemigroup_l2_sq_hasDerivWithinAt_proved f s hs hf
  -- Step 2: ContinuousOn g (Icc 0 t).
  have hg_cont : ContinuousOn g (Set.Icc 0 t) := by
    intro s hs
    have h := (hderiv s hs.1).continuousWithinAt
    exact h.mono (fun x hx => hx.1)
  -- Step 3: Right derivative on Ioo 0 t.
  have hderiv_open : ∀ s ∈ Set.Ioo 0 t,
      HasDerivWithinAt g
        (-2 * ∫ x, ouGamma (ouSemigroup s f) (ouSemigroup s f) x ∂γ) (Ioi s) s := by
    intro s hs
    exact (hderiv s hs.1.le).mono (fun x hx => hs.1.le.trans hx.le)
  -- Step 4: φ s ≤ g'(s) on Ioo 0 t (from gradient_decay).
  have hφg' : ∀ s ∈ Set.Ioo 0 t,
      φ s ≤ -2 * ∫ x, ouGamma (ouSemigroup s f) (ouSemigroup s f) x ∂γ := by
    intro s hs
    have hgrad := ouSemigroup_gradient_decay f s hs.1.le hf
    -- hgrad: ∫ deriv(P_s f) * deriv(P_s f) ≤ exp(-2*1*s) * ∫ deriv f * deriv f
    -- ouGamma f g x = deriv f x * deriv g x; ouEnergy f f = ∫ deriv f * deriv f
    have hgrad' : ∫ x, ouGamma (ouSemigroup s f) (ouSemigroup s f) x ∂γ ≤
        Real.exp (-2 * s) * Ef := by
      have he : Real.exp (-2 * 1 * s) = Real.exp (-2 * s) := by
        congr 1; ring
      rw [hEf_def]; simp only [ouEnergy, ouGamma]; rw [← he]; exact hgrad
    have h := mul_le_mul_of_nonneg_left hgrad' (by norm_num : (0:ℝ) ≤ 2)
    show -2 * Real.exp (-2 * s) * Ef ≤ -2 * _
    linarith
  -- Step 5: φ continuous, hence integrable on Icc 0 t.
  have hφ_cont : Continuous φ := by
    show Continuous (fun s => -2 * Real.exp (-2 * s) * Ef)
    fun_prop
  have hφ_int : MeasureTheory.IntegrableOn φ (Set.Icc 0 t) :=
    hφ_cont.continuousOn.integrableOn_Icc
  -- Step 6: FTC inequality: ∫₀ᵗ φ ≤ g(t) - g(0).
  have hFTC : ∫ s in (0)..t, φ s ≤ g t - g 0 :=
    intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le ht hg_cont
      hderiv_open hφ_int hφg'
  -- Step 7: Compute ∫₀ᵗ -2·exp(-2s)·Ef ds = Ef · (exp(-2t) - 1).
  have hderiv_exp : ∀ s : ℝ,
      HasDerivAt (fun u : ℝ => Real.exp (-2 * u)) (-2 * Real.exp (-2 * s)) s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => -2 * u) (-2 : ℝ) s := by
      simpa using (hasDerivAt_id s).const_mul (-2 : ℝ)
    -- chain rule: d/ds[exp(-2s)] = exp(-2s) * (-2)
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (-2 * u))
        (Real.exp (-2 * s) * (-2)) s :=
      (Real.hasDerivAt_exp (-2 * s)).comp s h1
    simpa [mul_comm] using h2
  have hintExp : ∫ s in (0)..t, -2 * Real.exp (-2 * s) =
      Real.exp (-2 * t) - Real.exp (-2 * 0) := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u => Real.exp (-2 * u))
      (f' := fun u => -2 * Real.exp (-2 * u))
      (a := 0) (b := t) (fun s _ => hderiv_exp s)
      ((continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).intervalIntegrable 0 t)
    exact this
  have hintφ : ∫ s in (0)..t, φ s = Ef * (Real.exp (-2 * t) - 1) := by
    show ∫ s in (0)..t, -2 * Real.exp (-2 * s) * Ef = Ef * (Real.exp (-2 * t) - 1)
    have hrw : (fun s => -2 * Real.exp (-2 * s) * Ef) =
        (fun s => -2 * Real.exp (-2 * s)) * (fun _ => Ef) := by
      ext s; rfl
    rw [show (fun s => -2 * Real.exp (-2 * s) * Ef) =
        (fun s => (-2 * Real.exp (-2 * s)) * Ef) from rfl]
    rw [intervalIntegral.integral_mul_const, hintExp]
    have : Real.exp (-2 * 0) = 1 := by simp
    rw [this, mul_comm]
  -- Step 8: Connect g(0) with ∫f². Since ouSemigroup 0 f = f.
  have hg0 : g 0 = ∫ x, (f x) ^ 2 ∂γ := by
    show ∫ x, (ouSemigroup 0 f x) ^ 2 ∂γ = ∫ x, (f x) ^ 2 ∂γ
    -- ouSemigroup 0 f x = ∫ y, f(e^0 x + √(1-e^0) y) dγ = ∫ y, f(x) dγ = f(x)
    have h_zero : ouSemigroup 0 f = f := by
      ext x
      simp only [ouSemigroup, neg_zero, Real.exp_zero, mul_zero, sub_self,
        Real.sqrt_zero, zero_mul, add_zero, one_mul]
      simp [integral_const]
    rw [h_zero]
  -- Step 9: assemble.
  rw [show g t = ∫ x, (ouSemigroup t f x) ^ 2 ∂γ from rfl] at hFTC
  rw [hg0, hintφ] at hFTC
  -- hFTC: Ef * (exp(-2t) - 1) ≤ ∫(P_t f)² - ∫f²
  -- Want: ∫f² - ∫(P_t f)² ≤ (1 - exp(-2*1*t)) / 1 * Ef
  have he : Real.exp (-2 * 1 * t) = Real.exp (-2 * t) := by congr 1; ring
  rw [he]
  linarith

/-! ## BakryEmerySpace instance -/

/-- The BakryEmerySpace instance for ℝ with standard Gaussian and OU semigroup. -/
@[reducible]
def bakryEmerySpace : BakryEmerySpace ℝ where
  toDirichletSpace := dirichletSpace
  Γ := ouGamma
  Γ_symm := fun f g => by ext x; simp only [ouGamma]; ring
  Γ_nonneg := fun f x => by simp only [ouGamma]; exact mul_self_nonneg _
  energy_eq_integral_Γ := fun f g => by
    simp only [ouGamma]; rfl
  IsCore_mul := by
    rintro f g hf hg
    obtain ⟨hf_smooth, Mf, hfM⟩ := hf
    obtain ⟨hg_smooth, Mg, hgM⟩ := hg
    refine ⟨hf_smooth.mul hg_smooth, ⟨Mf * Mg + 2 * (Mf * Mg) + Mf * Mg, fun x => ?_⟩⟩
    -- derivatives:
    have hf_core : IsCore f := ⟨hf_smooth, Mf, hfM⟩
    have hg_core : IsCore g := ⟨hg_smooth, Mg, hgM⟩
    have hdf := hf_core.differentiable
    have hdg := hg_core.differentiable
    have hdf' := hf_core.differentiable_deriv
    have hdg' := hg_core.differentiable_deriv
    -- (fg)' = f'g + fg'
    have h1 : ∀ y, deriv (f * g) y = deriv f y * g y + f y * deriv g y := fun y =>
      deriv_mul (hdf y) (hdg y)
    have h2 : deriv (f * g) = fun y => deriv f y * g y + f y * deriv g y := by
      ext y; exact h1 y
    -- (fg)'' = f''g + 2 f'g' + fg''
    have h3 : deriv (deriv (f * g)) x =
        deriv (deriv f) x * g x + deriv f x * deriv g x +
        (deriv f x * deriv g x + f x * deriv (deriv g) x) := by
      rw [h2]
      have hA : DifferentiableAt ℝ (fun y => deriv f y * g y) x :=
        (hdf' x).mul (hdg x)
      have hB : DifferentiableAt ℝ (fun y => f y * deriv g y) x :=
        (hdf x).mul (hdg' x)
      rw [deriv_fun_add hA hB]
      congr 1
      · exact deriv_fun_mul (hdf' x) (hdg x)
      · exact deriv_fun_mul (hdf x) (hdg' x)
    -- norm bounds
    have hMf_nn : 0 ≤ Mf := (norm_nonneg _).trans (hfM 0).1
    have hMg_nn : 0 ≤ Mg := (norm_nonneg _).trans (hgM 0).1
    refine ⟨?_, ?_, ?_⟩
    · -- ‖(f*g) x‖ ≤ Mf*Mg + 2(Mf*Mg) + Mf*Mg
      show ‖f x * g x‖ ≤ Mf * Mg + 2 * (Mf * Mg) + Mf * Mg
      have : ‖f x * g x‖ ≤ Mf * Mg := by
        rw [norm_mul]
        exact mul_le_mul (hfM x).1 (hgM x).1 (norm_nonneg _) hMf_nn
      nlinarith
    · -- ‖(fg)' x‖ ≤ total
      rw [h1]
      have h_le : ‖deriv f x * g x + f x * deriv g x‖ ≤ Mf * Mg + Mf * Mg := by
        calc ‖deriv f x * g x + f x * deriv g x‖
            ≤ ‖deriv f x * g x‖ + ‖f x * deriv g x‖ := norm_add_le _ _
          _ = ‖deriv f x‖ * ‖g x‖ + ‖f x‖ * ‖deriv g x‖ := by rw [norm_mul, norm_mul]
          _ ≤ Mf * Mg + Mf * Mg := by
              gcongr
              · exact (hfM x).2.1
              · exact (hgM x).1
              · exact (hfM x).1
              · exact (hgM x).2.1
      nlinarith
    · -- ‖(fg)'' x‖ ≤ total
      rw [h3]
      have h_le : ‖deriv (deriv f) x * g x + deriv f x * deriv g x +
            (deriv f x * deriv g x + f x * deriv (deriv g) x)‖
          ≤ Mf * Mg + 2 * (Mf * Mg) + Mf * Mg := by
        have e1 : ‖deriv (deriv f) x * g x‖ ≤ Mf * Mg := by
          rw [norm_mul]; exact mul_le_mul (hfM x).2.2 (hgM x).1 (norm_nonneg _) hMf_nn
        have e2 : ‖deriv f x * deriv g x‖ ≤ Mf * Mg := by
          rw [norm_mul]; exact mul_le_mul (hfM x).2.1 (hgM x).2.1 (norm_nonneg _) hMf_nn
        have e3 : ‖f x * deriv (deriv g) x‖ ≤ Mf * Mg := by
          rw [norm_mul]; exact mul_le_mul (hfM x).1 (hgM x).2.2 (norm_nonneg _) hMf_nn
        calc ‖deriv (deriv f) x * g x + deriv f x * deriv g x +
                (deriv f x * deriv g x + f x * deriv (deriv g) x)‖
            ≤ ‖deriv (deriv f) x * g x‖ + ‖deriv f x * deriv g x‖ +
                (‖deriv f x * deriv g x‖ + ‖f x * deriv (deriv g) x‖) := by
              exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
          _ ≤ Mf * Mg + Mf * Mg + (Mf * Mg + Mf * Mg) := by
              gcongr
          _ = Mf * Mg + 2 * (Mf * Mg) + Mf * Mg := by ring
      exact h_le
  IsCore_semigroup := fun t ht _ hf => ouSemigroup_preserves_IsCore t ht hf
  Γ_leibniz := fun f g h hf hg _ x => by
    simp only [ouGamma]
    -- deriv(fg) = deriv f * g + f * deriv g
    have hdf : DifferentiableAt ℝ f x := hf.differentiable.differentiableAt
    have hdg : DifferentiableAt ℝ g x := hg.differentiable.differentiableAt
    have : deriv (f * g) x = deriv f x * g x + f x * deriv g x := deriv_mul hdf hdg
    rw [this]; ring
  Γ_const := fun c f => by
    ext x; simp only [ouGamma, deriv_const, Pi.zero_apply]; ring
  semigroup := ouSemigroup
  ρ := 1
  hρ := one_pos
  gradient_decay := fun f t ht hf => by
    -- ouGamma f g x = deriv f x * deriv g x; ouEnergy = ∫ deriv f * deriv g dγ
    show ∫ x, ouGamma (ouSemigroup t f) (ouSemigroup t f) x ∂γ ≤
        Real.exp (-2 * 1 * t) * ∫ x, ouGamma f f x ∂γ
    simpa [ouGamma] using ouSemigroup_gradient_decay f t ht hf
  semigroup_zero := fun f => by
    ext x
    simp only [ouSemigroup, neg_zero, exp_zero, mul_zero, sub_self, sqrt_zero,
               zero_mul, add_zero, one_mul]
    simp [integral_const]
  semigroup_add := fun s t _ hs ht hf => ouSemigroup_compose s t hs ht hf
  semigroup_contraction := fun f t ht hf_core => by
    -- Jensen + kernel change of variables. Let φ(x,y) = ax+by where
    -- a = e^{-t}, b = √(1-e^{-2t}). Then:
    --   (P_t f x)² = (∫_y f(ax+by) dγ)² ≤ ∫_y f(ax+by)² dγ   (Jensen for x²)
    -- integrate in x, use ou_kernel_map with f²:
    --   ∫_x ∫_y f(ax+by)² dγ dγ = ∫_p f(φ p)² d(γ⊗γ) = ∫ f² dγ
    set a := exp (-t)
    set b := sqrt (1 - exp (-2 * t))
    set φ : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
    have hφ : Measurable φ := Measurable.add
      (measurable_const.mul measurable_fst) (measurable_const.mul measurable_snd)
    have hmap := ou_kernel_map t ht
    have hf_meas : Measurable f := hf_core.measurable
    have hf_cont : Continuous f := hf_core.continuous
    obtain ⟨M, hM⟩ := hf_core.bounded
    -- integrability of f² under γ
    have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
    have hf2_int : Integrable (fun x => f x ^ 2) γ := by
      refine Integrable.mono' (integrable_const (M^2))
        ((hf_meas.pow_const 2).aemeasurable.aestronglyMeasurable) ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      have h1 : |f x| ≤ M := by rw [← Real.norm_eq_abs]; exact hM x
      have h2 : (f x)^2 ≤ M^2 := by
        have : |f x|^2 ≤ M^2 := by nlinarith [abs_nonneg (f x)]
        rwa [sq_abs] at this
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have : ‖M^2‖ = M^2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      linarith
    -- f² composed with φ is integrable on γ⊗γ
    have hf2_φ_int : Integrable (fun p => (f (φ p))^2) (γ.prod γ) := by
      have hlaw : HasLaw φ γ (γ.prod γ) := ⟨hφ.aemeasurable, hmap⟩
      have hf2_aesm : AEStronglyMeasurable (fun x => f x ^ 2) ((γ.prod γ).map φ) := by
        rw [hmap]; exact (hf_meas.pow_const 2).aestronglyMeasurable
      have hf2_int' : Integrable (fun x => f x ^ 2) ((γ.prod γ).map φ) := by
        rw [hmap]; exact hf2_int
      exact (integrable_map_measure hf2_aesm hφ.aemeasurable).mp hf2_int'
    -- φ_x : y ↦ f(ax+by). For each x, integrable on γ; its square too.
    have hfφ_int : ∀ x, Integrable (fun y => f (a * x + b * y)) γ := by
      intro x
      -- bounded by M, measurable
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hf_meas.comp (measurable_const.add (measurable_const.mul measurable_id')))
          |>.aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun y => (hM (a*x + b*y)))
    -- Jensen: for convex g = (·)², probability measure γ, integrable f:
    -- g(∫ f dγ) ≤ ∫ g∘f dγ
    have h_convex : ConvexOn ℝ Set.univ (fun x : ℝ => x^2) :=
      Even.convexOn_pow (Nat.even_iff.mpr rfl)
    have h_cont : ContinuousOn (fun x : ℝ => x^2) Set.univ :=
      (continuous_pow 2).continuousOn
    have h_closed : IsClosed (Set.univ : Set ℝ) := isClosed_univ
    -- For each x, apply Jensen to y ↦ f(ax+by).
    have hJensen : ∀ x, (∫ y, f (a*x + b*y) ∂γ)^2 ≤ ∫ y, (f (a*x + b*y))^2 ∂γ := by
      intro x
      have hfφ_aesm : ∀ᵐ y ∂γ, f (a*x + b*y) ∈ (Set.univ : Set ℝ) :=
        Filter.Eventually.of_forall (fun y => Set.mem_univ _)
      have hfφ2_int : Integrable (fun y => (f (a*x + b*y))^2) γ := by
        refine Integrable.mono' (integrable_const (M^2)) ?_ ?_
        · exact ((hf_meas.comp (measurable_const.add (measurable_const.mul measurable_id')))
            |>.pow_const 2).aestronglyMeasurable
        · refine Filter.Eventually.of_forall (fun y => ?_)
          have hnn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have h1 : |f (a*x + b*y)| ≤ M := by
            rw [← Real.norm_eq_abs]; exact hM (a*x + b*y)
          have h2 : (f (a*x + b*y))^2 ≤ M^2 := by
            have : |f (a*x + b*y)|^2 ≤ M^2 := by nlinarith [abs_nonneg (f (a*x + b*y))]
            rwa [sq_abs] at this
          have : ‖M^2‖ = M^2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          linarith
      exact ConvexOn.map_integral_le h_convex h_cont h_closed hfφ_aesm (hfφ_int x) hfφ2_int
    -- now integrate
    show ∫ x, (ouSemigroup t f x) ^ 2 ∂γ ≤ ∫ x, (f x) ^ 2 ∂γ
    simp only [ouSemigroup]
    calc ∫ x, (∫ y, f (a * x + b * y) ∂γ) ^ 2 ∂γ
        ≤ ∫ x, ∫ y, (f (a*x + b*y))^2 ∂γ ∂γ := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
          · -- integrability of the RHS: x ↦ ∫ y, (f(ax+by))² dγ
            exact hf2_φ_int.integral_prod_left
          · exact Filter.Eventually.of_forall hJensen
      _ = ∫ p, (f (φ p))^2 ∂(γ.prod γ) := (integral_prod _ hf2_φ_int).symm
      _ = ∫ x, (f x)^2 ∂γ := by
          -- ∫ f² d((γ⊗γ).map φ) = ∫ f² dγ by ou_kernel_map
          have hlaw : HasLaw φ γ (γ.prod γ) := ⟨hφ.aemeasurable, hmap⟩
          exact hlaw.integral_comp (hf_meas.pow_const 2).aestronglyMeasurable
  semigroup_mean := fun f t ht hf_core => by
    -- Unfold to get γ explicitly
    show ∫ x, ouSemigroup t f x ∂γ = ∫ x, f x ∂γ
    simp only [ouSemigroup]
    -- Goal: ∫ x, (∫ y, f(e^{-t}x + √(1-e^{-2t})y) dγ(y)) dγ(x) = ∫ f dγ
    set a := exp (-t)
    set b := sqrt (1 - exp (-2 * t))
    set φ : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
    have hφ : Measurable φ := Measurable.add
      (measurable_const.mul measurable_fst) (measurable_const.mul measurable_snd)
    have hmap := ou_kernel_map t ht
    have hlaw : HasLaw φ γ (γ.prod γ) := ⟨hφ.aemeasurable, hmap⟩
    -- Under IsCore, f is AEStronglyMeasurable and Integrable.
    have hf : AEStronglyMeasurable f γ :=
      hf_core.stronglyMeasurable.aestronglyMeasurable
    have hint : Integrable f γ := hf_core.integrable
    have hcomp : ∫ p, f (φ p) ∂(γ.prod γ) = ∫ x, f x ∂γ :=
      hlaw.integral_comp hf
    rw [← hcomp]
    have hasm' : AEStronglyMeasurable f ((γ.prod γ).map φ) := by rwa [hmap]
    have hint' : Integrable f ((γ.prod γ).map φ) := by rwa [hmap]
    have hfφ : Integrable (f ∘ φ) (γ.prod γ) :=
      (integrable_map_measure hasm' hφ.aemeasurable).mp hint'
    -- Goal: ∫ x, (∫ y, f(φ(x,y)) dγ) dγ = ∫ p, f(φ p) d(γ.prod γ)
    exact (integral_prod (f ∘ φ) hfφ).symm
  semigroup_selfAdjoint := fun f g t ht hf hg => by
    -- Goal: ∫ (P_t f)(x) · g(x) dγ(x) = ∫ f(x) · (P_t g)(x) dγ(x)
    -- Strategy: Fubini + reflection T(x,y) = (ax+by, bx-ay) preserves γ⊗γ
    show ∫ x, ouSemigroup t f x * g x ∂γ = ∫ x, f x * ouSemigroup t g x ∂γ
    simp only [ouSemigroup]
    set a := exp (-t)
    set b := sqrt (1 - exp (-2 * t))
    set φ : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
    have hφ : Measurable φ := Measurable.add
      (measurable_const.mul measurable_fst) (measurable_const.mul measurable_snd)
    have hmap := ou_kernel_map t ht
    have hab : a ^ 2 + b ^ 2 = 1 := by
      simp only [a, b]; rw [sq_sqrt (one_sub_exp_nonneg t ht), sq, ← exp_add]; ring
    -- Both sides by Fubini become product integrals:
    -- LHS = ∫ f(φ p) · g(p.1) d(γ⊗γ)
    -- RHS = ∫ f(p.1) · g(φ p) d(γ⊗γ)
    -- Integrability
    obtain ⟨Mf, hMf⟩ := hf.bounded
    obtain ⟨Mg, hMg⟩ := hg.bounded
    -- All our functions are bounded and measurable on γ⊗γ (probability measure)
    -- so integrability follows from Integrable.mono' (integrable_const _) ...
    have hfφ_int : Integrable (fun p => f (φ p)) (γ.prod γ) :=
      Integrable.mono' (integrable_const Mf)
        ((hf.measurable.comp hφ).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun p => hMf (φ p))
    have hgφ_int : Integrable (fun p => g (φ p)) (γ.prod γ) :=
      Integrable.mono' (integrable_const Mg)
        ((hg.measurable.comp hφ).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun p => hMg (φ p))
    have hf_fst_int : Integrable (fun p : ℝ × ℝ => f p.1) (γ.prod γ) :=
      Integrable.mono' (integrable_const Mf)
        ((hf.measurable.comp measurable_fst).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun p => hMf p.1)
    have hMf_nn : 0 ≤ Mf := le_trans (norm_nonneg _) (hMf 0)
    have hMg_nn : 0 ≤ Mg := le_trans (norm_nonneg _) (hMg 0)
    -- f(φ p) · g(p.1) is integrable (bounded by Mf * Mg)
    have hfg1_int : Integrable (fun p : ℝ × ℝ => f (φ p) * g p.1) (γ.prod γ) :=
      Integrable.mono' (integrable_const (Mf * Mg))
        (((hf.measurable.comp hφ).mul (hg.measurable.comp measurable_fst)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun p => by
          rw [norm_mul]; exact mul_le_mul (hMf _) (hMg _) (norm_nonneg _) hMf_nn)
    -- f(p.1) · g(φ p) is integrable (bounded by Mf * Mg)
    have hfg2_int : Integrable (fun p : ℝ × ℝ => f p.1 * g (φ p)) (γ.prod γ) :=
      Integrable.mono' (integrable_const (Mf * Mg))
        (((hf.measurable.comp measurable_fst).mul (hg.measurable.comp hφ)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun p => by
          rw [norm_mul]; exact mul_le_mul (hMf _) (hMg _) (norm_nonneg _) hMf_nn)
    -- Fubini: convert iterated → product
    -- LHS = ∫ x, (∫ y, f(ax+by) dγ) * g x dγ = ∫ p, f(φ p) * g(p.1) d(γ⊗γ)
    have hLHS : ∫ x, (∫ y, f (a*x + b*y) ∂γ) * g x ∂γ =
        ∫ p, f (φ p) * g p.1 ∂(γ.prod γ) := by
      -- integral_prod gives: ∫ p, h p d(γ⊗γ) = ∫ x, ∫ y, h(x,y) dγ dγ
      -- The RHS of integral_prod for our function is:
      --   ∫ x, (∫ y, f(a*x + b*y) * g x dγ) dγ
      -- We need to pull g x out of the inner integral to get:
      --   ∫ x, (∫ y, f(a*x + b*y) dγ) * g x dγ
      have h1 : ∫ p, f (φ p) * g p.1 ∂(γ.prod γ) =
          ∫ x, (∫ y, f (a * x + b * y) * g x ∂γ) ∂γ :=
        integral_prod _ hfg1_int
      rw [h1]; congr 1; ext x
      rw [integral_mul_const]
    -- RHS = ∫ x, f x * (∫ y, g(ax+by) dγ) dγ = ∫ p, f(p.1) * g(φ p) d(γ⊗γ)
    have hRHS : ∫ x, f x * (∫ y, g (a*x + b*y) ∂γ) ∂γ =
        ∫ p, f p.1 * g (φ p) ∂(γ.prod γ) := by
      have h1 : ∫ p, f p.1 * g (φ p) ∂(γ.prod γ) =
          ∫ x, (∫ y, f x * g (a * x + b * y) ∂γ) ∂γ :=
        integral_prod _ hfg2_int
      rw [h1]; congr 1; ext x
      rw [integral_const_mul]
    rw [hLHS, hRHS]
    -- Now apply the reflection T(x,y) = (ax+by, bx-ay) to the LHS
    -- T preserves γ⊗γ (orthogonal with a²+b² = 1)
    -- and sends f(φ p)·g(p.1) to f(p.1)·g(φ p)
    set T : ℝ × ℝ → ℝ × ℝ := fun p => (a * p.1 + b * p.2, b * p.1 - a * p.2)
    -- T sends fst to φ: (T p).1 = a*p.1 + b*p.2 = φ p
    -- T sends φ to fst: φ(T p) = a(a*p.1+b*p.2) + b(b*p.1-a*p.2) = (a²+b²)p.1 = p.1
    have hT_φ_to_fst : ∀ p : ℝ × ℝ, φ (T p) = p.1 := by
      intro p; simp only [φ, T]
      have : a * (a * p.1 + b * p.2) + b * (b * p.1 - a * p.2) =
          (a ^ 2 + b ^ 2) * p.1 := by ring
      rw [this, hab, one_mul]
    have hT_fst_to_φ : ∀ p : ℝ × ℝ, (T p).1 = φ p := fun p => rfl
    -- T preserves γ⊗γ — orthogonal invariance of the 2D standard Gaussian.
    have hT_preserves : (γ.prod γ).map T = γ.prod γ :=
      gaussian2D_orthogonal_invariance a b hab
    -- Change variables: ∫ h d(γ⊗γ) = ∫ h∘T d(γ⊗γ)
    have hT_meas : Measurable T := by
      apply Measurable.prod
      · exact (measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)
      · exact (measurable_const.mul measurable_fst).sub (measurable_const.mul measurable_snd)
    -- ∫ h ∘ T d(γ⊗γ) = ∫ h d((γ⊗γ).map T) = ∫ h d(γ⊗γ)
    -- So we rewrite the LHS: ∫ f(φ p) * g(p.1) d(γ⊗γ) = ∫ f(φ(T p)) * g((T p).1) d(γ⊗γ)
    -- Then use hT_φ_to_fst and hT_fst_to_φ to get the RHS
    have hfg1_aesm_map : AEStronglyMeasurable (fun p => f (φ p) * g p.1)
        ((γ.prod γ).map T) := by rw [hT_preserves]; exact hfg1_int.aestronglyMeasurable
    calc ∫ p, f (φ p) * g p.1 ∂(γ.prod γ)
        = ∫ p, f (φ (T p)) * g (T p).1 ∂(γ.prod γ) := by
          conv_lhs => rw [← hT_preserves]
          exact integral_map hT_meas.aemeasurable hfg1_aesm_map
      _ = ∫ p, f p.1 * g (φ p) ∂(γ.prod γ) := by
          congr 1; ext p; rw [hT_φ_to_fst, hT_fst_to_φ]
  semigroup_l2_decay_bound := fun f t ht hf =>
    ouSemigroup_l2_decay_bound f t ht hf
  semigroup_l2_sq_hasDerivWithinAt := fun f t ht hf => by
    -- ouGamma f g x = deriv f x * deriv g x (matches axiom statement).
    have h := ouSemigroup_l2_sq_hasDerivWithinAt_proved f t ht hf
    simpa [ouGamma] using h
  semigroup_ergodic := fun f hf => ouSemigroup_ergodic f hf
  semigroup_entropy_sq_decay_bound := fun f t ht hf =>
    ouSemigroup_entropy_sq_decay_bound f t ht hf
  semigroup_entropy_sq_ergodic := fun f hf => ouSemigroup_entropy_sq_ergodic f hf
end Gaussian1D

end
