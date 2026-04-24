/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Standard Gaussian on ℝ: BakryEmerySpace Instance

The canonical Bakry-Émery space: ℝ with standard Gaussian measure
γ = N(0,1) and the Ornstein-Uhlenbeck semigroup (Mehler formula):

  P_t f(x) = ∫ f(e^{-t}x + √(1-e^{-2t})y) dγ(y)

  Γ(f,g)(x) = f'(x)·g'(x)
  E(f,f) = ∫ (f')² dγ
  ρ = 1 (Bakry-Émery curvature)

This is the setting of Gross's original 1975 theorem. Unlike the
TwoPoint instance, ℝ is a continuous state space so ALL BakryEmerySpace
fields hold, including Γ_leibniz (the diffusion/Leibniz property).

## Status

The easy algebraic fields are proved. The hard analytical fields
(involving Fubini, differentiation under the integral, generator
theory) are sorry'd with proof sketches. Each sorry is a standard
textbook result; the obstacle is Lean/Mathlib infrastructure for
parametric integration against continuous measures.

## References

- Gross, "Logarithmic Sobolev inequalities," Amer. J. Math. 97 (1975)
- Bakry, Gentil, Ledoux, Ch. 2 (OU semigroup and Gaussian measures)
-/

import MarkovSemigroups.Diffusion.CarreDuChamp
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

open MeasureTheory Filter Set Real ProbabilityTheory

noncomputable section

namespace Gaussian1D

/-! ## Definitions -/

/-- The standard Gaussian measure on ℝ. -/
def γ : Measure ℝ := gaussianReal 0 1

instance : IsProbabilityMeasure γ := by
  unfold γ; infer_instance

/-- The Ornstein-Uhlenbeck semigroup via Mehler's formula:
  P_t f(x) = ∫ f(e^{-t}x + √(1-e^{-2t})y) dγ(y). -/
def ouSemigroup (t : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ y, f (exp (-t) * x + sqrt (1 - exp (-2 * t)) * y) ∂γ

/-- The carré du champ: Γ(f,g)(x) = f'(x) · g'(x). -/
def ouGamma (f g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv f x * deriv g x

/-- The Dirichlet energy: E(f,g) = ∫ f'·g' dγ. -/
def ouEnergy (f g : ℝ → ℝ) : ℝ :=
  ∫ x, deriv f x * deriv g x ∂γ

/-! ## Helper lemmas -/

/-- For t ≥ 0: exp(-2t) ≤ 1 so 1 - exp(-2t) ≥ 0. -/
theorem one_sub_exp_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ 1 - exp (-2 * t) := by
  linarith [exp_le_one_iff.mpr (by linarith : -2 * t ≤ 0)]

/-- The OU kernel map (x,y) ↦ e^{-t}x + √(1-e^{-2t})y sends γ×γ to γ.
This is because e^{-2t} + (1 - e^{-2t}) = 1, so the sum of scaled
independent N(0,1) variables is N(0,1). -/
theorem ou_kernel_map (t : ℝ) (ht : 0 ≤ t) :
    (γ.prod γ).map (fun p : ℝ × ℝ => exp (-t) * p.1 + sqrt (1 - exp (-2 * t)) * p.2) = γ := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  -- On γ.prod γ, Prod.fst and Prod.snd are independent with law γ = N(0,1)
  have hX : HasLaw (fun p : ℝ × ℝ => p.1) γ (γ.prod γ) :=
    ⟨measurable_fst.aemeasurable,
     by rw [Measure.map_fst_prod]; simp [measure_univ]⟩
  have hY : HasLaw (fun p : ℝ × ℝ => p.2) γ (γ.prod γ) :=
    ⟨measurable_snd.aemeasurable,
     by rw [Measure.map_snd_prod]; simp [measure_univ]⟩
  -- a * fst has law N(0, a²)
  have haX := gaussianReal_const_mul hX a
  -- b * snd has law N(0, b²)
  have hbY := gaussianReal_const_mul hY b
  -- Independence of a*fst and b*snd
  have hindep : (fun p : ℝ × ℝ => a * p.1) ⟂ᵢ[γ.prod γ] (fun p : ℝ × ℝ => b * p.2) :=
    (indepFun_prod measurable_id measurable_id).comp
      (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  -- Sum has law N(0, a²+b²)
  have hmap := gaussianReal_add_gaussianReal_of_indepFun hindep haX.map_eq hbY.map_eq
  -- Key: a² + b² = 1 (as ℝ)
  have hab_real : a ^ 2 + b ^ 2 = 1 := by
    simp only [a, b]
    rw [sq_sqrt (one_sub_exp_nonneg t ht), sq, ← exp_add]
    ring
  -- Simplify the gaussianReal parameters to get γ
  have hgoal : gaussianReal (a * 0 + b * 0)
      (⟨a ^ 2, sq_nonneg a⟩ * 1 + ⟨b ^ 2, sq_nonneg b⟩ * 1) = γ := by
    show gaussianReal (a * 0 + b * 0) (⟨a ^ 2, sq_nonneg a⟩ * 1 + ⟨b ^ 2, sq_nonneg b⟩ * 1)
        = gaussianReal 0 1
    congr 1
    · simp
    · simp only [mul_one]
      exact NNReal.eq (by simp [NNReal.coe_add, NNReal.coe_mk]; exact hab_real)
  rw [hgoal] at hmap
  exact hmap

/-! ## DirichletSpace instance -/

/-- The core algebra for OU on ℝ: smooth functions with bounded first and
second derivatives. Closed under constants, addition, scalar multiplication;
closure under products and the semigroup is stated with `sorry` — these
are standard but tedious (bounded derivatives remain bounded under these
operations). -/
def IsCore (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ f ∧ ∃ M : ℝ,
    ∀ x, ‖f x‖ ≤ M ∧ ‖deriv f x‖ ≤ M ∧ ‖deriv (deriv f) x‖ ≤ M

/-! ## IsCore helpers -/

theorem IsCore.contDiff {f : ℝ → ℝ} (hf : IsCore f) : ContDiff ℝ ⊤ f := hf.1

theorem IsCore.differentiable {f : ℝ → ℝ} (hf : IsCore f) : Differentiable ℝ f :=
  hf.1.differentiable (by simp)

theorem IsCore.contDiff_deriv {f : ℝ → ℝ} (hf : IsCore f) :
    ContDiff ℝ ⊤ (deriv f) := by
  -- From ContDiff ℝ ω f, deriv f is also ContDiff ℝ ω.
  have hω : ContDiff ℝ (⊤ : WithTop ℕ∞) f := hf.1
  -- Using ContDiff.deriv' we only get down by 1, but ⊤ + 1 = ⊤ here (ω-analytic).
  -- Simpler: derive from ContDiff at order 2 which suffices for our use.
  have h2 : ContDiff ℝ 2 f := hf.1.of_le (by
    exact_mod_cast (OrderTop.le_top (2 : WithTop ℕ∞)))
  -- but we want to return top-level deriv ContDiff. Use fun_prop:
  exact hf.1.deriv'.of_le (by
    exact_mod_cast (OrderTop.le_top _))

theorem IsCore.differentiable_deriv {f : ℝ → ℝ} (hf : IsCore f) :
    Differentiable ℝ (deriv f) :=
  hf.contDiff_deriv.differentiable (by simp)

theorem IsCore.continuous {f : ℝ → ℝ} (hf : IsCore f) : Continuous f :=
  hf.1.continuous

theorem IsCore.measurable {f : ℝ → ℝ} (hf : IsCore f) : Measurable f :=
  hf.continuous.measurable

theorem IsCore.stronglyMeasurable {f : ℝ → ℝ} (hf : IsCore f) :
    StronglyMeasurable f :=
  hf.continuous.stronglyMeasurable

theorem IsCore.bounded {f : ℝ → ℝ} (hf : IsCore f) :
    ∃ M, ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨_, M, hM⟩ := hf
  exact ⟨M, fun x => (hM x).1⟩

theorem IsCore.integrable {f : ℝ → ℝ} (hf : IsCore f) : Integrable f γ := by
  obtain ⟨M, hM⟩ := hf.bounded
  refine Integrable.mono' (integrable_const M) hf.stronglyMeasurable.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun x => hM x)

@[reducible]
def dirichletSpace : DirichletSpace ℝ where
  μ := γ
  hμ := inferInstance
  energy := ouEnergy
  energy_symm := fun f g => by
    simp only [ouEnergy]; congr 1; ext x; ring
  energy_nonneg := fun f => by
    simp only [ouEnergy]
    exact integral_nonneg (fun x => mul_self_nonneg (deriv f x))
  IsCore := IsCore
  IsCore_const := fun c => by
    refine ⟨contDiff_const, ⟨‖c‖, fun x => ?_⟩⟩
    refine ⟨le_refl _, ?_, ?_⟩
    · simp [deriv_const]
    · simp [deriv_const]
  IsCore_add := by
    rintro f g hf hg
    obtain ⟨hf_smooth, Mf, hfM⟩ := hf
    obtain ⟨hg_smooth, Mg, hgM⟩ := hg
    refine ⟨hf_smooth.add hg_smooth, ⟨Mf + Mg, fun x => ?_⟩⟩
    have hdf : DifferentiableAt ℝ f x :=
      (hf_smooth.differentiable (by simp)).differentiableAt
    have hdg : DifferentiableAt ℝ g x :=
      (hg_smooth.differentiable (by simp)).differentiableAt
    have hdf' : DifferentiableAt ℝ (deriv f) x :=
      (IsCore.contDiff_deriv ⟨hf_smooth, Mf, hfM⟩).differentiable (by simp) |>.differentiableAt
    have hdg' : DifferentiableAt ℝ (deriv g) x :=
      (IsCore.contDiff_deriv ⟨hg_smooth, Mg, hgM⟩).differentiable (by simp) |>.differentiableAt
    have hderiv_sum : deriv (f + g) x = deriv f x + deriv g x := deriv_add hdf hdg
    -- deriv (deriv (f+g)) = deriv (deriv f + deriv g) = deriv (deriv f) + deriv (deriv g)
    have hderiv2_sum : deriv (deriv (f + g)) x = deriv (deriv f) x + deriv (deriv g) x := by
      have heq : deriv (f + g) = (fun y => deriv f y + deriv g y) := by
        ext y
        have hdfy : DifferentiableAt ℝ f y :=
          (hf_smooth.differentiable (by simp)).differentiableAt
        have hdgy : DifferentiableAt ℝ g y :=
          (hg_smooth.differentiable (by simp)).differentiableAt
        exact deriv_add hdfy hdgy
      rw [heq]
      exact deriv_add hdf' hdg'
    refine ⟨?_, ?_, ?_⟩
    · show ‖(f + g) x‖ ≤ Mf + Mg
      calc ‖(f + g) x‖ = ‖f x + g x‖ := rfl
        _ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
        _ ≤ Mf + Mg := add_le_add (hfM x).1 (hgM x).1
    · rw [hderiv_sum]
      calc ‖deriv f x + deriv g x‖ ≤ ‖deriv f x‖ + ‖deriv g x‖ := norm_add_le _ _
        _ ≤ Mf + Mg := add_le_add (hfM x).2.1 (hgM x).2.1
    · rw [hderiv2_sum]
      calc ‖deriv (deriv f) x + deriv (deriv g) x‖
          ≤ ‖deriv (deriv f) x‖ + ‖deriv (deriv g) x‖ := norm_add_le _ _
        _ ≤ Mf + Mg := add_le_add (hfM x).2.2 (hgM x).2.2
  IsCore_smul := by
    rintro c f hf
    obtain ⟨hf_smooth, Mf, hfM⟩ := hf
    refine ⟨hf_smooth.const_smul c, ⟨‖c‖ * Mf, fun x => ?_⟩⟩
    -- (c • f) x = c * f x
    have h1 : (c • f) x = c * f x := rfl
    have h_deriv : deriv (c • f) x = c * deriv f x := by
      have := deriv_const_smul_field c f (x := x)
      simpa [smul_eq_mul] using this
    have h_deriv_fun : deriv (c • f) = fun y => c * deriv f y := by
      ext y
      have := deriv_const_smul_field c f (x := y)
      simpa [smul_eq_mul] using this
    have h_deriv2 : deriv (deriv (c • f)) x = c * deriv (deriv f) x := by
      rw [h_deriv_fun]
      have : deriv (fun y => c * deriv f y) x = c * deriv (deriv f) x := by
        have := deriv_const_smul_field c (deriv f) (x := x)
        simp [smul_eq_mul] at this; exact this
      exact this
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hfM x).1 (norm_nonneg c)
    · rw [h_deriv, norm_mul]
      exact mul_le_mul_of_nonneg_left (hfM x).2.1 (norm_nonneg c)
    · rw [h_deriv2, norm_mul]
      exact mul_le_mul_of_nonneg_left (hfM x).2.2 (norm_nonneg c)
  energy_add_left := fun f₁ f₂ g hf₁ hf₂ hg => by
    simp only [ouEnergy]
    -- deriv (f₁ + f₂) = deriv f₁ + deriv f₂ pointwise, since both are differentiable.
    have hderiv : ∀ x, deriv (f₁ + f₂) x * deriv g x =
        deriv f₁ x * deriv g x + deriv f₂ x * deriv g x := fun x => by
      rw [deriv_add (hf₁.differentiable.differentiableAt)
                    (hf₂.differentiable.differentiableAt)]
      ring
    simp_rw [hderiv]
    -- integrability of products
    have hdf₁_bound : ∃ M, ∀ x, ‖deriv f₁ x‖ ≤ M := ⟨hf₁.2.choose, fun x => (hf₁.2.choose_spec x).2.1⟩
    have hdf₂_bound : ∃ M, ∀ x, ‖deriv f₂ x‖ ≤ M := ⟨hf₂.2.choose, fun x => (hf₂.2.choose_spec x).2.1⟩
    have hdg_bound  : ∃ M, ∀ x, ‖deriv g  x‖ ≤ M := ⟨hg.2.choose, fun x => (hg.2.choose_spec x).2.1⟩
    have hdf₁_meas : Measurable (deriv f₁) :=
      (hf₁.1.continuous_deriv (by simp)).measurable
    have hdf₂_meas : Measurable (deriv f₂) :=
      (hf₂.1.continuous_deriv (by simp)).measurable
    have hdg_meas  : Measurable (deriv g) :=
      (hg.1.continuous_deriv (by simp)).measurable
    -- integrability of deriv f₁ * deriv g and deriv f₂ * deriv g
    obtain ⟨M₁, hM₁⟩ := hdf₁_bound
    obtain ⟨M₂, hM₂⟩ := hdf₂_bound
    obtain ⟨Mg, hMg⟩ := hdg_bound
    have hint₁ : Integrable (fun x => deriv f₁ x * deriv g x) γ := by
      refine Integrable.mono' (integrable_const (M₁ * Mg))
        ((hdf₁_meas.mul hdg_meas).aemeasurable.aestronglyMeasurable) ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |deriv f₁ x| ≤ M₁ := by rw [← Real.norm_eq_abs]; exact hM₁ x
      have h2 : |deriv g x| ≤ Mg := by rw [← Real.norm_eq_abs]; exact hMg x
      have hM₁_nn : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
      have hMg_nn : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0)
      exact mul_le_mul h1 h2 (abs_nonneg _) hM₁_nn
    have hint₂ : Integrable (fun x => deriv f₂ x * deriv g x) γ := by
      refine Integrable.mono' (integrable_const (M₂ * Mg))
        ((hdf₂_meas.mul hdg_meas).aemeasurable.aestronglyMeasurable) ?_
      refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |deriv f₂ x| ≤ M₂ := by rw [← Real.norm_eq_abs]; exact hM₂ x
      have h2 : |deriv g x| ≤ Mg := by rw [← Real.norm_eq_abs]; exact hMg x
      have hM₂_nn : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0)
      have hMg_nn : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0)
      exact mul_le_mul h1 h2 (abs_nonneg _) hM₂_nn
    rw [integral_add hint₁ hint₂]
  energy_smul_left := fun c f g _ _ => by
    simp only [ouEnergy]
    have h : ∀ x, deriv (c • f) x = c * deriv f x := fun x => by
      have := deriv_const_smul_field c f (x := x)
      simp only [smul_eq_mul] at this
      exact this
    simp_rw [h, mul_assoc]
    exact integral_const_mul c _
  energy_const := fun c => by
    simp only [ouEnergy, deriv_const, zero_mul, integral_zero]

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
  IsCore_semigroup := fun t ht f hf => by
    -- P_t preserves smoothness and bounded derivatives. Standard but tedious.
    sorry
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
  gradient_decay := fun f t ht _ => by
    -- ∫ (P_t f')² dγ ≤ e^{-2t} ∫ (f')² dγ
    -- Proof: by Mehler, (P_t f)'(x) = e^{-t} ∫ f'(e^{-t}x + √(1-e^{-2t})y) dγ(y)
    -- so (P_t f)'(x)² = e^{-2t} (∫ f'(...) dγ(y))² ≤ e^{-2t} ∫ (f'(...))² dγ(y)
    -- by Jensen. Integrating over x and using Fubini gives the result.
    sorry
  semigroup_zero := fun f => by
    ext x
    simp only [ouSemigroup, neg_zero, exp_zero, mul_zero, sub_self, sqrt_zero,
               zero_mul, add_zero, one_mul]
    simp [integral_const]
  semigroup_add := fun s t f hs ht => by
    -- Semigroup property P_{s+t} = P_s ∘ P_t.
    -- Proof: the composition of two Mehler kernels with parameters (s) and (t)
    -- gives a Mehler kernel with parameter (s+t), using
    -- e^{-(s+t)} = e^{-s}·e^{-t} and the Gaussian convolution formula.
    sorry
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
    -- T preserves γ⊗γ
    have hT_preserves : (γ.prod γ).map T = γ.prod γ := by
      sorry -- orthogonal invariance of 2D Gaussian
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
  semigroup_l2_decay_bound := fun f t ht _ => by
    -- Integrated gradient decay. Follows from gradient_decay + FTC.
    sorry
  semigroup_l2_sq_hasDerivWithinAt := fun f t ht _ => by
    -- d/dt ∫(P_t f)² dγ = -2 ∫ (P_t f')² dγ = -2 E(P_t f).
    -- Requires differentiation under the integral for the Mehler kernel.
    sorry
  semigroup_ergodic := fun f _ => by
    -- Var(P_t f) → 0: as t → ∞, P_t f → E[f] in L²(γ) since
    -- e^{-t} → 0 and √(1-e^{-2t}) → 1, so P_t f(x) → ∫ f dγ.
    sorry
  semigroup_entropy_sq_decay_bound := fun f t ht _ => by
    -- Entropy decay bound. Follows from Γ_leibniz (giving I(f²) = 4E(f))
    -- and gradient_decay for Fisher information.
    sorry
  semigroup_entropy_sq_ergodic := fun f _ => by
    -- Ent(P_t(f²)) → 0 by ergodicity + continuity of x·log(x).
    sorry

end Gaussian1D

end
