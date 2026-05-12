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
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

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

/-! ## Textbook axioms (Gaussian OU semigroup, BGL Ch. 2)

These nine axioms package standard properties of the Ornstein–Uhlenbeck
semigroup on the standard Gaussian on `ℝ`. Each is a textbook result
(Gross 1975; Bakry–Gentil–Ledoux 2014, Ch. 2). The Lean obstruction in
every case is parametric integration infrastructure (Fubini for OU
products, differentiation under the integral against the Mehler kernel)
that is not yet in Mathlib at the level of generality required.

**Source:** Bakry, Gentil, Ledoux, *Analysis and Geometry of Markov
Diffusion Operators*, Springer 2014, Ch. 2 (§2.7.1 OU semigroup);
Gross, *Logarithmic Sobolev inequalities*, Amer. J. Math. 97 (1975).

**Vetting status:** to be reviewed via Gemini chat (gemini-3-pro-preview)
in the same pass that introduces these axioms; status recorded in the
project audit table. -/

/-- **Orthogonal invariance of the 2D standard Gaussian (BGL Ch. 1).**

For real `a, b` with `a² + b² = 1`, the orthogonal map
`T(x,y) = (a·x + b·y, b·x - a·y)` preserves the product measure
`γ ⊗ γ = N(0,1) ⊗ N(0,1)`.

Reference: BGL §1.10.1 (rotational invariance of the Gaussian). The two
components of `T(x,y)` are jointly Gaussian with mean 0 and identity
covariance because `a² + b² = 1`. Consumed inside
`semigroup_selfAdjoint` to convert `f(φ p) · g(p.1)` to its mirror via
the change-of-variables formula. -/
theorem gaussian2D_orthogonal_invariance
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (γ.prod γ).map (fun p : ℝ × ℝ => (a * p.1 + b * p.2, b * p.1 - a * p.2))
      = γ.prod γ := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × ℝ) :=
    { toLinearEquiv :=
        { toFun := fun x => WithLp.toLp 2 (x 0, x 1)
          invFun := fun p => !₂[p.fst, p.snd]
          left_inv := by
            intro x
            apply (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).injective
            funext i
            fin_cases i <;> rfl
          right_inv := by
            intro p
            apply (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).injective
            rfl
          map_add' := by
            intro x y
            rfl
          map_smul' := by
            intro c x
            rfl }
      norm_map' := by
        intro x
        change ‖WithLp.toLp 2 (x 0, x 1)‖ = ‖x‖
        rw [← sq_eq_sq₀ (show 0 ≤ ‖WithLp.toLp 2 (x 0, x 1)‖ by positivity)
          (show 0 ≤ ‖x‖ by positivity)]
        simp [EuclideanSpace, PiLp.norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2] }
  let U : WithLp 2 (ℝ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℝ × ℝ) :=
    { toLinearEquiv :=
        { toFun := fun p => WithLp.toLp 2 (a * p.fst + b * p.snd, b * p.fst - a * p.snd)
          invFun := fun p => WithLp.toLp 2 (a * p.fst + b * p.snd, b * p.fst - a * p.snd)
          left_inv := by
            intro p
            apply (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).injective
            ext
            · calc
                a * (a * p.fst + b * p.snd) + b * (b * p.fst - a * p.snd)
                    = (a ^ 2 + b ^ 2) * p.fst := by ring
                _ = p.fst := by rw [hab]; ring
            · calc
                b * (a * p.fst + b * p.snd) - a * (b * p.fst - a * p.snd)
                    = (a ^ 2 + b ^ 2) * p.snd := by ring
                _ = p.snd := by rw [hab]; ring
          right_inv := by
            intro p
            apply (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).injective
            ext
            · calc
                a * (a * p.fst + b * p.snd) + b * (b * p.fst - a * p.snd)
                    = (a ^ 2 + b ^ 2) * p.fst := by ring
                _ = p.fst := by rw [hab]; ring
            · calc
                b * (a * p.fst + b * p.snd) - a * (b * p.fst - a * p.snd)
                    = (a ^ 2 + b ^ 2) * p.snd := by ring
                _ = p.snd := by rw [hab]; ring
          map_add' := by
            intro p q
            apply (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).injective
            ext <;> simp [mul_add, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
          map_smul' := by
            intro c p
            apply (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).injective
            ext <;> simp [mul_add, mul_left_comm, sub_eq_add_neg] }
      norm_map' := by
        intro p
        change ‖WithLp.toLp 2 (a * p.fst + b * p.snd, b * p.fst - a * p.snd)‖ = ‖p‖
        rw [← sq_eq_sq₀ (show 0 ≤ ‖WithLp.toLp 2 (a * p.fst + b * p.snd, b * p.fst - a * p.snd)‖ by positivity)
          (show 0 ≤ ‖p‖ by positivity),
          WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
        simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs]
        calc
          (a * p.fst + b * p.snd) ^ 2 + (b * p.fst - a * p.snd) ^ 2 =
              (a ^ 2 + b ^ 2) * (p.fst ^ 2 + p.snd ^ 2) := by ring
          _ = p.fst ^ 2 + p.snd ^ 2 := by rw [hab]; ring }
  have hstd : (γ.prod γ).map (WithLp.toLp 2) = ProbabilityTheory.stdGaussian (WithLp 2 (ℝ × ℝ)) := by
    have hecomp : e ∘ WithLp.toLp 2 = fun x : Fin 2 → ℝ => WithLp.toLp 2 (x 0, x 1) := by
      funext x
      rfl
    have hmap_pi :
        ((Measure.pi fun _ : Fin 2 => γ).map (fun x : Fin 2 → ℝ => WithLp.toLp 2 (x 0, x 1))) =
          ProbabilityTheory.stdGaussian (WithLp 2 (ℝ × ℝ)) := by
      calc
        ((Measure.pi fun _ : Fin 2 => γ).map (fun x : Fin 2 → ℝ => WithLp.toLp 2 (x 0, x 1)))
            = (((Measure.pi fun _ : Fin 2 => γ).map (WithLp.toLp 2)).map e) := by
                rw [← hecomp]
                rw [Measure.map_map (by fun_prop) (by fun_prop)]
        _ = (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))).map e := by
              simpa [γ] using congrArg (fun μ => μ.map e) (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin 2))
        _ = ProbabilityTheory.stdGaussian (WithLp 2 (ℝ × ℝ)) := by
              simpa using ProbabilityTheory.stdGaussian_map e
    have hfin :
        (Measure.pi fun _ : Fin 2 => γ).map (fun x : Fin 2 → ℝ => (x 0, x 1)) = γ.prod γ := by
      simpa using (MeasureTheory.measurePreserving_finTwoArrow γ).map_eq
    calc
      (γ.prod γ).map (WithLp.toLp 2)
          = (((Measure.pi fun _ : Fin 2 => γ).map (fun x : Fin 2 → ℝ => (x 0, x 1))).map (WithLp.toLp 2)) := by
              rw [hfin]
      _ = ((Measure.pi fun _ : Fin 2 => γ).map (fun x : Fin 2 → ℝ => WithLp.toLp 2 (x 0, x 1))) := by
            simpa [Function.comp_def] using
              (Measure.map_map (μ := Measure.pi fun _ : Fin 2 => γ)
                (f := fun x : Fin 2 → ℝ => (x 0, x 1)) (g := WithLp.toLp 2)
                (by fun_prop) (show Measurable (fun x : Fin 2 → ℝ => (x 0, x 1)) by fun_prop))
      _ = ProbabilityTheory.stdGaussian (WithLp 2 (ℝ × ℝ)) := hmap_pi
  have hU :
      ((γ.prod γ).map (fun p : ℝ × ℝ => (a * p.1 + b * p.2, b * p.1 - a * p.2))).map (WithLp.toLp 2) =
        (γ.prod γ).map (WithLp.toLp 2) := by
    calc
      ((γ.prod γ).map (fun p : ℝ × ℝ => (a * p.1 + b * p.2, b * p.1 - a * p.2))).map (WithLp.toLp 2)
          = ((γ.prod γ).map (WithLp.toLp 2)).map U := by
              rw [Measure.map_map (μ := γ.prod γ)
                (f := fun p : ℝ × ℝ => (a * p.1 + b * p.2, b * p.1 - a * p.2))
                (g := WithLp.toLp 2) (by fun_prop) (by fun_prop),
                Measure.map_map (μ := γ.prod γ) (f := WithLp.toLp 2) (g := U) (by fun_prop)
                  (by fun_prop)]
              rfl
      _ = (ProbabilityTheory.stdGaussian (WithLp 2 (ℝ × ℝ))).map U := by rw [hstd]
      _ = ProbabilityTheory.stdGaussian (WithLp 2 (ℝ × ℝ)) := by
            simpa using ProbabilityTheory.stdGaussian_map U
      _ = (γ.prod γ).map (WithLp.toLp 2) := hstd.symm
  let ew : WithLp 2 (ℝ × ℝ) ≃ᵐ ℝ × ℝ :=
    (WithLp.homeomorphProd (p := 2) (α := ℝ) (β := ℝ)).toMeasurableEquiv
  have := congrArg (fun μ : Measure (WithLp 2 (ℝ × ℝ)) => μ.map WithLp.ofLp) hU
  have hback_left :
      Measure.map WithLp.ofLp
          (Measure.map (WithLp.toLp 2)
            (Measure.map (fun p : ℝ × ℝ => (a * p.1 + b * p.2, b * p.1 - a * p.2)) (γ.prod γ))) =
        Measure.map (fun p : ℝ × ℝ => (a * p.1 + b * p.2, b * p.1 - a * p.2)) (γ.prod γ) := by
    simpa [ew] using
      (MeasurableEquiv.map_map_symm
        (ν := Measure.map (fun p : ℝ × ℝ => (a * p.1 + b * p.2, b * p.1 - a * p.2)) (γ.prod γ))
        ew)
  have hback_right :
      Measure.map WithLp.ofLp (Measure.map (WithLp.toLp 2) (γ.prod γ)) = γ.prod γ := by
    simpa [ew] using (MeasurableEquiv.map_map_symm (ν := γ.prod γ) ew)
  calc
    Measure.map (fun p : ℝ × ℝ => (a * p.1 + b * p.2, b * p.1 - a * p.2)) (γ.prod γ)
        = Measure.map WithLp.ofLp
            (Measure.map (WithLp.toLp 2)
              (Measure.map (fun p : ℝ × ℝ => (a * p.1 + b * p.2, b * p.1 - a * p.2)) (γ.prod γ))) := hback_left.symm
    _ = Measure.map WithLp.ofLp (Measure.map (WithLp.toLp 2) (γ.prod γ)) := this
    _ = γ.prod γ := hback_right

/-! ### `IsCore` preservation by `ouSemigroup` (BGL §2.7)

The original axiom `ouSemigroup_preserves_IsCore` was decomposed (2026-05-12):
the bounded parts (`|P_t f|, |(P_t f)'|, |(P_t f)''| ≤ M`) are PROVED in
`ouSemigroup_preserves_bounds` via the Mehler derivative formulas
`(P_t f)' = e^{-t} P_t(f')` and `(P_t f)'' = e^{-2t} P_t(f'')`. Only the
`ContDiff ℝ ⊤` smoothing remains as a smaller atomic axiom
(`ouSemigroup_contDiff`). The combination
(`ouSemigroup_preserves_IsCore`) is now a theorem, defined below after
the bound proof. -/

/-- **Smoothing of `ouSemigroup`** (BGL §2.7.1, atomic). The OU semigroup
applied to a `C^∞` function (or even bounded measurable) produces a
`C^∞` function in `x` — a consequence of the Mehler kernel's `C^∞`
regularity. Full discharge requires Mathlib infrastructure for `ContDiff`
of parametric integrals at all orders (Schwartz-class kernel convolution),
which is not yet present.

Reference: BGL §2.7.1; the Mehler kernel is `C^∞` in `x` with all
derivatives integrable against bounded `f`. -/
axiom ouSemigroup_contDiff (t : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (ouSemigroup t f)

/-- **Mehler derivative formula, generalized hypothesis.** PROVED.

For any `C¹` `f` with `f` and `deriv f` bounded by `M`,
  `(P_t f)'(x₀) = e^{-t} · P_t(f')(x₀)`.

This weakens `hasDerivAt_ouSemigroup` (which requires `IsCore f`) to just
need C¹ smoothness + bounded f, f' — enabling iterated application for
higher-order Mehler derivatives. -/
theorem hasDerivAt_ouSemigroup_C1 (t : ℝ) {f : ℝ → ℝ}
    (hf_C1 : ContDiff ℝ 1 f) {M : ℝ}
    (hf_bd : ∀ x, ‖f x‖ ≤ M) (hf'_bd : ∀ x, ‖deriv f x‖ ≤ M)
    (x₀ : ℝ) :
    HasDerivAt (ouSemigroup t f)
      (Real.exp (-t) * ouSemigroup t (deriv f) x₀) x₀ := by
  set a := Real.exp (-t)
  set b := Real.sqrt (1 - Real.exp (-2 * t))
  set F : ℝ → ℝ → ℝ := fun x y => f (a * x + b * y)
  set F' : ℝ → ℝ → ℝ := fun x y => a * deriv f (a * x + b * y)
  set bound : ℝ → ℝ := fun _ => |a| * M
  have hs : Set.Ioo (x₀ - 1) (x₀ + 1) ∈ nhds x₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hf_meas : Measurable f := hf_C1.continuous.measurable
  have hF_meas : ∀ x, AEStronglyMeasurable (F x) γ := by
    intro x
    refine (hf_meas.comp ?_).aestronglyMeasurable
    exact measurable_const.add (measurable_const.mul measurable_id)
  have hF_int : Integrable (F x₀) γ := by
    refine Integrable.mono' (integrable_const M) (hF_meas x₀) ?_
    filter_upwards with y; exact hf_bd (a * x₀ + b * y)
  have hf'_meas : Measurable (deriv f) :=
    (hf_C1.continuous_deriv (by simp)).measurable
  have hF'_meas : AEStronglyMeasurable (F' x₀) γ := by
    refine (measurable_const.mul ?_).aestronglyMeasurable
    exact hf'_meas.comp (measurable_const.add (measurable_const.mul measurable_id))
  have h_bound : ∀ᵐ y ∂γ, ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 1),
      ‖F' x y‖ ≤ bound y := by
    filter_upwards with y x _
    show ‖a * deriv f (a * x + b * y)‖ ≤ |a| * M
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |deriv f (a * x + b * y)| ≤ M := by
      rw [← Real.norm_eq_abs]; exact hf'_bd _
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
  have h_bound_int : Integrable bound γ := integrable_const _
  have h_diff : ∀ᵐ y ∂γ, ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 1),
      HasDerivAt (F · y) (F' x y) x := by
    filter_upwards with y x _
    show HasDerivAt (fun x => f (a * x + b * y)) (a * deriv f (a * x + b * y)) x
    have h_inner : HasDerivAt (fun x => a * x + b * y) a x := by
      simpa using ((hasDerivAt_id x).const_mul a).add_const (b * y)
    have h_f : HasDerivAt f (deriv f (a * x + b * y)) (a * x + b * y) :=
      (hf_C1.differentiable (by simp)).differentiableAt.hasDerivAt
    have := h_f.comp x h_inner
    simpa [mul_comm a (deriv f _)] using this
  obtain ⟨_, h_deriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
      (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas h_bound h_bound_int h_diff
  have h_lhs_eq : (fun x => ∫ y, F x y ∂γ) = ouSemigroup t f := rfl
  have h_rhs_eq : ∫ y, F' x₀ y ∂γ = Real.exp (-t) * ouSemigroup t (deriv f) x₀ := by
    show ∫ y, a * deriv f (a * x₀ + b * y) ∂γ = a * ouSemigroup t (deriv f) x₀
    rw [integral_const_mul]; rfl
  rw [← h_lhs_eq, ← h_rhs_eq]
  exact h_deriv

/-- **Mehler derivative formula (BGL §2.7).** PROVED.

  `(P_t f)'(x₀) = e^{-t} · P_t(f')(x₀)`.

Corollary of `hasDerivAt_ouSemigroup_C1` for `IsCore f`. -/
theorem hasDerivAt_ouSemigroup (t : ℝ) {f : ℝ → ℝ} (hf : IsCore f) (x₀ : ℝ) :
    HasDerivAt (ouSemigroup t f)
      (Real.exp (-t) * ouSemigroup t (deriv f) x₀) x₀ := by
  obtain ⟨h_smooth, M, hM⟩ := hf
  refine hasDerivAt_ouSemigroup_C1 t
    (h_smooth.of_le (by simp : ((1 : WithTop ℕ∞)) ≤ ⊤))
    (M := M) (fun x => (hM x).1) (fun x => (hM x).2.1) x₀

/-- Pointwise: `deriv (ouSemigroup t f) x = e^{-t} · ouSemigroup t (deriv f) x`. -/
theorem deriv_ouSemigroup_eq {f : ℝ → ℝ} (hf : IsCore f) (t : ℝ) :
    deriv (ouSemigroup t f) = fun x => Real.exp (-t) * ouSemigroup t (deriv f) x := by
  funext x; exact (hasDerivAt_ouSemigroup t hf x).deriv

/-- **Second-order Mehler derivative formula.** PROVED.

  `(P_t f)''(x₀) = e^{-2t} · P_t(f'')(x₀)`.

Iterated application of `hasDerivAt_ouSemigroup_C1`: apply once to `f` (giving
`(P_t f)' = e^{-t} P_t(f')`), then again to `g := deriv f`. For `IsCore f`,
`deriv f` is `C^∞` (hence `C¹`) with `‖deriv f‖, ‖deriv (deriv f)‖ ≤ M`,
so the weakened hypothesis is met. -/
theorem hasDerivAt_deriv_ouSemigroup (t : ℝ) {f : ℝ → ℝ} (hf : IsCore f) (x₀ : ℝ) :
    HasDerivAt (deriv (ouSemigroup t f))
      (Real.exp (-2 * t) * ouSemigroup t (deriv (deriv f)) x₀) x₀ := by
  obtain ⟨h_smooth, M, hM⟩ := hf
  -- Apply hasDerivAt_ouSemigroup_C1 to g := deriv f.
  have hg_C1 : ContDiff ℝ 1 (deriv f) :=
    (IsCore.contDiff_deriv ⟨h_smooth, M, hM⟩).of_le
      (by simp : ((1 : WithTop ℕ∞)) ≤ ⊤)
  have hg_bd : ∀ x, ‖deriv f x‖ ≤ M := fun x => (hM x).2.1
  have hg'_bd : ∀ x, ‖deriv (deriv f) x‖ ≤ M := fun x => (hM x).2.2
  have h_inner : HasDerivAt (ouSemigroup t (deriv f))
      (Real.exp (-t) * ouSemigroup t (deriv (deriv f)) x₀) x₀ :=
    hasDerivAt_ouSemigroup_C1 t hg_C1 hg_bd hg'_bd x₀
  -- deriv (ouSemigroup t f) = fun x => e^{-t} · ouSemigroup t (deriv f) x.
  rw [deriv_ouSemigroup_eq ⟨h_smooth, M, hM⟩]
  -- Goal: HasDerivAt (fun x => e^{-t} * P_t(f') x) (e^{-2t} * P_t(f'') x₀) x₀.
  have h := h_inner.const_mul (Real.exp (-t))
  -- h : HasDerivAt (fun x => e^{-t} * P_t(f') x) (e^{-t} * (e^{-t} * P_t(f'') x₀)) x₀.
  convert h using 1
  -- e^{-2t} * P_t(f'') x₀ = e^{-t} * (e^{-t} * P_t(f'') x₀)
  rw [show Real.exp (-2 * t) = Real.exp (-t) * Real.exp (-t) from by
    rw [show (-2 * t : ℝ) = -t + -t from by ring, Real.exp_add]]
  ring

/-- Pointwise: `deriv (deriv (ouSemigroup t f)) x = e^{-2t} · ouSemigroup t (deriv (deriv f)) x`. -/
theorem deriv_deriv_ouSemigroup_eq {f : ℝ → ℝ} (hf : IsCore f) (t : ℝ) :
    deriv (deriv (ouSemigroup t f)) = fun x =>
      Real.exp (-2 * t) * ouSemigroup t (deriv (deriv f)) x := by
  funext x; exact (hasDerivAt_deriv_ouSemigroup t hf x).deriv

/-- **The bounded parts of `IsCore` are preserved by `ouSemigroup`.** PROVED.

For `t ≥ 0` and `f` smooth-bounded as in `IsCore f` (parameterized by an
explicit `M`), `P_t f`, `(P_t f)'`, and `(P_t f)''` are all bounded by the
same `M`:
* `|P_t f x| ≤ M` (integral of bounded function on probability measure);
* `|(P_t f)' x| = |e^{-t} P_t(f') x| ≤ e^{-t} M ≤ M`;
* `|(P_t f)'' x| = |e^{-2t} P_t(f'') x| ≤ e^{-2t} M ≤ M`.

This proves the bound-related half of `ouSemigroup_preserves_IsCore`. The
`ContDiff ℝ ⊤` requirement of `IsCore` is the only remaining piece (a
smaller atomic axiom: the Mehler kernel's `C^∞` smoothing). -/
theorem ouSemigroup_preserves_bounds {f : ℝ → ℝ}
    (h_smooth : ContDiff ℝ ⊤ f) {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M ∧ ‖deriv f x‖ ≤ M ∧ ‖deriv (deriv f) x‖ ≤ M)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ x, ‖ouSemigroup t f x‖ ≤ M ∧
         ‖deriv (ouSemigroup t f) x‖ ≤ M ∧
         ‖deriv (deriv (ouSemigroup t f)) x‖ ≤ M := by
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0).1
  have hf_core : IsCore f := ⟨h_smooth, M, hM⟩
  have h_e_t_le : Real.exp (-t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have h_e_2t_le : Real.exp (-2 * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have h_e_t_nn : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have h_e_2t_nn : 0 ≤ Real.exp (-2 * t) := (Real.exp_pos _).le
  intro x
  refine ⟨?_, ?_, ?_⟩
  -- |P_t f x| ≤ M.
  · show ‖ouSemigroup t f x‖ ≤ M
    rw [Real.norm_eq_abs]
    have h_int : Integrable (fun y => f (Real.exp (-t) * x +
        Real.sqrt (1 - Real.exp (-2*t)) * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (h_smooth.continuous.measurable.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with y; exact (hM _).1
    have h_le : ∀ y, |f (Real.exp (-t) * x +
        Real.sqrt (1 - Real.exp (-2*t)) * y)| ≤ M := fun y => by
      rw [← Real.norm_eq_abs]; exact (hM _).1
    show |∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2*t)) * y) ∂γ| ≤ M
    calc |∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2*t)) * y) ∂γ|
        ≤ ∫ y, |f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2*t)) * y)| ∂γ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _, M ∂γ := by
          refine integral_mono h_int.abs (integrable_const _) ?_
          intro y; exact h_le y
      _ = M := by simp
  -- |(P_t f)' x| = |e^{-t} P_t(f') x| ≤ M.
  · rw [deriv_ouSemigroup_eq hf_core]
    show ‖Real.exp (-t) * ouSemigroup t (deriv f) x‖ ≤ M
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_e_t_nn]
    -- |P_t(f') x| ≤ M, then multiply by e^{-t} ≤ 1.
    have h_int : Integrable (fun y => deriv f (Real.exp (-t) * x +
        Real.sqrt (1 - Real.exp (-2*t)) * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · have hd_meas : Measurable (deriv f) :=
          (h_smooth.continuous_deriv (by simp)).measurable
        exact (hd_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with y; exact (hM _).2.1
    have h_pf'_le : |ouSemigroup t (deriv f) x| ≤ M := by
      show |∫ y, deriv f (Real.exp (-t) * x +
        Real.sqrt (1 - Real.exp (-2*t)) * y) ∂γ| ≤ M
      calc |∫ y, deriv f (Real.exp (-t) * x +
            Real.sqrt (1 - Real.exp (-2*t)) * y) ∂γ|
          ≤ ∫ y, |deriv f (Real.exp (-t) * x +
              Real.sqrt (1 - Real.exp (-2*t)) * y)| ∂γ := abs_integral_le_integral_abs
        _ ≤ ∫ _, M ∂γ := by
            refine integral_mono h_int.abs (integrable_const _) ?_
            intro y
            show |deriv f (Real.exp (-t) * x +
              Real.sqrt (1 - Real.exp (-2*t)) * y)| ≤ M
            rw [← Real.norm_eq_abs]; exact (hM _).2.1
        _ = M := by simp
    calc Real.exp (-t) * |ouSemigroup t (deriv f) x|
        ≤ 1 * M := mul_le_mul h_e_t_le h_pf'_le (abs_nonneg _) (by linarith)
      _ = M := one_mul _
  -- |(P_t f)'' x| = |e^{-2t} P_t(f'') x| ≤ M.
  · rw [deriv_deriv_ouSemigroup_eq hf_core]
    show ‖Real.exp (-2 * t) * ouSemigroup t (deriv (deriv f)) x‖ ≤ M
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h_e_2t_nn]
    have h_int : Integrable (fun y => deriv (deriv f) (Real.exp (-t) * x +
        Real.sqrt (1 - Real.exp (-2*t)) * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · have hd_meas : Measurable (deriv (deriv f)) := by
          have h_smooth_d : ContDiff ℝ ⊤ (deriv f) :=
            IsCore.contDiff_deriv hf_core
          exact (h_smooth_d.continuous_deriv (by simp)).measurable
        exact (hd_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with y; exact (hM _).2.2
    have h_pf''_le : |ouSemigroup t (deriv (deriv f)) x| ≤ M := by
      show |∫ y, deriv (deriv f) (Real.exp (-t) * x +
        Real.sqrt (1 - Real.exp (-2*t)) * y) ∂γ| ≤ M
      calc |∫ y, deriv (deriv f) (Real.exp (-t) * x +
            Real.sqrt (1 - Real.exp (-2*t)) * y) ∂γ|
          ≤ ∫ y, |deriv (deriv f) (Real.exp (-t) * x +
              Real.sqrt (1 - Real.exp (-2*t)) * y)| ∂γ := abs_integral_le_integral_abs
        _ ≤ ∫ _, M ∂γ := by
            refine integral_mono h_int.abs (integrable_const _) ?_
            intro y
            show |deriv (deriv f) (Real.exp (-t) * x +
              Real.sqrt (1 - Real.exp (-2*t)) * y)| ≤ M
            rw [← Real.norm_eq_abs]; exact (hM _).2.2
        _ = M := by simp
    calc Real.exp (-2 * t) * |ouSemigroup t (deriv (deriv f)) x|
        ≤ 1 * M := mul_le_mul h_e_2t_le h_pf''_le (abs_nonneg _) (by linarith)
      _ = M := one_mul _

/-- **OU semigroup preserves `IsCore` (BGL §2.7).** PROVED, modulo the
smaller atomic axiom `ouSemigroup_contDiff` (the `C^∞` smoothing).

For `t ≥ 0` and `IsCore f`, `P_t f` is `IsCore`:
* `ContDiff ⊤ (P_t f)`: from the `ouSemigroup_contDiff` axiom.
* Boundedness of `P_t f`, `(P_t f)'`, `(P_t f)''` by the same `M` as `f`:
  PROVED in `ouSemigroup_preserves_bounds` via the Mehler derivative
  formulas `(P_t f)' = e^{-t} P_t(f')` and `(P_t f)'' = e^{-2t} P_t(f'')`. -/
theorem ouSemigroup_preserves_IsCore (t : ℝ) (ht : 0 ≤ t) {f : ℝ → ℝ}
    (hf : IsCore f) : IsCore (ouSemigroup t f) := by
  obtain ⟨h_smooth, M, hM⟩ := hf
  refine ⟨ouSemigroup_contDiff t h_smooth, M, ?_⟩
  exact ouSemigroup_preserves_bounds h_smooth hM t ht

/-- **OU gradient decay (BGL Theorem 5.5.2).** PROVED (was axiom).

  ∫ ((P_t f)')² dγ ≤ e^{-2t} ∫ (f')² dγ.

Proof: by `hasDerivAt_ouSemigroup`, `(P_t f)'(x) = e^{-t} P_t(f')(x)`.
Jensen on probability measure `γ`: `(P_t f' x)² ≤ P_t((f')²) x`.
Integrating against `γ` and using γ-invariance of `P_t` (Fubini +
`ou_kernel_map`): `∫ P_t((f')²) dγ = ∫(f')² dγ`. -/
theorem ouSemigroup_gradient_decay (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : IsCore f) :
    ∫ x, deriv (ouSemigroup t f) x * deriv (ouSemigroup t f) x ∂γ ≤
      Real.exp (-2 * 1 * t) * ∫ x, deriv f x * deriv f x ∂γ := by
  set a := Real.exp (-t)
  set b := Real.sqrt (1 - Real.exp (-2 * t))
  obtain ⟨h_smooth, M, hM⟩ := hf
  have hf_core : IsCore f := ⟨h_smooth, M, hM⟩
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
  have ha_sq : a ^ 2 = Real.exp (-2 * 1 * t) := by
    show Real.exp (-t) ^ 2 = Real.exp (-2 * 1 * t)
    rw [show (-2 * 1 * t : ℝ) = -t + -t from by ring, Real.exp_add]; ring
  have hf'_meas : Measurable (deriv f) :=
    (h_smooth.continuous_deriv (by simp)).measurable
  have hf'_bd : ∀ x, ‖deriv f x‖ ≤ M := fun x => (hM x).2.1
  have hf'sq_meas : Measurable (fun y => deriv f y ^ 2) := hf'_meas.pow_const 2
  -- Mehler derivative pointwise.
  have h_deriv : ∀ x,
      deriv (ouSemigroup t f) x = a * ouSemigroup t (deriv f) x :=
    fun x => (hasDerivAt_ouSemigroup t hf_core x).deriv
  -- Pointwise Jensen.
  have h_jensen : ∀ x,
      (ouSemigroup t (deriv f) x) ^ 2 ≤
        ouSemigroup t (fun y => deriv f y ^ 2) x := by
    intro x
    show (∫ y, deriv f (a * x + b * y) ∂γ) ^ 2 ≤
         ∫ y, deriv f (a * x + b * y) ^ 2 ∂γ
    have h_conv : ConvexOn ℝ Set.univ (fun s : ℝ => s ^ 2) :=
      Even.convexOn_pow (Nat.even_iff.mpr rfl)
    have h_cont : ContinuousOn (fun s : ℝ => s ^ 2) Set.univ :=
      (continuous_pow 2).continuousOn
    have h_closed : IsClosed (Set.univ : Set ℝ) := isClosed_univ
    have h_aem : ∀ᵐ y ∂γ, deriv f (a * x + b * y) ∈ (Set.univ : Set ℝ) :=
      Filter.Eventually.of_forall (fun _ => Set.mem_univ _)
    have h_inner_int : Integrable (fun y => deriv f (a * x + b * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hf'_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id)))
          |>.aestronglyMeasurable
      · filter_upwards with y; exact hf'_bd _
    have h_inner_sq_int :
        Integrable (fun y => (deriv f (a * x + b * y)) ^ 2) γ := by
      refine Integrable.mono' (integrable_const (M^2)) ?_ ?_
      · exact ((hf'_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id))).pow_const 2)
          |>.aestronglyMeasurable
      · filter_upwards with y
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h1 : |deriv f (a*x + b*y)| ≤ M := by
          rw [← Real.norm_eq_abs]; exact hf'_bd _
        have : (deriv f (a*x + b*y)) ^ 2 = |deriv f (a*x + b*y)| ^ 2 := by
          rw [sq_abs]
        rw [this]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    exact ConvexOn.map_integral_le h_conv h_cont h_closed h_aem h_inner_int h_inner_sq_int
  -- Pointwise bound combining h_deriv + h_jensen.
  have h_ptwise : ∀ x,
      deriv (ouSemigroup t f) x * deriv (ouSemigroup t f) x ≤
        a ^ 2 * ouSemigroup t (fun y => deriv f y ^ 2) x := by
    intro x
    rw [h_deriv, ← sq]
    show (a * ouSemigroup t (deriv f) x) ^ 2 ≤
        a ^ 2 * ouSemigroup t (fun y => deriv f y ^ 2) x
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (h_jensen x) (sq_nonneg _)
  -- γ-invariance: ∫ P_t((f')²) dγ = ∫ (f')² dγ.
  have h_inv : ∫ x, ouSemigroup t (fun y => deriv f y ^ 2) x ∂γ =
      ∫ y, deriv f y ^ 2 ∂γ := by
    set φ : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
    have hφ_meas : Measurable φ := Measurable.add
      (measurable_const.mul measurable_fst) (measurable_const.mul measurable_snd)
    have hmap := ou_kernel_map t ht
    have hf'sq_φ_int : Integrable (fun p => (deriv f (φ p)) ^ 2) (γ.prod γ) := by
      refine Integrable.mono' (integrable_const (M^2))
        ((hf'sq_meas.comp hφ_meas).aestronglyMeasurable) ?_
      filter_upwards with p
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 : |deriv f (φ p)| ≤ M := by rw [← Real.norm_eq_abs]; exact hf'_bd _
      have : (deriv f (φ p)) ^ 2 = |deriv f (φ p)| ^ 2 := by rw [sq_abs]
      rw [this]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h_fubini :
        ∫ x, (∫ y, (deriv f (a*x + b*y)) ^ 2 ∂γ) ∂γ =
          ∫ p, (deriv f (φ p)) ^ 2 ∂(γ.prod γ) :=
      (integral_prod _ hf'sq_φ_int).symm
    have h_law : HasLaw φ γ (γ.prod γ) := ⟨hφ_meas.aemeasurable, hmap⟩
    have h_push : ∫ p, (deriv f (φ p)) ^ 2 ∂(γ.prod γ) =
        ∫ z, (deriv f z) ^ 2 ∂γ :=
      h_law.integral_comp hf'sq_meas.aestronglyMeasurable
    show ∫ x, (∫ y, (deriv f (a*x + b*y)) ^ 2 ∂γ) ∂γ = ∫ y, deriv f y ^ 2 ∂γ
    rw [h_fubini, h_push]
  -- Assemble: integrate the pointwise bound, then apply γ-invariance.
  calc ∫ x, deriv (ouSemigroup t f) x * deriv (ouSemigroup t f) x ∂γ
      ≤ ∫ x, a ^ 2 * ouSemigroup t (fun y => deriv f y ^ 2) x ∂γ := by
        apply integral_mono_of_nonneg
        · filter_upwards with x; exact mul_self_nonneg _
        · refine Integrable.mono' (integrable_const (a^2 * M^2)) ?_ ?_
          · have hgφ_sm : StronglyMeasurable
                (fun p : ℝ × ℝ => (deriv f (a * p.1 + b * p.2)) ^ 2) :=
              (hf'sq_meas.comp ((measurable_const.mul measurable_fst).add
                (measurable_const.mul measurable_snd))).stronglyMeasurable
            have h_sm : StronglyMeasurable
                (fun x => ouSemigroup t (fun y => deriv f y ^ 2) x) := by
              show StronglyMeasurable fun x => ∫ y, (deriv f (a*x + b*y)) ^ 2 ∂γ
              exact hgφ_sm.integral_prod_right' (ν := γ)
            exact (stronglyMeasurable_const.mul h_sm).aestronglyMeasurable
          · filter_upwards with x
            have h_inner_le : ∀ y : ℝ, (deriv f (a*x + b*y)) ^ 2 ≤ M^2 := by
              intro y
              have h1 : |deriv f (a*x + b*y)| ≤ M := by
                rw [← Real.norm_eq_abs]; exact hf'_bd _
              have : (deriv f (a*x + b*y)) ^ 2 = |deriv f (a*x + b*y)| ^ 2 := by
                rw [sq_abs]
              rw [this]
              exact pow_le_pow_left₀ (abs_nonneg _) h1 2
            have h_inner_int : Integrable
                (fun y => (deriv f (a*x + b*y)) ^ 2) γ := by
              refine Integrable.mono' (integrable_const (M^2)) ?_ ?_
              · exact ((hf'_meas.comp
                  (measurable_const.add (measurable_const.mul measurable_id))).pow_const 2)
                  |>.aestronglyMeasurable
              · filter_upwards with y
                rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
                exact h_inner_le _
            have h_bound : ouSemigroup t (fun y => deriv f y ^ 2) x ≤ M^2 := by
              show ∫ y, (deriv f (a*x + b*y)) ^ 2 ∂γ ≤ M^2
              calc ∫ y, (deriv f (a*x + b*y)) ^ 2 ∂γ
                  ≤ ∫ _, (M^2 : ℝ) ∂γ :=
                    integral_mono h_inner_int (integrable_const _) (fun y => h_inner_le _)
                _ = M^2 := by simp
            have h_nn : 0 ≤ ouSemigroup t (fun y => deriv f y ^ 2) x := by
              show 0 ≤ ∫ y, (deriv f (a*x + b*y)) ^ 2 ∂γ
              exact integral_nonneg (fun y => sq_nonneg _)
            have h_target_nn : 0 ≤ a^2 * ouSemigroup t (fun y => deriv f y ^ 2) x :=
              mul_nonneg (sq_nonneg _) h_nn
            rw [Real.norm_eq_abs, abs_of_nonneg h_target_nn]
            exact mul_le_mul_of_nonneg_left h_bound (sq_nonneg _)
        · exact Filter.Eventually.of_forall h_ptwise
    _ = a ^ 2 * ∫ x, ouSemigroup t (fun y => deriv f y ^ 2) x ∂γ := by
        rw [integral_const_mul]
    _ = a ^ 2 * ∫ y, deriv f y ^ 2 ∂γ := by rw [h_inv]
    _ = Real.exp (-2 * 1 * t) * ∫ x, deriv f x * deriv f x ∂γ := by
        rw [ha_sq]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show deriv f y ^ 2 = deriv f y * deriv f y
        ring

/-- **OU semigroup composition (Mehler kernel arithmetic, BGL §2.7.1).**

  P_{s+t} f = P_s (P_t f).

Proof sketch: writing the iterated integral, the inner Mehler kernel
with parameter `t` and the outer with parameter `s` compose to the
Mehler kernel with parameter `s+t` because `e^{-(s+t)} = e^{-s}·e^{-t}`
and `1 - e^{-2(s+t)} = e^{-2s}(1 - e^{-2t}) + (1 - e^{-2s})`. The
underlying analytic step is Gaussian convolution: `N(0, σ₁²) * N(0, σ₂²)
= N(0, σ₁² + σ₂²)`.

The `IsCore f` hypothesis ensures `f` is bounded, so all Mehler
integrals converge — without it Lean's `integral` returns `0` on
non-integrable integrands, which can desync LHS and RHS for fast-growing
`f` (see Gemini soundness review).

Reference: BGL §2.7.1 (Mehler formula, semigroup property). -/
theorem ouSemigroup_compose (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) {f : ℝ → ℝ}
    (hf : IsCore f) :
    ouSemigroup (s + t) f = ouSemigroup s (ouSemigroup t f) := by
  ext x
  obtain ⟨M, hM⟩ := hf.bounded
  have hf_meas : Measurable f := hf.measurable
  -- Notation
  set ast := Real.exp (-(s + t))
  set bst := Real.sqrt (1 - Real.exp (-2 * (s + t)))
  set as := Real.exp (-s)
  set bs := Real.sqrt (1 - Real.exp (-2 * s))
  set at_ := Real.exp (-t)
  set bt := Real.sqrt (1 - Real.exp (-2 * t))
  -- Useful nonneg facts
  have hbst_nn : 0 ≤ 1 - Real.exp (-2 * (s + t)) :=
    one_sub_exp_nonneg (s + t) (by linarith)
  have hbs_nn : 0 ≤ 1 - Real.exp (-2 * s) := one_sub_exp_nonneg s hs
  have hbt_nn : 0 ≤ 1 - Real.exp (-2 * t) := one_sub_exp_nonneg t ht
  -- exp(-(s+t)) = exp(-s) * exp(-t).
  have h_ast : ast = as * at_ := by
    show Real.exp (-(s + t)) = Real.exp (-s) * Real.exp (-t)
    rw [show -(s + t) = -s + -t from by ring, Real.exp_add]
  -- LHS = ∫ y, f(ast * x + bst * y) dγ
  -- We will show: LHS = ∫(y',y), f(ast*x + at_*bs*y' + bt*y) d(γ⊗γ)
  -- and similarly RHS = the same thing.
  -- Step 1: Define the inner kernel function.
  set Ψ : ℝ × ℝ → ℝ := fun p => at_ * bs * p.1 + bt * p.2 with hΨ_def
  have hΨ_meas : Measurable Ψ :=
    (measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)
  -- Step 2: (γ.prod γ).map Ψ = N(0, b_{s+t}²) = γ.map (fun z => b_{s+t} z).
  -- Variance of Ψ: (at_*bs)² + bt² = at_²·bs² + bt² = e^{-2t}(1-e^{-2s}) + (1-e^{-2t})
  --              = e^{-2t} - e^{-2(s+t)} + 1 - e^{-2t} = 1 - e^{-2(s+t)} = bst².
  have h_var_eq : (at_ * bs) ^ 2 + bt ^ 2 = 1 - Real.exp (-2 * (s + t)) := by
    show (Real.exp (-t) * Real.sqrt (1 - Real.exp (-2 * s))) ^ 2 +
         (Real.sqrt (1 - Real.exp (-2 * t))) ^ 2 = 1 - Real.exp (-2 * (s + t))
    rw [mul_pow, Real.sq_sqrt hbs_nn, Real.sq_sqrt hbt_nn,
      show (Real.exp (-t)) ^ 2 = Real.exp (-2 * t) by
        rw [show (-2 * t : ℝ) = -t + -t from by ring, Real.exp_add]; ring]
    -- e^{-2t}*(1-e^{-2s}) + (1-e^{-2t}) = 1 - e^{-2t}*e^{-2s} = 1 - e^{-2(s+t)}
    have h2 : Real.exp (-2 * t) * Real.exp (-2 * s) = Real.exp (-2 * (s + t)) := by
      rw [← Real.exp_add]; congr 1; ring
    linarith [h2]
  -- Step 3: build laws
  have hX : HasLaw (fun p : ℝ × ℝ => p.1) γ (γ.prod γ) :=
    ⟨measurable_fst.aemeasurable,
     by rw [Measure.map_fst_prod]; simp [measure_univ]⟩
  have hY : HasLaw (fun p : ℝ × ℝ => p.2) γ (γ.prod γ) :=
    ⟨measurable_snd.aemeasurable,
     by rw [Measure.map_snd_prod]; simp [measure_univ]⟩
  -- Laws of (at_*bs)*fst and bt*snd
  have h1 := gaussianReal_const_mul hX (at_ * bs)
  have h2 := gaussianReal_const_mul hY bt
  -- Independence
  have hindep : (fun p : ℝ × ℝ => (at_ * bs) * p.1) ⟂ᵢ[γ.prod γ]
      (fun p : ℝ × ℝ => bt * p.2) :=
    (indepFun_prod measurable_id measurable_id).comp
      (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  -- Sum has law gaussianReal 0 ((at_*bs)²·1 + bt²·1)
  have hΨ_law := gaussianReal_add_gaussianReal_of_indepFun hindep h1.map_eq h2.map_eq
  -- Convert to N(0, 1 - exp(-2(s+t)))
  have h_eq : gaussianReal ((at_ * bs) * 0 + bt * 0)
      (⟨(at_ * bs) ^ 2, sq_nonneg _⟩ * 1 + ⟨bt ^ 2, sq_nonneg _⟩ * 1) =
      gaussianReal 0 ⟨1 - Real.exp (-2 * (s + t)), hbst_nn⟩ := by
    congr 1
    · simp
    · simp only [mul_one]
      apply NNReal.eq
      simp [NNReal.coe_add, NNReal.coe_mk]
      have h_norm : (-(2 * (s + t)) : ℝ) = -2 * (s + t) := by ring
      rw [h_norm]
      exact h_var_eq
  rw [h_eq] at hΨ_law
  -- hΨ_law: (γ.prod γ).map Ψ = N(0, 1-exp(-2(s+t)))
  -- Step 4: γ.map (fun z => bst * z) = N(0, bst²) = N(0, 1-exp(-2(s+t))).
  have hZ : HasLaw (fun z : ℝ => z) γ γ := ⟨measurable_id.aemeasurable, by simp⟩
  have h_bst_law := gaussianReal_const_mul hZ bst
  -- bst² = 1 - exp(-2(s+t)) (since bst nonneg)
  have h_bst_sq : bst ^ 2 = 1 - Real.exp (-2 * (s + t)) := Real.sq_sqrt hbst_nn
  have h_bst_law' : Measure.map (fun z => bst * z) γ =
      gaussianReal 0 ⟨1 - Real.exp (-2 * (s + t)), hbst_nn⟩ := by
    have := h_bst_law.map_eq
    -- this: γ.map (fun z => bst * z) = gaussianReal (bst * 0) (⟨bst², sq_nonneg _⟩ * 1)
    rw [this]
    simp only [mul_zero, mul_one]
    congr 1
    apply NNReal.eq; simp
    have h_norm : (-(2 * (s + t)) : ℝ) = -2 * (s + t) := by ring
    rw [h_norm]
    exact h_bst_sq
  -- Step 5: Integrability
  have hf_int_basic : ∀ c d : ℝ,
      Integrable (fun y => f (c + d * y)) γ := by
    intro c d
    refine Integrable.mono' (integrable_const M) ?_ ?_
    · exact (hf_meas.comp (measurable_const.add (measurable_const.mul measurable_id'))).aestronglyMeasurable
    · filter_upwards with y; exact hM _
  have hf_int_Ψ : Integrable (fun p : ℝ × ℝ => f (ast * x + Ψ p)) (γ.prod γ) := by
    refine Integrable.mono' (integrable_const M) ?_ ?_
    · have : Measurable (fun p : ℝ × ℝ => f (ast * x + Ψ p)) :=
        hf_meas.comp (measurable_const.add hΨ_meas)
      exact this.aestronglyMeasurable
    · filter_upwards with p; exact hM _
  -- Step 6: P_s(P_t f)(x) = ∫ p, f(ast*x + Ψ p) d(γ.prod γ).
  have hRHS : ouSemigroup s (ouSemigroup t f) x =
      ∫ p, f (ast * x + Ψ p) ∂(γ.prod γ) := by
    show ∫ y', (∫ y, f (at_ * (as * x + bs * y') + bt * y) ∂γ) ∂γ =
        ∫ p, f (ast * x + Ψ p) ∂(γ.prod γ)
    -- Rewrite at_*(as*x + bs*y') + bt*y = ast*x + at_*bs*y' + bt*y = ast*x + Ψ(y', y).
    have h_eq_pt : ∀ y' y, at_ * (as * x + bs * y') + bt * y = ast * x + Ψ (y', y) := by
      intro y' y
      show at_ * (as * x + bs * y') + bt * y = ast * x + (at_ * bs * y' + bt * y)
      rw [h_ast]; ring
    simp_rw [h_eq_pt]
    -- Apply Fubini (using integrability under γ.prod γ).
    rw [integral_prod _ hf_int_Ψ]
  -- Compute Measure.map Ψ (γ.prod γ) in Ψ-form (synced from hΨ_law).
  have hΨ_law' : Measure.map Ψ (γ.prod γ) =
      gaussianReal 0 ⟨1 - Real.exp (-2 * (s + t)), hbst_nn⟩ := by
    have hΨ_eq : Ψ = (fun p : ℝ × ℝ => at_ * bs * p.1) + fun p => bt * p.2 := by
      funext p; rfl
    rw [hΨ_eq]; exact hΨ_law
  -- Step 7: ∫ f(ast*x + Ψ p) d(γ.prod γ) = ∫ f(ast*x + bst*z) dγ.
  -- Both sides are integrals of `g(w) := f(ast*x + w)` against laws that agree.
  have hcompose : ∫ p, f (ast * x + Ψ p) ∂(γ.prod γ) =
      ∫ z, f (ast * x + bst * z) ∂γ := by
    have h_lhs_via_law :
        ∫ p, f (ast * x + Ψ p) ∂(γ.prod γ) =
        ∫ w, f (ast * x + w) ∂((γ.prod γ).map Ψ) := by
      have hf_w_int : AEStronglyMeasurable (fun w => f (ast * x + w)) ((γ.prod γ).map Ψ) := by
        rw [hΨ_law']
        exact (hf_meas.comp (measurable_const.add measurable_id')).aestronglyMeasurable
      rw [integral_map hΨ_meas.aemeasurable hf_w_int]
    have h_rhs_via_law :
        ∫ z, f (ast * x + bst * z) ∂γ =
        ∫ w, f (ast * x + w) ∂(Measure.map (fun z => bst * z) γ) := by
      have h_bst_meas : Measurable (fun z : ℝ => bst * z) := measurable_const.mul measurable_id'
      have hf_w_int : AEStronglyMeasurable (fun w => f (ast * x + w))
          (Measure.map (fun z => bst * z) γ) := by
        rw [h_bst_law']
        exact (hf_meas.comp (measurable_const.add measurable_id')).aestronglyMeasurable
      rw [integral_map h_bst_meas.aemeasurable hf_w_int]
    rw [h_lhs_via_law, h_rhs_via_law, hΨ_law', h_bst_law']
  -- Step 8: Connect LHS to ∫f(ast*x + bst*z) dγ.
  show ouSemigroup (s + t) f x = ouSemigroup s (ouSemigroup t f) x
  rw [hRHS, hcompose]
  rfl

/-- **L² derivative formula (BGL Proposition 4.7.1).**

  d/dt ∫ (P_t f)² dγ = -2 E(P_t f, P_t f) = -2 ∫ (P_t f)'² dγ.

Proof sketch: integration by parts (the OU generator is
`Lf = f'' - x·f'`, self-adjoint on `L²(γ)`), giving
`d/dt P_t f = L(P_t f)` and hence `d/dt ‖P_t f‖²₂ = 2⟨P_t f, L P_t f⟩
= -2 E(P_t f)`. The differentiation under the integral against the
Gaussian density is standard but Mathlib does not yet have it at the
required generality.

Reference: BGL Proposition 4.7.1 (entropy/L² derivative formulas). -/
axiom ouSemigroup_l2_sq_hasDerivWithinAt (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : IsCore f) :
    HasDerivWithinAt
      (fun s => ∫ x, (ouSemigroup s f x) ^ 2 ∂γ)
      (-2 * ∫ x, ouGamma (ouSemigroup t f) (ouSemigroup t f) x ∂γ)
      (Ici 0) t

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
    exact ouSemigroup_l2_sq_hasDerivWithinAt f s hs hf
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

/-- **L² ergodicity of the OU semigroup — DERIVED via Mehler DCT.**

  ∫ (P_t f)² dγ - (∫ f dγ)² → 0 as t → ∞.

Proof: as `t → ∞`, `e^{-t} → 0` and `b_t = √(1-e^{-2t}) → 1`, so
`P_t f(x) = ∫ f(e^{-t}x + b_t y) dγ(y) → ∫ f(y) dγ(y) = ∫f` for each
`x` by dominated convergence (integrand bounded by `M`, pointwise limit
`f(y)` by continuity). Squaring and applying DCT a second time
(integrand `(P_t f x)² ≤ M²`, pointwise limit `(∫f)²`) gives
`∫(P_t f)² dγ → (∫f)²`. Subtracting `(∫f)²` yields the claim.

This was previously a textbook axiom; it is now proved using `IsCore`
boundedness and `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`.

Reference: BGL Proposition 4.2.1; the OU spectral gap is 1. -/
theorem ouSemigroup_ergodic (f : ℝ → ℝ) (hf : IsCore f) :
    Tendsto
      (fun t => ∫ x, (ouSemigroup t f x) ^ 2 ∂γ - (∫ x, f x ∂γ) ^ 2)
      atTop (nhds 0) := by
  obtain ⟨M, hM⟩ := hf.bounded
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
  have hf_cont : Continuous f := hf.continuous
  have hf_meas : Measurable f := hf.measurable
  -- The pointwise limit ∫f.
  set Ef : ℝ := ∫ y, f y ∂γ with hEf_def
  -- Step 1: `e^{-t} → 0`.
  have h_exp_neg_atTop : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot)
  -- Step 2: `e^{-2t} → 0`.
  have h_exp_neg2_atTop : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (nhds 0) := by
    have h_neg2t : Tendsto (fun t : ℝ => -2 * t) atTop atBot := by
      refine Filter.tendsto_atBot.mpr fun B => ?_
      rw [Filter.eventually_atTop]
      refine ⟨max 1 ((1 - B) / 2), fun t ht => ?_⟩
      have h1 : (1 - B) / 2 ≤ t := (le_max_right _ _).trans ht
      linarith
    exact Real.tendsto_exp_atBot.comp h_neg2t
  -- Step 3: `b_t → 1`.
  have h_b_atTop : Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t))) atTop (nhds 1) := by
    have h_inner : Tendsto (fun t : ℝ => 1 - Real.exp (-2 * t)) atTop (nhds 1) := by
      simpa using Filter.Tendsto.const_sub 1 h_exp_neg2_atTop
    have := h_inner.sqrt
    simpa using this
  -- Step 4: For each x, P_t f(x) → ∫f as t → ∞ (inner DCT).
  have h_ptwise : ∀ x, Tendsto (fun t => ouSemigroup t f x) atTop (nhds Ef) := by
    intro x
    show Tendsto
      (fun t => ∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ)
      atTop (nhds (∫ y, f y ∂γ))
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M) ?_ ?_ (integrable_const M) ?_
    · -- AEStronglyMeasurable
      filter_upwards with t
      have hmeas : Measurable
          (fun y => f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)) :=
        hf_meas.comp (measurable_const.add (measurable_const.mul measurable_id'))
      exact hmeas.aestronglyMeasurable
    · -- bound: ‖f(...)‖ ≤ M
      filter_upwards with t
      filter_upwards with y
      exact hM _
    · -- pointwise limit at each y: f(e^{-t}x + b_t y) → f(y)
      filter_upwards with y
      have h_arg : Tendsto
          (fun t : ℝ => Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
          atTop (nhds y) := by
        have h1 : Tendsto (fun t : ℝ => Real.exp (-t) * x) atTop (nhds 0) := by
          simpa using h_exp_neg_atTop.mul_const x
        have h2 : Tendsto
            (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t)) * y) atTop (nhds y) := by
          simpa using h_b_atTop.mul_const y
        have := h1.add h2
        simpa using this
      exact (hf_cont.tendsto y).comp h_arg
  -- Step 5: For each x, |P_t f(x)| ≤ M.
  have h_bound : ∀ x t, |ouSemigroup t f x| ≤ M := by
    intro x t
    show |∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ| ≤ M
    have hint : Integrable
        (fun y => f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hf_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id'))).aestronglyMeasurable
      · filter_upwards with y; exact hM _
    calc |_| ≤ ∫ y, |f _| ∂γ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _y, M ∂γ := by
          refine integral_mono hint.abs (integrable_const M) ?_
          intro y
          show |f _| ≤ M
          have := hM (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
          rwa [Real.norm_eq_abs] at this
      _ = M := by simp
  -- Step 6: ∫(P_t f)² dγ → ∫(Ef)² dγ = Ef² as t → ∞ (outer DCT).
  have h_outer :
      Tendsto (fun t => ∫ x, (ouSemigroup t f x) ^ 2 ∂γ) atTop (nhds (Ef ^ 2)) := by
    have h_target : Ef ^ 2 = ∫ _x, Ef ^ 2 ∂γ := by simp
    rw [h_target]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M ^ 2) ?_ ?_ (integrable_const _) ?_
    · -- AEStronglyMeasurable: t ↦ (P_t f)² is strongly measurable.
      filter_upwards with t
      have hjoint_meas : Measurable (fun p : ℝ × ℝ =>
          f (Real.exp (-t) * p.1 + Real.sqrt (1 - Real.exp (-2 * t)) * p.2)) :=
        hf_meas.comp ((measurable_const.mul measurable_fst).add
          (measurable_const.mul measurable_snd))
      have hjoint_sm : MeasureTheory.StronglyMeasurable
          (fun p : ℝ × ℝ =>
            f (Real.exp (-t) * p.1 + Real.sqrt (1 - Real.exp (-2 * t)) * p.2)) :=
        hjoint_meas.stronglyMeasurable
      have hPtf_sm : MeasureTheory.StronglyMeasurable (ouSemigroup t f) :=
        hjoint_sm.integral_prod_right'
      exact (hPtf_sm.pow 2).aestronglyMeasurable
    · -- bound: ‖(P_t f x)²‖ ≤ M²
      filter_upwards with t
      filter_upwards with x
      have habs : |ouSemigroup t f x| ≤ M := h_bound x t
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have : |ouSemigroup t f x| ^ 2 ≤ M ^ 2 := by
        nlinarith [abs_nonneg (ouSemigroup t f x)]
      rwa [sq_abs] at this
    · -- pointwise: (P_t f x)² → Ef²
      filter_upwards with x
      exact (h_ptwise x).pow 2
  -- Step 7: Subtract Ef² to get the ergodic statement.
  have := h_outer.sub_const (Ef ^ 2)
  simpa using this

/-- **Entropy decay for `f²` under OU (BGL Theorem 5.5.2).**

  Ent_γ(f²) − Ent_γ(P_t(f²)) ≤ (1 − e^{-2t}) · 2 · E(f, f).

Proof sketch: by the Leibniz rule for `Γ` (the diffusion property),
`I(f²) = 4 E(f, f)` (Fisher information of `f²` in terms of energy of
`f`). The de Bruijn identity gives `d/dt Ent(P_t g) = -I(P_t g)`, and
gradient decay `I(P_t g) ≤ e^{-2t} I(g)` integrates from 0 to t to
yield the claim with `g = f²`.

Reference: BGL §5.5, proof of Theorem 5.5.2 (LSI from Bakry–Émery). -/
axiom ouSemigroup_entropy_sq_decay_bound (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : IsCore f) :
    DirichletSpace.entropy (ds := dirichletSpace) (fun x => f x * f x) -
    DirichletSpace.entropy (ds := dirichletSpace)
      (ouSemigroup t (fun x => f x * f x)) ≤
      (1 - Real.exp (-2 * 1 * t)) * (2 / 1) * ouEnergy f f

/-- **Entropy ergodicity of the OU semigroup — DERIVED via Mehler DCT + `s log s` continuity.**

  Ent_γ(P_t(f²)) → 0 as t → ∞.

Proof: f² is bounded by `M²` (from `IsCore`). The Mehler-DCT inner
argument gives `P_t(f²)(x) → ∫f² dγ` for each `x` (integrand bounded
by `M²`, pointwise limit `f²(y)` by continuity). Using the explicit
entropy formula
`Ent(h) = ∫ h·log h dγ - (∫h)·log(∫h)` and mean preservation
`∫P_t(f²) = ∫f²` (computed via `ou_kernel_map`), the second term is
constant in `t` and equals `(∫f²)·log(∫f²)`. The outer DCT applied to
`s · log s` (continuous on `[0, ∞)` per `Real.continuous_mul_log`,
bounded on `[0, M²]` by compactness) gives
`∫(P_t f²)·log(P_t f²) dγ → (∫f²)·log(∫f²)`. The two contributions
cancel.

This was previously a textbook axiom; it is now reduced to the
atomic five plus `Real.continuous_mul_log`.

Reference: BGL Proposition 5.2.1 (entropy decay, ergodic limit). -/
theorem ouSemigroup_entropy_sq_ergodic (f : ℝ → ℝ) (hf : IsCore f) :
    Tendsto
      (fun t => DirichletSpace.entropy (ds := dirichletSpace)
        (ouSemigroup t (fun x => f x * f x)))
      atTop (nhds 0) := by
  obtain ⟨M, hM⟩ := hf.bounded
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
  have hf_cont : Continuous f := hf.continuous
  have hf_meas : Measurable f := hf.measurable
  -- f² bounded by M², continuous.
  set g : ℝ → ℝ := fun x => f x * f x with hg_def
  have hg_cont : Continuous g := hf_cont.mul hf_cont
  have hg_meas : Measurable g := hg_cont.measurable
  have hg_nn : ∀ x, 0 ≤ g x := fun x => mul_self_nonneg _
  have hg_bdd : ∀ x, g x ≤ M ^ 2 := by
    intro x
    have h1 : |f x| ≤ M := by rw [← Real.norm_eq_abs]; exact hM x
    have h2 : (f x) ^ 2 ≤ M ^ 2 := by
      have : |f x| ^ 2 ≤ M ^ 2 := by nlinarith [abs_nonneg (f x)]
      rwa [sq_abs] at this
    show f x * f x ≤ M ^ 2
    have : f x * f x = (f x) ^ 2 := by ring
    linarith
  -- Pointwise convergence: P_t g(x) → ∫g for each x.
  set Eg : ℝ := ∫ y, g y ∂γ with hEg_def
  have h_ptwise : ∀ x, Tendsto (fun t => ouSemigroup t g x) atTop (nhds Eg) := by
    intro x
    show Tendsto
      (fun t => ∫ y, g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ)
      atTop (nhds (∫ y, g y ∂γ))
    -- Same DCT pattern as in `ouSemigroup_ergodic`.
    have h_exp_neg_atTop : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot)
    have h_neg2t : Tendsto (fun t : ℝ => -2 * t) atTop atBot := by
      refine Filter.tendsto_atBot.mpr fun B => ?_
      rw [Filter.eventually_atTop]
      refine ⟨max 1 ((1 - B) / 2), fun t ht => ?_⟩
      have h1 : (1 - B) / 2 ≤ t := (le_max_right _ _).trans ht
      linarith
    have h_exp_neg2_atTop : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h_neg2t
    have h_b_atTop : Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t))) atTop (nhds 1) := by
      have h_inner : Tendsto (fun t : ℝ => 1 - Real.exp (-2 * t)) atTop (nhds 1) := by
        simpa using Filter.Tendsto.const_sub 1 h_exp_neg2_atTop
      simpa using h_inner.sqrt
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M ^ 2) ?_ ?_ (integrable_const _) ?_
    · filter_upwards with t
      have : Measurable (fun y => g (Real.exp (-t) * x +
          Real.sqrt (1 - Real.exp (-2 * t)) * y)) :=
        hg_meas.comp (measurable_const.add (measurable_const.mul measurable_id'))
      exact this.aestronglyMeasurable
    · filter_upwards with t
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn _)]
      exact hg_bdd _
    · filter_upwards with y
      have h_arg : Tendsto
          (fun t : ℝ => Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y)
          atTop (nhds y) := by
        have h1 : Tendsto (fun t : ℝ => Real.exp (-t) * x) atTop (nhds 0) := by
          simpa using h_exp_neg_atTop.mul_const x
        have h2 : Tendsto
            (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t)) * y) atTop (nhds y) := by
          simpa using h_b_atTop.mul_const y
        simpa using h1.add h2
      exact (hg_cont.tendsto y).comp h_arg
  -- Bound for P_t g(x) on [0, M²].
  have h_Ptg_bdd : ∀ x t, 0 ≤ ouSemigroup t g x ∧ ouSemigroup t g x ≤ M ^ 2 := by
    intro x t
    have hint : Integrable (fun y => g (Real.exp (-t) * x +
        Real.sqrt (1 - Real.exp (-2 * t)) * y)) γ := by
      refine Integrable.mono' (integrable_const (M ^ 2)) ?_ ?_
      · exact (hg_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id'))).aestronglyMeasurable
      · filter_upwards with y
        rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn _)]; exact hg_bdd _
    refine ⟨?_, ?_⟩
    · show 0 ≤ ∫ y, g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ
      exact integral_nonneg (fun y => hg_nn _)
    · show ∫ y, g (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ ≤ M ^ 2
      calc ∫ y, _ ∂γ
          ≤ ∫ _y, M ^ 2 ∂γ :=
            integral_mono hint (integrable_const _) (fun y => hg_bdd _)
        _ = M ^ 2 := by simp
  -- Bound for h log h on [0, M²]: by compactness.
  have hM2_nn : (0:ℝ) ≤ M ^ 2 := sq_nonneg M
  obtain ⟨B, hB⟩ : ∃ B, ∀ s ∈ Set.Icc (0:ℝ) (M ^ 2), |s * Real.log s| ≤ B := by
    have h_compact : IsCompact (Set.Icc (0:ℝ) (M ^ 2)) := isCompact_Icc
    have h_cont_abs : Continuous (fun s => |s * Real.log s|) :=
      Real.continuous_mul_log.abs
    have h_im_compact : IsCompact ((fun s => |s * Real.log s|) '' Set.Icc 0 (M ^ 2)) :=
      h_compact.image h_cont_abs
    obtain ⟨B, hB⟩ := h_im_compact.bddAbove
    refine ⟨B, fun s hs => ?_⟩
    exact hB ⟨s, hs, rfl⟩
  -- Outer DCT: ∫(P_t g)(x) · log((P_t g)(x)) dγ → Eg · log Eg.
  have h_outer_log :
      Tendsto (fun t => ∫ x, ouSemigroup t g x * Real.log (ouSemigroup t g x) ∂γ)
        atTop (nhds (Eg * Real.log Eg)) := by
    have h_target :
        Eg * Real.log Eg = ∫ _x, Eg * Real.log Eg ∂γ := by simp
    rw [h_target]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => B) ?_ ?_ (integrable_const _) ?_
    · -- AEStronglyMeasurable: x ↦ (P_t g x) · log(P_t g x).
      filter_upwards with t
      have hjoint_meas : Measurable
          (fun p : ℝ × ℝ => g (Real.exp (-t) * p.1 +
            Real.sqrt (1 - Real.exp (-2 * t)) * p.2)) :=
        hg_meas.comp ((measurable_const.mul measurable_fst).add
          (measurable_const.mul measurable_snd))
      have hPtg_sm : MeasureTheory.StronglyMeasurable (ouSemigroup t g) :=
        hjoint_meas.stronglyMeasurable.integral_prod_right'
      have h_log_meas : Measurable (fun x => Real.log (ouSemigroup t g x)) :=
        Real.measurable_log.comp hPtg_sm.measurable
      have h_meas : Measurable (fun x => ouSemigroup t g x * Real.log (ouSemigroup t g x)) :=
        hPtg_sm.measurable.mul h_log_meas
      exact h_meas.aestronglyMeasurable
    · -- bound: ‖(P_t g x) · log(P_t g x)‖ ≤ B
      filter_upwards with t
      filter_upwards with x
      rw [Real.norm_eq_abs]
      apply hB
      exact ⟨(h_Ptg_bdd x t).1, (h_Ptg_bdd x t).2⟩
    · -- pointwise: (P_t g x) · log(P_t g x) → Eg · log Eg.
      filter_upwards with x
      have h := (h_ptwise x)
      have h_cont_pt : ContinuousAt (fun s => s * Real.log s) Eg :=
        Real.continuous_mul_log.continuousAt
      exact h_cont_pt.tendsto.comp h
  -- Mean preservation: ∫ P_t g dγ = ∫ g dγ.
  have h_mean : ∀ t, 0 ≤ t → ∫ x, ouSemigroup t g x ∂γ = ∫ x, g x ∂γ := by
    intro t ht
    -- Use `ou_kernel_map` and Fubini, mirroring the `semigroup_mean` field proof.
    set a := Real.exp (-t)
    set b := Real.sqrt (1 - Real.exp (-2 * t))
    set φ : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
    have hφ : Measurable φ := Measurable.add
      (measurable_const.mul measurable_fst) (measurable_const.mul measurable_snd)
    have hmap := ou_kernel_map t ht
    have hg_int : Integrable g γ := by
      refine Integrable.mono' (integrable_const (M ^ 2))
        hg_meas.aestronglyMeasurable ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn _)]
      exact hg_bdd _
    have hgφ_int : Integrable (g ∘ φ) (γ.prod γ) := by
      have hasm' : AEStronglyMeasurable g ((γ.prod γ).map φ) := by
        rw [hmap]; exact hg_meas.aestronglyMeasurable
      have hint' : Integrable g ((γ.prod γ).map φ) := by rw [hmap]; exact hg_int
      exact (integrable_map_measure hasm' hφ.aemeasurable).mp hint'
    show ∫ x, ouSemigroup t g x ∂γ = ∫ x, g x ∂γ
    simp only [ouSemigroup]
    rw [show (∫ x, (∫ y, g (a * x + b * y) ∂γ) ∂γ) = ∫ p, g (φ p) ∂(γ.prod γ) from
      (integral_prod (g ∘ φ) hgφ_int).symm]
    have hlaw : HasLaw φ γ (γ.prod γ) := ⟨hφ.aemeasurable, hmap⟩
    exact hlaw.integral_comp hg_meas.aestronglyMeasurable
  -- Combine: entropy = ∫ h·log h dγ - (∫h)·log(∫h).
  -- For h = P_t g, ∫h = Eg, so log(∫h) = log Eg, second term = Eg · log Eg.
  -- ∫ h·log h dγ → Eg · log Eg, so entropy → 0.
  have h_entropy_eq : ∀ t, 0 ≤ t →
      DirichletSpace.entropy (ds := dirichletSpace) (ouSemigroup t g) =
        (∫ x, ouSemigroup t g x * Real.log (ouSemigroup t g x) ∂γ) - Eg * Real.log Eg := by
    intro t ht
    show (∫ x, ouSemigroup t g x * Real.log (ouSemigroup t g x) ∂γ) -
        (∫ x, ouSemigroup t g x ∂γ) * Real.log (∫ x, ouSemigroup t g x ∂γ) =
        (∫ x, ouSemigroup t g x * Real.log (ouSemigroup t g x) ∂γ) - Eg * Real.log Eg
    rw [h_mean t ht]
  -- Massage the goal: rewrite entropy as the difference, then the difference → 0.
  have h_diff : Tendsto
      (fun t => (∫ x, ouSemigroup t g x * Real.log (ouSemigroup t g x) ∂γ) -
        Eg * Real.log Eg) atTop (nhds 0) := by
    have := h_outer_log.sub_const (Eg * Real.log Eg)
    simpa using this
  -- The function `t ↦ entropy(P_t g)` agrees with the difference for t ≥ 0.
  -- atTop is eventually ≥ 0, so the limits agree.
  have h_eq_eventually : (fun t => DirichletSpace.entropy (ds := dirichletSpace)
      (ouSemigroup t g)) =ᶠ[atTop]
      (fun t => (∫ x, ouSemigroup t g x * Real.log (ouSemigroup t g x) ∂γ) -
        Eg * Real.log Eg) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact h_entropy_eq t ht
  exact (Tendsto.congr' h_eq_eventually.symm h_diff)

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
    have h := ouSemigroup_l2_sq_hasDerivWithinAt f t ht hf
    simpa [ouGamma] using h
  semigroup_ergodic := fun f hf => ouSemigroup_ergodic f hf
  semigroup_entropy_sq_decay_bound := fun f t ht hf =>
    ouSemigroup_entropy_sq_decay_bound f t ht hf
  semigroup_entropy_sq_ergodic := fun f hf => ouSemigroup_entropy_sq_ergodic f hf

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

end Gaussian1D

end
