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

/-- **`IsCore` is preserved by the OU semigroup (BGL §2.7).**

The Mehler integral `P_t f(x) = ∫ f(e^{-t}x + √(1-e^{-2t})y) dγ(y)`
preserves smoothness (differentiation under the integral) and bounded
derivatives (the integral of a bounded family is bounded with the same
bound, and `(P_t f)'(x) = e^{-t} P_t(f')(x)`).

Reference: BGL §2.7.1 (OU semigroup smoothing); standard differentiation
under the integral against the Gaussian density. -/
axiom ouSemigroup_preserves_IsCore (t : ℝ) (ht : 0 ≤ t) {f : ℝ → ℝ}
    (hf : IsCore f) : IsCore (ouSemigroup t f)

/-- **OU gradient decay (BGL Theorem 5.5.2).**

  ∫ ((P_t f)')² dγ ≤ e^{-2t} ∫ (f')² dγ.

Proof sketch: by Mehler's formula and differentiation under the integral,
`(P_t f)'(x) = e^{-t} ∫ f'(e^{-t}x + √(1-e^{-2t})y) dγ(y) = e^{-t} P_t(f')(x)`.
Then Jensen's inequality on the convex function `s ↦ s²` gives
`(P_t f)'(x)² ≤ e^{-2t} P_t((f')²)(x)`, and integrating over `γ` together
with `P_t`-invariance of `γ` yields the claim.

Reference: BGL Theorem 5.5.2; equivalent to Bakry–Émery curvature `ρ = 1`
of the standard Gaussian. -/
axiom ouSemigroup_gradient_decay (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : IsCore f) :
    ∫ x, deriv (ouSemigroup t f) x * deriv (ouSemigroup t f) x ∂γ ≤
      Real.exp (-2 * 1 * t) * ∫ x, deriv f x * deriv f x ∂γ

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

end Gaussian1D

end
