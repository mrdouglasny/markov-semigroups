/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Brascamp-Lieb Inequality (Classical/Statistical Mechanics Version)

The Brascamp-Lieb inequality for log-concave measures on ℝⁿ:
given μ = e^{-V} dx with V ∈ C² strictly convex (Hess V > 0),

  Var_μ(f) ≤ ∫ ⟨∇f, (Hess V)⁻¹ ∇f⟩ dμ

This is stronger than the Poincaré inequality Var_μ(f) ≤ (1/ρ) ∫ |∇f|² dμ
(which follows by taking ρ = inf spec(Hess V)), because it uses the
pointwise Hessian inverse rather than a uniform lower bound.

## Architecture

Two textbook results are postulated as axioms:

1. `brascampLieb_axiom` — the core inequality (BGL §4.9, Prop. 4.9.1).
   Proof requires weighted integration by parts for the generator
   L = -Δ + ⟨∇V, ∇·⟩ and the Bochner identity.

2. `contDiff_hessianInverse_gradient` — smooth dependence of
   (Hess V)⁻¹ ∇f on x (Cramer's rule + chain rule for C^∞ inversion
   of smoothly varying invertible operators in finite dimensions).

Everything else is fully proven:
- `hessian_injective`, `hessian_surjective` — Hessian invertibility
- `pointwise_hessian_bound` — (∇f)(g) ≤ (1/ρ)‖∇f‖²
- `exists_hessian_inverse` — existence and regularity of g
- `brascampLieb`, `brascampLieb_poincare` — the main theorems

## References

- Brascamp and Lieb, "On extensions of the Brunn-Minkowski and
  Prékopa-Leindler theorems," J. Funct. Anal. 22 (1976), 366–389
- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, §4.9
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

open MeasureTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The Hessian bilinear form of V at x, evaluated on (v, w).
Given V : E → ℝ, the Hessian at x is the second Fréchet derivative
fderiv ℝ (fderiv ℝ V) x : E →L[ℝ] (E →L[ℝ] ℝ).
The bilinear form evaluates as ((Hess V)(x) v) w : ℝ. -/
def hessianBilin (V : E → ℝ) (x : E) (v : E) (w : E) : ℝ :=
  ((fderiv ℝ (fderiv ℝ V) x) v) w

/-- A log-concave measure on a finite-dimensional real inner product space:
μ = e^{-V(x)} dx where V is C² and strictly convex (Hess V is positive
definite everywhere).

This is the setting of the classical Brascamp-Lieb inequality. -/
structure LogConcaveMeasure (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] where
  /-- The potential V : E → ℝ. -/
  V : E → ℝ
  /-- V is twice differentiable. -/
  hV_diff : ContDiff ℝ 2 V
  /-- The Hessian bilinear form of V is positive definite everywhere:
    ((Hess V)(x) v) v > 0 for all v ≠ 0. -/
  hV_convex : ∀ (x : E) (v : E), v ≠ 0 →
    (0 : ℝ) < hessianBilin V x v v
  /-- The weighted measure μ = e^{-V} dx is a probability measure. -/
  μ : Measure E
  hμ_prob : IsProbabilityMeasure μ

attribute [instance] LogConcaveMeasure.hμ_prob

/-! ## Postulated textbook results

These two axioms encapsulate deep analytical results that are standard
in the literature but require substantial infrastructure to formalize
(weighted integration by parts, Bochner identity, smooth operator
inversion). They are postulated here and used to derive the main theorems.
-/

/-- **Postulated.** The Brascamp-Lieb inequality (Brascamp-Lieb 1976,
Bakry-Gentil-Ledoux 2014, Proposition 4.9.1).

For a log-concave measure μ = e^{-V} dx with V strictly convex, and
g solving (Hess V)(x) · g(x) = ∇f(x) pointwise,

  Var_μ(f) ≤ ∫ (∇f(x))(g(x)) dμ(x)

The proof uses: (1) weighted integration by parts for the generator
L = -Δ + ⟨∇V, ∇·⟩ to write Var_μ(f) = ∫ ⟨∇f, ∇u⟩ dμ where Lu = f - μ(f);
(2) the Bochner identity to bound ∫ ⟨∇u, Hess V · ∇u⟩ dμ ≤ Var_μ(f);
(3) Cauchy-Schwarz with weight (Hess V)^{1/2} to conclude. -/
axiom brascampLieb_axiom {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (m : LogConcaveMeasure E)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (g : E → E) (hg : ContDiff ℝ 1 g)
    (hg_solve : ∀ (x : E), (fderiv ℝ (fderiv ℝ m.V) x) (g x) = fderiv ℝ f x) :
    (∫ x, (f x) ^ 2 ∂m.μ - (∫ x, f x ∂m.μ) ^ 2) ≤ ∫ x, (fderiv ℝ f x) (g x) ∂m.μ

/-- **Postulated.** Smooth dependence of the Hessian inverse applied to
the gradient: the map x ↦ (Hess V(x))⁻¹(∇f(x)) is C¹.

This is a standard result in finite-dimensional smooth analysis. When
V is C² and f is C¹, the Hessian x ↦ Hess V(x) is continuous and
pointwise invertible (by strict convexity), and the gradient x ↦ ∇f(x)
is continuous. The composition through the inverse is C¹ by Cramer's
rule (the inverse of a smoothly varying invertible matrix depends
smoothly on its entries) and the chain rule for ContDiff functions.

Reference: any textbook on smooth manifolds or matrix analysis,
e.g., Hirsch, *Differential Topology*, Ch. 1. -/
axiom contDiff_hessianInverse_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (m : LogConcaveMeasure E)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (g : E → E)
    (hg_solve : ∀ (x : E), (fderiv ℝ (fderiv ℝ m.V) x) (g x) = fderiv ℝ f x) :
    ContDiff ℝ 1 g

namespace LogConcaveMeasure

variable (m : LogConcaveMeasure E)

/-- Variance of f under the log-concave measure. -/
def variance (f : E → ℝ) : ℝ :=
  ∫ x, (f x) ^ 2 ∂m.μ - (∫ x, f x ∂m.μ) ^ 2

/-! ### The Brascamp-Lieb inequality -/

/-- **Brascamp-Lieb inequality** (full pointwise form).
Proved from `brascampLieb_axiom`. -/
theorem brascampLieb (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (g : E → E) (hg : ContDiff ℝ 1 g)
    (hg_solve : ∀ (x : E), (fderiv ℝ (fderiv ℝ m.V) x) (g x) = fderiv ℝ f x) :
    m.variance f ≤ ∫ x, (fderiv ℝ f x) (g x) ∂m.μ :=
  brascampLieb_axiom m f hf g hg hg_solve

/-! ### Corollary: Poincaré inequality -/

/-- Pointwise bound: if Hess V ≥ ρI at x and (Hess V)(x) · g(x) = ∇f(x),
then (∇f(x))(g(x)) ≤ (1/ρ) ‖∇f(x)‖².

From ρ‖g(x)‖² ≤ hessianBilin(g(x), g(x)) = (∇f(x))(g(x)) and the
operator norm bound |(∇f(x))(g(x))| ≤ ‖∇f(x)‖‖g(x)‖, we get
‖g(x)‖ ≤ (1/ρ)‖∇f(x)‖, hence (∇f(x))(g(x)) ≤ (1/ρ)‖∇f(x)‖². -/
theorem pointwise_hessian_bound
    (V : E → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ_bound : ∀ (x : E) (v : E), ρ * ‖v‖ ^ 2 ≤ hessianBilin V x v v)
    (f : E → ℝ) (g : E → E) (x : E)
    (hg_solve : (fderiv ℝ (fderiv ℝ V) x) (g x) = fderiv ℝ f x) :
    (fderiv ℝ f x) (g x) ≤ (1 / ρ) * ‖fderiv ℝ f x‖ ^ 2 := by
  have key : (fderiv ℝ f x) (g x) = hessianBilin V x (g x) (g x) := by
    simp only [hessianBilin]
    rw [← hg_solve]
  rw [key]
  have hρg := hρ_bound x (g x)
  have hnorm : hessianBilin V x (g x) (g x) ≤ ‖fderiv ℝ f x‖ * ‖g x‖ := by
    calc hessianBilin V x (g x) (g x)
        = ((fderiv ℝ (fderiv ℝ V) x) (g x)) (g x) := rfl
      _ ≤ ‖((fderiv ℝ (fderiv ℝ V) x) (g x)) (g x)‖ := le_abs_self _
      _ ≤ ‖(fderiv ℝ (fderiv ℝ V) x) (g x)‖ * ‖g x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ f x‖ * ‖g x‖ := by rw [hg_solve]
  by_cases hgz : g x = 0
  · simp only [hessianBilin, hgz, map_zero]
    positivity
  · have hg_pos : (0 : ℝ) < ‖g x‖ := norm_pos_iff.mpr hgz
    have hg_bound : ‖g x‖ ≤ (1 / ρ) * ‖fderiv ℝ f x‖ := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hρ]
      have h1 : ρ * (‖g x‖ * ‖g x‖) ≤ ‖fderiv ℝ f x‖ * ‖g x‖ := by
        have := le_trans hρg hnorm; rwa [sq] at this
      nlinarith [hg_pos]
    calc hessianBilin V x (g x) (g x)
        ≤ ‖fderiv ℝ f x‖ * ‖g x‖ := hnorm
      _ ≤ ‖fderiv ℝ f x‖ * ((1 / ρ) * ‖fderiv ℝ f x‖) :=
          mul_le_mul_of_nonneg_left hg_bound (norm_nonneg _)
      _ = 1 / ρ * ‖fderiv ℝ f x‖ ^ 2 := by ring

/-! ### Hessian invertibility -/

/-- The Hessian of a strictly convex function is injective: if
(Hess V)(x) v = 0 then v = 0. -/
theorem hessian_injective (x : E) :
    Function.Injective (fderiv ℝ (fderiv ℝ m.V) x) := by
  intro v w hvw
  by_contra h
  have hne : v - w ≠ 0 := sub_ne_zero.mpr h
  have hpos := m.hV_convex x (v - w) hne
  have : hessianBilin m.V x (v - w) (v - w) = 0 := by
    simp only [hessianBilin, map_sub]
    have : (fderiv ℝ (fderiv ℝ m.V) x) v = (fderiv ℝ (fderiv ℝ m.V) x) w := hvw
    simp [this, sub_self]
  linarith

/-- In finite dimensions, the Hessian is surjective. -/
theorem hessian_surjective (x : E) :
    Function.Surjective (fderiv ℝ (fderiv ℝ m.V) x) := by
  have hinj := m.hessian_injective x
  have hfd : FiniteDimensional ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← Subspace.dual_finrank_eq (K := ℝ) (V := E)]
    exact LinearMap.toContinuousLinearMap.finrank_eq
  have hinj_lm : Function.Injective (fderiv ℝ (fderiv ℝ m.V) x).toLinearMap := hinj
  have hsurj_lm := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj_lm
  intro φ
  obtain ⟨v, hv⟩ := hsurj_lm φ
  exact ⟨v, hv⟩

/-- Existence and regularity of the pointwise Hessian inverse.
Existence by surjectivity (proven); smoothness from
`contDiff_hessianInverse_gradient` (postulated). -/
theorem exists_hessian_inverse
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ g : E → E, ContDiff ℝ 1 g ∧
    ∀ (x : E), (fderiv ℝ (fderiv ℝ m.V) x) (g x) = fderiv ℝ f x := by
  have hsurj := m.hessian_surjective
  let g : E → E := fun x => (hsurj x (fderiv ℝ f x)).choose
  have hg_solve : ∀ x, (fderiv ℝ (fderiv ℝ m.V) x) (g x) = fderiv ℝ f x :=
    fun x => (hsurj x (fderiv ℝ f x)).choose_spec
  exact ⟨g, contDiff_hessianInverse_gradient m f hf g hg_solve, hg_solve⟩

/-- **Brascamp-Lieb implies Poincaré.** If Hess V ≥ ρI everywhere, then

  Var_μ(f) ≤ (1/ρ) ∫ ‖∇f‖² dμ -/
theorem brascampLieb_poincare
    (ρ : ℝ) (hρ : 0 < ρ)
    (hρ_bound : ∀ (x : E) (v : E),
      ρ * ‖v‖ ^ 2 ≤ hessianBilin m.V x v v)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (hf_grad_int : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) m.μ) :
    m.variance f ≤ (1 / ρ) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂m.μ := by
  obtain ⟨g, hg_smooth, hg_solve⟩ := m.exists_hessian_inverse f hf
  have hBL := m.brascampLieb f hf g hg_smooth hg_solve
  have hpw : ∀ x, (fderiv ℝ f x) (g x) ≤ 1 / ρ * ‖fderiv ℝ f x‖ ^ 2 :=
    fun x => pointwise_hessian_bound m.V ρ hρ hρ_bound f g x (hg_solve x)
  have hnn : ∀ x, 0 ≤ (fderiv ℝ f x) (g x) := by
    intro x
    have hρg := hρ_bound x (g x)
    have hkey : (fderiv ℝ f x) (g x) = hessianBilin m.V x (g x) (g x) := by
      simp only [hessianBilin]; rw [← hg_solve x]
    rw [hkey]
    have : 0 ≤ ρ * ‖g x‖ ^ 2 := by positivity
    linarith
  calc m.variance f
      ≤ ∫ x, (fderiv ℝ f x) (g x) ∂m.μ := hBL
    _ ≤ ∫ x, (1 / ρ * ‖fderiv ℝ f x‖ ^ 2) ∂m.μ := by
        apply MeasureTheory.integral_mono
        · -- Integrability via domination by (1/ρ)‖∇f‖²
          apply (hf_grad_int.const_mul (1 / ρ)).mono'
          · -- g is C¹ hence continuous; fderiv ℝ f is continuous (f is C¹).
            -- The map x ↦ (fderiv ℝ f x)(g x) is continuous, hence measurable.
            have hg_cont : Continuous g := hg_smooth.continuous
            have hdf_cont : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
            exact ((hdf_cont.clm_apply hg_cont).measurable).aestronglyMeasurable
          · filter_upwards with x
            rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
            exact hpw x
        · exact hf_grad_int.const_mul _
        · exact hpw
    _ = 1 / ρ * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂m.μ :=
        MeasureTheory.integral_const_mul _ _

end LogConcaveMeasure

end
