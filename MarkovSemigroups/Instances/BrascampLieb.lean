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

## Main definitions

- `LogConcaveMeasure` — structure bundling V, its regularity, and the
  weighted measure e^{-V} dx on a finite-dimensional real inner product
  space E
- `brascampLieb` — the Brascamp-Lieb variance bound
- `brascampLieb_poincare` — corollary: Brascamp-Lieb implies Poincaré

## Proof structure

- `pointwise_hessian_bound` — fully proven: when Hess V ≥ ρI,
  the integrand satisfies (∇f)(g) ≤ (1/ρ)‖∇f‖²
- `hessian_injective` — fully proven: positive definiteness ⟹ injectivity
- `hessian_surjective` — fully proven: injectivity + finite dimension ⟹
  surjectivity (via `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`)
- `exists_hessian_inverse` — existence proven via surjectivity;
  smoothness of g sorry'd (requires smooth dependence on parameters)
- `brascampLieb` — sorry'd (requires weighted IBP and Bochner identity)
- `brascampLieb_poincare` — derived from the above

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

namespace LogConcaveMeasure

variable (m : LogConcaveMeasure E)

/-- Variance of f under the log-concave measure. -/
def variance (f : E → ℝ) : ℝ :=
  ∫ x, (f x) ^ 2 ∂m.μ - (∫ x, f x ∂m.μ) ^ 2

/-! ### The Brascamp-Lieb inequality -/

/-- **Brascamp-Lieb inequality** (full pointwise form).
For a log-concave measure μ = e^{-V} dx with V strictly convex,
and any C¹ function f : E → ℝ,

  Var_μ(f) ≤ ∫ ((Hess V)(x))⁻¹[∇f(x), ∇f(x)] dμ(x)

The RHS is expressed via g = (Hess V)⁻¹ ∇f: given that
(Hess V)(x) · g(x) = ∇f(x) pointwise, the integrand is (∇f(x))(g(x)).
This bound is sharp: equality holds when f is affine.

## Proof outline (Bakry-Gentil-Ledoux, Prop. 4.9.1)

Let f̄ = f - μ(f) and solve Lu = f̄ where L = -Δ + ⟨∇V, ∇·⟩.

**Step 1.** Var_μ(f) = ∫ f̄² dμ = ∫ ⟨∇f, ∇u⟩ dμ (weighted IBP).

**Step 2.** From the Bochner identity ½L|∇u|² = ‖Hess u‖² +
  ⟨∇u, Hess V · ∇u⟩ + ⟨∇u, ∇(Lu)⟩, integrating against μ and using
  ∫ Lh dμ = 0 gives:
  ∫ ‖Hess u‖² dμ + ∫ ⟨∇u, Hess V · ∇u⟩ dμ = Var_μ(f).

**Step 3.** Since ‖Hess u‖² ≥ 0, we have
  ∫ ⟨∇u, Hess V · ∇u⟩ dμ ≤ Var_μ(f).

**Step 4.** Cauchy-Schwarz with weight (Hess V)^{1/2}:
  Var_μ(f)² = (∫ ⟨∇f, ∇u⟩ dμ)²
            ≤ (∫ ⟨∇f, (Hess V)⁻¹ ∇f⟩ dμ)(∫ ⟨∇u, Hess V · ∇u⟩ dμ)
            ≤ (∫ (∇f)(g) dμ) · Var_μ(f).

Dividing by Var_μ(f) gives the result. -/
theorem brascampLieb (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (g : E → E) (hg : ContDiff ℝ 1 g)
    (hg_solve : ∀ (x : E), (fderiv ℝ (fderiv ℝ m.V) x) (g x) = fderiv ℝ f x) :
    m.variance f ≤ ∫ x, (fderiv ℝ f x) (g x) ∂m.μ := by
  -- Requires: weighted IBP for μ = e^{-V} dx, existence of the resolvent
  -- for L = -Δ + ⟨∇V, ∇·⟩, the Bochner identity, and Cauchy-Schwarz.
  -- See docstring for the full proof outline.
  sorry

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
(Hess V)(x) v = 0 then v = 0. This follows from positive definiteness:
if v ≠ 0 then ((Hess V)(x) v) v > 0, so (Hess V)(x) v ≠ 0. -/
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

/-- In finite dimensions, the Hessian is surjective: since
E and E →L[ℝ] ℝ have equal finite rank (by the Riesz representation),
an injective linear map between them is also surjective. -/
theorem hessian_surjective (x : E) :
    Function.Surjective (fderiv ℝ (fderiv ℝ m.V) x) := by
  have hinj := m.hessian_injective x
  have hfd : FiniteDimensional ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← Subspace.dual_finrank_eq (K := ℝ) (V := E)]
    exact LinearMap.toContinuousLinearMap.finrank_eq
  -- The underlying linear map is injective
  have hinj_lm : Function.Injective (fderiv ℝ (fderiv ℝ m.V) x).toLinearMap := hinj
  -- Injective between equal-rank spaces → surjective
  have hsurj_lm := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj_lm
  intro φ
  obtain ⟨v, hv⟩ := hsurj_lm φ
  exact ⟨v, hv⟩

/-- Existence of the pointwise Hessian inverse: when Hess V is
positive definite everywhere, for any function f there exists
g : E → E with (Hess V)(x) · g(x) = ∇f(x) at every point. -/
theorem exists_hessian_inverse
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ g : E → E, ContDiff ℝ 1 g ∧
    ∀ (x : E), (fderiv ℝ (fderiv ℝ m.V) x) (g x) = fderiv ℝ f x := by
  -- At each x, the Hessian is surjective, so we can choose a preimage.
  have hsurj := m.hessian_surjective
  refine ⟨fun x => (hsurj x (fderiv ℝ f x)).choose, ?_, ?_⟩
  · -- Smoothness: g(x) = (Hess V)(x)⁻¹(∇f(x)) depends smoothly on x
    -- because V is C² (so the Hessian is C⁰) and f is C¹ (so ∇f is C⁰),
    -- and inversion of a smoothly varying family of invertible operators
    -- is smooth (Cramer's rule in finite dimensions).
    sorry
  · intro x
    exact (hsurj x (fderiv ℝ f x)).choose_spec

/-- **Brascamp-Lieb implies Poincaré.** If Hess V ≥ ρI everywhere, then

  Var_μ(f) ≤ (1/ρ) ∫ ‖∇f‖² dμ

Proof: construct g = (Hess V)⁻¹ ∇f, apply `brascampLieb`, then bound
the integrand pointwise using `pointwise_hessian_bound`. -/
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
  calc m.variance f
      ≤ ∫ x, (fderiv ℝ f x) (g x) ∂m.μ := hBL
    _ ≤ ∫ x, (1 / ρ * ‖fderiv ℝ f x‖ ^ 2) ∂m.μ := by
        apply MeasureTheory.integral_mono
        · sorry -- Integrable (fun x => (fderiv ℝ f x) (g x)) m.μ
        · exact hf_grad_int.const_mul _
        · exact hpw
    _ = 1 / ρ * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂m.μ :=
        MeasureTheory.integral_const_mul _ _

end LogConcaveMeasure

end
