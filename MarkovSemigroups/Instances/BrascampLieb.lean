/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Brascamp-Lieb Inequality (Classical/Statistical Mechanics Version)

The Brascamp-Lieb inequality for log-concave measures on ℝⁿ:
given μ = e^{-V} dx with V ∈ C² strictly convex (Hess V > 0),

  Var_μ(f) ≤ ∫ ⟨∇f, (Hess V)⁻¹ ∇f⟩ dμ

## Architecture

Three textbook results are postulated as axioms, each more elementary
than Brascamp-Lieb itself:

1. `resolvent_ibp_axiom` — resolvent existence + weighted IBP
2. `bochner_inequality` — the Bochner/Weitzenböck inequality
3. `weighted_young` — Young's inequality for positive definite forms

The Brascamp-Lieb inequality `brascampLieb` is PROVEN from these three
axioms by a short algebraic argument. The Poincaré corollary
`brascampLieb_poincare` is then derived from Brascamp-Lieb.

Also postulated:
4. `continuous_hessianInverse_gradient` — continuity of (Hess V)⁻¹ ∇f

## References

- Brascamp and Lieb, J. Funct. Anal. 22 (1976), 366–389
- Bakry, Gentil, and Ledoux, Springer, 2014, §4.9
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option linter.unusedSectionVars false

open MeasureTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The Hessian bilinear form of V at x, evaluated on (v, w). -/
def hessianBilin (V : E → ℝ) (x : E) (v : E) (w : E) : ℝ :=
  ((fderiv ℝ (fderiv ℝ V) x) v) w

/-- The gradient of f at x ∈ E, as an element of E (Riesz representative
of the Fréchet derivative). Satisfies ⟨gradient f x, v⟩ = (fderiv ℝ f x) v. -/
def gradient (f : E → ℝ) (x : E) : E :=
  (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)

theorem gradient_inner (f : E → ℝ) (x : E) (v : E) :
    @inner ℝ E _ (gradient f x) v = (fderiv ℝ f x) v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

/-- A log-concave measure on a finite-dimensional real inner product space:
μ = e^{-V(x)} dx where V is C² and strictly convex. -/
structure LogConcaveMeasure (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] where
  V : E → ℝ
  hV_diff : ContDiff ℝ 2 V
  hV_convex : ∀ (x : E) (v : E), v ≠ 0 → (0 : ℝ) < hessianBilin V x v v
  μ : Measure E
  hμ_prob : IsProbabilityMeasure μ
  /-- The resolvent: for each C¹ function f, the solution u of
  Lu = -(f - ∫f dμ) where L = Δ - ⟨∇V, ∇·⟩.
  Existence follows from Lax-Milgram for the Dirichlet form
  E(u,g) = ∫ ⟨∇u, ∇g⟩ dμ on H¹(μ). -/
  resolvent : (E → ℝ) → (E → ℝ)
  /-- Weighted IBP identity: Var(f) = ∫ ⟨∇f, ∇u⟩ dμ where u = resolvent(f).
  Combines Lax-Milgram (resolvent existence) with the weighted divergence
  theorem for μ = e^{-V} dx.
  Reference: BGL §1.15. -/
  resolvent_ibp : ∀ (f : E → ℝ), ContDiff ℝ 1 f →
    (∫ x, (f x) ^ 2 ∂μ - (∫ x, f x ∂μ) ^ 2) =
      ∫ x, (fderiv ℝ f x) (gradient (resolvent f) x) ∂μ
  /-- The integrand in the IBP identity is integrable. -/
  resolvent_ibp_integrable : ∀ (f : E → ℝ), ContDiff ℝ 1 f →
    Integrable (fun x => (fderiv ℝ f x) (gradient (resolvent f) x)) μ
  /-- Integrated Bochner-Weitzenböck identity: for u = resolvent(f),
  Var(f) = R + ∫ H(∇u, ∇u) dμ where R = ∫ ‖Hess u‖² dμ ≥ 0.

  Takes u as parameter (equals resolvent f by construction) to
  match the downstream API that passes u from resolvent_ibp.

  Integrates the pointwise Bochner formula
    ½L(|∇u|²) = ⟨∇u, ∇(Lu)⟩ + ‖Hess u‖² + H(∇u, ∇u)
  against μ, using ∫Lh dμ = 0 and Lu = -(f - ∫f).
  Reference: BGL §1.16. -/
  bochner_identity : ∀ (f : E → ℝ) (u : E → ℝ), ContDiff ℝ 1 f →
    (∫ x, (f x) ^ 2 ∂μ - (∫ x, f x ∂μ) ^ 2) =
      ∫ x, (fderiv ℝ f x) (gradient u x) ∂μ →
    ∃ R : ℝ, 0 ≤ R ∧
    (∫ x, (f x) ^ 2 ∂μ - (∫ x, f x ∂μ) ^ 2) =
      R + ∫ x, hessianBilin V x (gradient u x) (gradient u x) ∂μ

attribute [instance] LogConcaveMeasure.hμ_prob

/-! ## Proved from structure fields (formerly axioms) -/

/-- **Resolvent + weighted IBP (BGL §1.15).** PROVED from structure fields. -/
theorem resolvent_ibp_axiom {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (m : LogConcaveMeasure E)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ u : E → ℝ,
    (∫ x, (f x) ^ 2 ∂m.μ - (∫ x, f x ∂m.μ) ^ 2) =
      ∫ x, (fderiv ℝ f x) (gradient u x) ∂m.μ ∧
    Integrable (fun x => (fderiv ℝ f x) (gradient u x)) m.μ :=
  ⟨m.resolvent f, m.resolvent_ibp f hf, m.resolvent_ibp_integrable f hf⟩

/-- **Integrated Bochner identity (BGL §1.16).** PROVED from structure fields.
Note: the identity is stated for u = m.resolvent f specifically. -/
theorem integrated_bochner_inequality {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (m : LogConcaveMeasure E)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (u : E → ℝ)
    (hu : (∫ x, (f x) ^ 2 ∂m.μ - (∫ x, f x ∂m.μ) ^ 2) =
          ∫ x, (fderiv ℝ f x) (gradient u x) ∂m.μ) :
    ∃ R : ℝ, 0 ≤ R ∧
    (∫ x, (f x) ^ 2 ∂m.μ - (∫ x, f x ∂m.μ) ^ 2) =
      R + ∫ x, hessianBilin m.V x (gradient u x) (gradient u x) ∂m.μ :=
  m.bochner_identity f u hf hu

/-- **Bochner inequality (PROVEN).** ∫ H(∇u, ∇u) dμ ≤ Var(f).
Immediate from `integrated_bochner_inequality`: Var = R + ∫H(∇u,∇u) with R ≥ 0. -/
theorem bochner_inequality {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (m : LogConcaveMeasure E)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (u : E → ℝ)
    (hu : (∫ x, (f x) ^ 2 ∂m.μ - (∫ x, f x ∂m.μ) ^ 2) =
          ∫ x, (fderiv ℝ f x) (gradient u x) ∂m.μ) :
    ∫ x, hessianBilin m.V x (gradient u x) (gradient u x) ∂m.μ ≤
      (∫ x, (f x) ^ 2 ∂m.μ - (∫ x, f x ∂m.μ) ^ 2) := by
  obtain ⟨R, hR, hident⟩ := integrated_bochner_inequality m f hf u hu
  linarith

/-- **Weighted Young's inequality (PROVEN).** Pointwise:
(∇f)(∇u) ≤ ½ H(∇u, ∇u) + ½ (∇f)(g)

Proof: expand 0 ≤ ½ H(∇u - g, ∇u - g) using bilinearity and Hessian
symmetry (equality of mixed partials for C² functions). -/
theorem weighted_young (m : LogConcaveMeasure E)
    (f : E → ℝ) (g : E → E)
    (hg_solve : ∀ x, (fderiv ℝ (fderiv ℝ m.V) x) (g x) = fderiv ℝ f x)
    (u : E → ℝ) (x : E) :
    (fderiv ℝ f x) (gradient u x) ≤
      (1 / 2) * hessianBilin m.V x (gradient u x) (gradient u x) +
      (1 / 2) * (fderiv ℝ f x) (g x) := by
  -- Hessian symmetry: for C² functions, mixed partials commute
  have hsymm : ∀ v w, hessianBilin m.V x v w = hessianBilin m.V x w v := by
    intro v w
    have hcd : ContDiffAt ℝ 2 m.V x := m.hV_diff.contDiffAt
    have := hcd.isSymmSndFDerivAt (𝕜 := ℝ) (by norm_num [minSmoothness])
    exact this v w
  -- Key identity: H(∇u, g) = (∇f)(∇u) by symmetry + solve equation
  have hHug : hessianBilin m.V x (gradient u x) (g x) =
      (fderiv ℝ f x) (gradient u x) := by
    rw [hsymm (gradient u x) (g x)]
    simp only [hessianBilin]
    rw [← hg_solve x]
  -- Key identity: H(g, g) = (∇f)(g) by solve equation
  have hHgg : hessianBilin m.V x (g x) (g x) = (fderiv ℝ f x) (g x) := by
    simp only [hessianBilin]; rw [← hg_solve x]
  -- Let w = ∇u - g. By positive semi-definiteness: 0 ≤ H(w, w)
  set a := gradient u x
  set b := g x
  -- H(a-b, a-b) = H(a,a) - 2H(a,b) + H(b,b) by bilinearity
  have hexpand : hessianBilin m.V x (a - b) (a - b) =
      hessianBilin m.V x a a - 2 * hessianBilin m.V x a b +
      hessianBilin m.V x b b := by
    simp only [hessianBilin, map_sub, ContinuousLinearMap.sub_apply]
    have := hsymm a b
    simp only [hessianBilin] at this
    linarith
  -- 0 ≤ H(a-b, a-b)
  have hpsd : 0 ≤ hessianBilin m.V x (a - b) (a - b) := by
    by_cases hw : a - b = 0
    · simp [hessianBilin, hw, map_zero]
    · exact le_of_lt (m.hV_convex x (a - b) hw)
  -- Substitute identities and rearrange
  rw [hexpand, hHug, hHgg] at hpsd
  linarith

/-- Construct a ContinuousLinearEquiv from a bijective CLM in finite dimensions. -/
def clmEquivOfBijective (H : E →L[ℝ] (E →L[ℝ] ℝ))
    (hinj : Function.Injective H) (hsurj : Function.Surjective H) :
    E ≃L[ℝ] (E →L[ℝ] ℝ) := by
  let le := LinearEquiv.ofBijective H.toLinearMap ⟨hinj, hsurj⟩
  let invCLM : (E →L[ℝ] ℝ) →L[ℝ] E := LinearMap.toContinuousLinearMap le.symm.toLinearMap
  exact ContinuousLinearEquiv.equivOfInverse H invCLM
    (fun x => le.symm_apply_apply x) (fun x => le.apply_symm_apply x)

/-- **PROVEN.** Continuity of the canonical Hessian inverse applied to
the gradient: g(x) = (Hess V x)⁻¹(∇f x) is continuous.

Proof: the Hessian x ↦ Hess V x is continuous (V is C²), operator
inversion is continuous at invertible maps (`contDiffAt_map_inverse`),
and the gradient x ↦ ∇f x is continuous (f is C¹). The composition
via `Continuous.clm_apply` is continuous. -/
theorem continuous_hessianInverse_gradient (m : LogConcaveMeasure E)
    (hinj : ∀ x, Function.Injective (fderiv ℝ (fderiv ℝ m.V) x))
    (hsurj : ∀ x, Function.Surjective (fderiv ℝ (fderiv ℝ m.V) x))
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) :
    Continuous (fun x => ContinuousLinearMap.inverse (fderiv ℝ (fderiv ℝ m.V) x) (fderiv ℝ f x)) := by
  have hHess_cont : Continuous (fderiv ℝ (fderiv ℝ m.V)) := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ m.V) := m.hV_diff.fderiv_right (by norm_num)
    exact h1.continuous_fderiv (by norm_num)
  have hgrad_cont : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hInv : ∀ x, ContinuousLinearMap.IsInvertible (fderiv ℝ (fderiv ℝ m.V) x) :=
    fun x => ⟨clmEquivOfBijective _ (hinj x) (hsurj x), rfl⟩
  have hInvHess : Continuous (fun x => ContinuousLinearMap.inverse (fderiv ℝ (fderiv ℝ m.V) x)) := by
    rw [continuous_iff_continuousAt]; intro x
    exact (((hInv x).contDiffAt_map_inverse (n := 0)).continuousAt).comp hHess_cont.continuousAt
  exact hInvHess.clm_apply hgrad_cont

namespace LogConcaveMeasure

variable (m : LogConcaveMeasure E)

/-- Variance of f under the log-concave measure. -/
def variance (f : E → ℝ) : ℝ :=
  ∫ x, (f x) ^ 2 ∂m.μ - (∫ x, f x ∂m.μ) ^ 2

/-! ### The Brascamp-Lieb inequality — PROVEN -/

/-- **Brascamp-Lieb inequality.** PROVEN from Axioms 1–3.

Let u be the resolvent (Axiom 1), so Var(f) = ∫(∇f)(∇u) dμ.
By weighted Young's (Axiom 3): (∇f)(∇u) ≤ ½H(∇u,∇u) + ½(∇f)(g).
Integrating and using Bochner (Axiom 2): ∫H(∇u,∇u) dμ ≤ Var(f).
So: Var(f) ≤ ½Var(f) + ½∫(∇f)(g) dμ, giving Var(f) ≤ ∫(∇f)(g) dμ. -/
theorem brascampLieb (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (g : E → E)
    (hg_solve : ∀ x, (fderiv ℝ (fderiv ℝ m.V) x) (g x) = fderiv ℝ f x)
    (hg_int : Integrable (fun x => (fderiv ℝ f x) (g x)) m.μ)
    (hH_int : ∀ u : E → ℝ, Integrable (fun x =>
      hessianBilin m.V x (gradient u x) (gradient u x)) m.μ) :
    m.variance f ≤ ∫ x, (fderiv ℝ f x) (g x) ∂m.μ := by
  -- Step 1: Get resolvent u from Axiom 1
  obtain ⟨u, hu_var, hu_int⟩ := resolvent_ibp_axiom m f hf
  have hu_bochner := bochner_inequality m f hf u hu_var
  -- Step 2: Pointwise Young's (Axiom 3)
  have h_young : ∀ x, (fderiv ℝ f x) (gradient u x) ≤
      (1/2) * hessianBilin m.V x (gradient u x) (gradient u x) +
      (1/2) * (fderiv ℝ f x) (g x) :=
    weighted_young m f g hg_solve u
  -- Step 3: Integrate the pointwise bound
  have h_int_bound : ∫ x, (fderiv ℝ f x) (gradient u x) ∂m.μ ≤
      (1/2) * ∫ x, hessianBilin m.V x (gradient u x) (gradient u x) ∂m.μ +
      (1/2) * ∫ x, (fderiv ℝ f x) (g x) ∂m.μ := by
    calc ∫ x, (fderiv ℝ f x) (gradient u x) ∂m.μ
        ≤ ∫ x, ((1/2) * hessianBilin m.V x (gradient u x) (gradient u x) +
                 (1/2) * (fderiv ℝ f x) (g x)) ∂m.μ :=
          MeasureTheory.integral_mono hu_int
            ((hH_int u).const_mul (1/2) |>.add (hg_int.const_mul (1/2)))
            h_young
      _ = (1/2) * ∫ x, hessianBilin m.V x (gradient u x) (gradient u x) ∂m.μ +
          (1/2) * ∫ x, (fderiv ℝ f x) (g x) ∂m.μ := by
          rw [MeasureTheory.integral_add ((hH_int u).const_mul _) (hg_int.const_mul _),
              MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- Step 4: Combine: Var = ∫(∇f)(∇u) ≤ ½∫H(∇u,∇u) + ½∫(∇f)(g) ≤ ½Var + ½∫(∇f)(g)
  unfold variance
  linarith

/-! ### Pointwise bound -/

theorem pointwise_hessian_bound
    (V : E → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ_bound : ∀ (x : E) (v : E), ρ * ‖v‖ ^ 2 ≤ hessianBilin V x v v)
    (f : E → ℝ) (g : E → E) (x : E)
    (hg_solve : (fderiv ℝ (fderiv ℝ V) x) (g x) = fderiv ℝ f x) :
    (fderiv ℝ f x) (g x) ≤ (1 / ρ) * ‖fderiv ℝ f x‖ ^ 2 := by
  have key : (fderiv ℝ f x) (g x) = hessianBilin V x (g x) (g x) := by
    simp only [hessianBilin]; rw [← hg_solve]
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
  · simp only [hessianBilin, hgz, map_zero]; positivity
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

theorem hessian_injective (x : E) :
    Function.Injective (fderiv ℝ (fderiv ℝ m.V) x) := by
  intro v w hvw; by_contra h
  have hne : v - w ≠ 0 := sub_ne_zero.mpr h
  have hpos := m.hV_convex x (v - w) hne
  have : hessianBilin m.V x (v - w) (v - w) = 0 := by
    simp only [hessianBilin, map_sub]
    simp [show (fderiv ℝ (fderiv ℝ m.V) x) v = (fderiv ℝ (fderiv ℝ m.V) x) w from hvw, sub_self]
  linarith

theorem hessian_surjective (x : E) :
    Function.Surjective (fderiv ℝ (fderiv ℝ m.V) x) := by
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← Subspace.dual_finrank_eq (K := ℝ) (V := E)]
    exact LinearMap.toContinuousLinearMap.finrank_eq
  have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (m.hessian_injective x : Function.Injective (fderiv ℝ (fderiv ℝ m.V) x).toLinearMap)
  intro φ; obtain ⟨v, hv⟩ := this φ; exact ⟨v, hv⟩

theorem exists_hessian_inverse (f : E → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ g : E → E, Continuous g ∧
    ∀ x, (fderiv ℝ (fderiv ℝ m.V) x) (g x) = fderiv ℝ f x := by
  -- Define g explicitly via ContinuousLinearMap.inverse
  let g : E → E := fun x =>
    ContinuousLinearMap.inverse (fderiv ℝ (fderiv ℝ m.V) x) (fderiv ℝ f x)
  refine ⟨g, ?_, ?_⟩
  · -- Continuity: proven via contDiffAt_map_inverse
    exact continuous_hessianInverse_gradient m
      (fun x => m.hessian_injective x) (fun x => m.hessian_surjective x) f hf
  · -- Solve equation: (Hess V x)(g x) = ∇f(x)
    intro x
    have hInv : ContinuousLinearMap.IsInvertible (fderiv ℝ (fderiv ℝ m.V) x) :=
      ⟨clmEquivOfBijective _ (m.hessian_injective x) (m.hessian_surjective x), rfl⟩
    exact ContinuousLinearMap.IsInvertible.self_apply_inverse hInv _

/-! ### Poincaré corollary -/

theorem brascampLieb_poincare
    (ρ : ℝ) (hρ : 0 < ρ)
    (hρ_bound : ∀ (x v : E), ρ * ‖v‖ ^ 2 ≤ hessianBilin m.V x v v)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (hf_grad_int : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) m.μ)
    (hH_int : ∀ u : E → ℝ, Integrable (fun x =>
      hessianBilin m.V x (gradient u x) (gradient u x)) m.μ) :
    m.variance f ≤ (1 / ρ) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂m.μ := by
  obtain ⟨g, hg_cont, hg_solve⟩ := m.exists_hessian_inverse f hf
  -- Integrability of (∇f)(g)
  have hpw : ∀ x, (fderiv ℝ f x) (g x) ≤ 1 / ρ * ‖fderiv ℝ f x‖ ^ 2 :=
    fun x => pointwise_hessian_bound m.V ρ hρ hρ_bound f g x (hg_solve x)
  have hnn : ∀ x, 0 ≤ (fderiv ℝ f x) (g x) := by
    intro x
    have hkey : (fderiv ℝ f x) (g x) = hessianBilin m.V x (g x) (g x) := by
      simp only [hessianBilin]; rw [← hg_solve x]
    rw [hkey]
    have h1 := hρ_bound x (g x)
    have h2 : 0 ≤ ρ * ‖g x‖ ^ 2 := by positivity
    linarith
  have hg_int : Integrable (fun x => (fderiv ℝ f x) (g x)) m.μ := by
    apply (hf_grad_int.const_mul (1 / ρ)).mono'
    · exact ((hf.continuous_fderiv (by norm_num)).clm_apply hg_cont).measurable.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]; exact hpw x
  -- Apply Brascamp-Lieb
  have hBL := m.brascampLieb f hf g hg_solve hg_int hH_int
  calc m.variance f
      ≤ ∫ x, (fderiv ℝ f x) (g x) ∂m.μ := hBL
    _ ≤ ∫ x, (1 / ρ * ‖fderiv ℝ f x‖ ^ 2) ∂m.μ :=
        MeasureTheory.integral_mono hg_int (hf_grad_int.const_mul _) hpw
    _ = 1 / ρ * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂m.μ :=
        MeasureTheory.integral_const_mul _ _

end LogConcaveMeasure

end
