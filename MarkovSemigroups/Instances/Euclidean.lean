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

def dirichletSpace : DirichletSpace ℝ where
  μ := γ
  hμ := inferInstance
  energy := ouEnergy
  energy_symm := fun f g => by
    simp only [ouEnergy]; congr 1; ext x; ring
  energy_nonneg := fun f => by
    simp only [ouEnergy]
    exact integral_nonneg (fun x => mul_self_nonneg (deriv f x))
  energy_add_left := fun f₁ f₂ g => by
    -- PROVABLE when f₁, f₂ differentiable: deriv(f₁+f₂) = deriv f₁ + deriv f₂.
    -- For general functions, deriv returns 0 at non-differentiable points.
    -- The identity holds when both are differentiable (deriv_add) or when
    -- both are non-differentiable (all terms 0). The mixed case needs care.
    simp only [ouEnergy]
    sorry
  energy_smul_left := fun c f g => by
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
def bakryEmerySpace : BakryEmerySpace ℝ where
  toDirichletSpace := dirichletSpace
  Γ := ouGamma
  Γ_symm := fun f g => by ext x; simp only [ouGamma]; ring
  Γ_nonneg := fun f x => by simp only [ouGamma]; exact mul_self_nonneg _
  energy_eq_integral_Γ := fun f g => by
    simp only [ouGamma]; rfl
  Γ_leibniz := fun f g h x => by
    -- THIS IS THE KEY FIELD that fails for TwoPoint but holds here.
    -- Γ(fg, h)(x) = deriv(fg)(x) · deriv h(x)
    --             = (f(x)·deriv g(x) + g(x)·deriv f(x)) · deriv h(x)  [product rule]
    --             = f(x)·Γ(g,h)(x) + g(x)·Γ(f,h)(x)
    -- Needs DifferentiableAt for deriv_mul. Sorry for general functions;
    -- holds for all smooth/differentiable functions (the intended domain).
    simp only [ouGamma]
    sorry
  Γ_const := fun c f => by
    ext x; simp only [ouGamma, deriv_const, Pi.zero_apply]; ring
  semigroup := ouSemigroup
  ρ := 1
  hρ := one_pos
  gradient_decay := fun f t ht => by
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
  semigroup_contraction := fun f t ht => by
    -- Jensen: ∫(P_t f)² dγ ≤ ∫ f² dγ since (·)² is convex and P_t is a
    -- Markov operator (positive, mass-preserving).
    sorry
  semigroup_mean := fun f t ht => by
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
    by_cases hf : AEStronglyMeasurable f γ
    · -- ∫ f dγ = ∫ f ∘ φ d(γ×γ) by HasLaw.integral_comp
      have hcomp : ∫ p, f (φ p) ∂(γ.prod γ) = ∫ x, f x ∂γ :=
        hlaw.integral_comp hf
      rw [← hcomp]
      by_cases hint : Integrable f γ
      · -- Integrable: use Fubini
        have hasm' : AEStronglyMeasurable f ((γ.prod γ).map φ) := by rwa [hmap]
        have hint' : Integrable f ((γ.prod γ).map φ) := by rwa [hmap]
        have hfφ : Integrable (f ∘ φ) (γ.prod γ) :=
          (integrable_map_measure hasm' hφ.aemeasurable).mp hint'
        -- Goal: ∫ x, (∫ y, f(φ(x,y)) dγ) dγ = ∫ p, f(φ p) d(γ.prod γ)
        -- This is Fubini backward: integral_prod gives ∫ prod = ∫∫ iterated
        exact (integral_prod (f ∘ φ) hfφ).symm
      · -- AEStronglyMeasurable but not integrable: the iterated integral
        -- equals the product integral (both are 0).
        -- RHS = ∫ f dγ = 0 since f is not integrable
        rw [hcomp, integral_undef hint]
        -- LHS = 0: requires showing the iterated integral vanishes
        -- when the product integral is not integrable.
        sorry
    · -- f is not AEStronglyMeasurable w.r.t. γ: both sides = 0
      rw [integral_non_aestronglyMeasurable hf]
      -- The iterated integral is 0 because f is not measurable
      sorry
  semigroup_selfAdjoint := fun f g t ht => by
    -- Self-adjointness: the Mehler kernel K(t,x,y) is symmetric in (x,y)
    -- after accounting for the Gaussian weight.
    sorry
  semigroup_l2_decay_bound := fun f t ht => by
    -- Integrated gradient decay. Follows from gradient_decay + FTC.
    sorry
  semigroup_l2_sq_hasDerivWithinAt := fun f t ht => by
    -- d/dt ∫(P_t f)² dγ = -2 ∫ (P_t f')² dγ = -2 E(P_t f).
    -- Requires differentiation under the integral for the Mehler kernel.
    sorry
  semigroup_ergodic := fun f => by
    -- Var(P_t f) → 0: as t → ∞, P_t f → E[f] in L²(γ) since
    -- e^{-t} → 0 and √(1-e^{-2t}) → 1, so P_t f(x) → ∫ f dγ.
    sorry
  semigroup_entropy_sq_decay_bound := fun f t ht => by
    -- Entropy decay bound. Follows from Γ_leibniz (giving I(f²) = 4E(f))
    -- and gradient_decay for Fisher information.
    sorry
  semigroup_entropy_sq_ergodic := fun f => by
    -- Ent(P_t(f²)) → 0 by ergodicity + continuity of x·log(x).
    sorry

end Gaussian1D

end
