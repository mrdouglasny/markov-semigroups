/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dirichlet Forms and Markov Semigroups

Layer 1 of the abstraction hierarchy. A `DirichletSpace` bundles a
probability measure μ with a symmetric energy form E(f,g), providing the
minimal structure for Poincaré and log-Sobolev inequalities.

No gradient, metric, or manifold structure is assumed.

## Main definitions

- `DirichletSpace` — probability measure + symmetric energy form
- `DirichletSpace.variance` — Var_μ(f) = E[f²] - E[f]²
- `DirichletSpace.entropy` — Ent_μ(f) = ∫ f log f dμ - (∫ f dμ) log(∫ f dμ)

## References

- Fukushima, Oshima, and Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, de Gruyter, 2011
- Ma and Röckner, *Introduction to the Theory of (Non-Symmetric)
  Dirichlet Forms*, Springer, 1992
- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 1
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory

noncomputable section

/-- A Dirichlet space: a probability space equipped with a symmetric
energy form (Dirichlet form).

This is the minimal structure for stating Poincaré and log-Sobolev
inequalities. No gradient or geometry is assumed.

The energy form `E(f,g)` abstracts the integral `∫ ⟨∇f, ∇g⟩ dμ` that
appears on the right side of these inequalities. On ℝⁿ with the
Gaussian measure, `E(f,g) = ∫ ⟨∇f, ∇g⟩ dγ`. On a finite graph,
`E(f,g) = ½ Σ_{x~y} (f(x)-f(y))(g(x)-g(y)) μ(x)`. The abstract
formulation covers both. -/
class DirichletSpace (X : Type*) [MeasurableSpace X] where
  /-- Reference probability measure. -/
  μ : Measure X
  /-- The measure is a probability measure. -/
  hμ : IsProbabilityMeasure μ
  /-- Symmetric energy form (Dirichlet form): E(f, g). -/
  energy : (X → ℝ) → (X → ℝ) → ℝ
  /-- Energy is symmetric. -/
  energy_symm : ∀ f g, energy f g = energy g f
  /-- Energy is nonneg on the diagonal. -/
  energy_nonneg : ∀ f, 0 ≤ energy f f
  /-- Energy is bilinear (left). -/
  energy_add_left : ∀ f₁ f₂ g, energy (f₁ + f₂) g = energy f₁ g + energy f₂ g
  /-- Energy is bilinear (scalar left). -/
  energy_smul_left : ∀ (c : ℝ) f g, energy (c • f) g = c * energy f g
  /-- Constants have zero energy (Markov property consequence). -/
  energy_const : ∀ c : ℝ, energy (fun _ => c) (fun _ => c) = 0

attribute [instance] DirichletSpace.hμ

namespace DirichletSpace

variable {X : Type*} [MeasurableSpace X] [ds : DirichletSpace X]

/-- Variance of f under the reference measure. -/
def variance (f : X → ℝ) : ℝ :=
  ∫ x, (f x) ^ 2 ∂ds.μ - (∫ x, f x ∂ds.μ) ^ 2

/-- Entropy of a nonneg function f under the reference measure. -/
def entropy (f : X → ℝ) : ℝ :=
  ∫ x, f x * Real.log (f x) ∂ds.μ -
  (∫ x, f x ∂ds.μ) * Real.log (∫ x, f x ∂ds.μ)

/-- Poincaré inequality with constant ρ:
  Var_μ(f) ≤ (1/ρ) E(f, f) -/
def SatisfiesPoincare (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ f : X → ℝ, variance f ≤ (1 / ρ) * ds.energy f f

/-- Log-Sobolev inequality with constant ρ:
  Ent_μ(f²) ≤ (2/ρ) E(f, f) -/
def SatisfiesLogSobolev (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ f : X → ℝ, entropy (fun x => f x * f x) ≤ (2 / ρ) * ds.energy f f

/-! ### Helper lemmas for the energy form -/

/-- A constant function has zero energy against any function.
Proof: E(1,1) = 0 and E(f,f) >= 0 imply E(1,f) = 0 by the Cauchy-Schwarz
argument (the quadratic t -> E(1 + t*f, 1 + t*f) = 2t*E(1,f) + t^2*E(f,f)
must be nonneg for all t). Then E(c, f) = c * E(1, f) = 0. -/
theorem energy_const_left (c : ℝ) (f : X → ℝ) :
    ds.energy (fun _ => c) f = 0 := by
  -- First show E(1, f) = 0 where 1 is the constant-1 function
  suffices h1 : ds.energy (fun _ => (1 : ℝ)) f = 0 by
    have : ds.energy (fun _ => c) f = c * ds.energy (fun _ => (1 : ℝ)) f := by
      have : (fun (_ : X) => c) = c • (fun (_ : X) => (1 : ℝ)) := by
        ext x; simp
      rw [this, ds.energy_smul_left]
    rw [this, h1, mul_zero]
  -- Prove E(1, f) = 0 by Cauchy-Schwarz style argument
  -- For all t : ℝ, E(1 + t*f, 1 + t*f) >= 0
  -- E(1 + t*f, 1 + t*f) = E(1,1) + 2t*E(1,f) + t^2*E(f,f) = 2t*E(1,f) + t^2*E(f,f)
  -- This quadratic in t is >= 0 for all t, so E(1,f) = 0.
  by_contra h
  push Not at h
  set e := ds.energy (fun _ => (1 : ℝ)) f with he_def
  set a := ds.energy f f with ha_def
  -- We know E(1,1) = 0
  have h11 : ds.energy (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) = 0 := ds.energy_const 1
  -- Consider t = -e / a if a > 0, or t = -sign(e) * large otherwise
  -- Actually simpler: pick t with the right sign and small enough magnitude
  -- For all t, 2*t*e + t^2*a >= 0
  have key : ∀ t : ℝ, 0 ≤ 2 * t * e + t ^ 2 * a := by
    intro t
    -- E(1 + t•f, 1 + t•f) >= 0
    have h_nn := ds.energy_nonneg ((fun _ => (1 : ℝ)) + t • f)
    -- Rewrite as E(1,1) + 2t*E(1,f) + t^2*E(f,f) = 0 + 2t*e + t^2*a
    set one : X → ℝ := fun _ => (1 : ℝ) with hone_def
    set tf : X → ℝ := t • f with htf_def
    -- E(one + tf, one + tf) = E(one, one + tf) + E(tf, one + tf)
    have expand1 : ds.energy (one + tf) (one + tf) =
        ds.energy one (one + tf) + ds.energy tf (one + tf) :=
      ds.energy_add_left one tf (one + tf)
    -- E(one, one + tf) = E(one, one) + E(one, tf) = 0 + E(one, tf) = E(one, tf)
    have expand2 : ds.energy one (one + tf) =
        ds.energy one one + ds.energy one tf := by
      rw [ds.energy_symm one (one + tf), ds.energy_add_left, ds.energy_symm one one,
          ds.energy_symm tf one]
    -- E(tf, one + tf) = E(tf, one) + E(tf, tf)
    have expand3 : ds.energy tf (one + tf) =
        ds.energy tf one + ds.energy tf tf := by
      rw [ds.energy_symm tf (one + tf), ds.energy_add_left, ds.energy_symm one tf,
          ds.energy_symm tf tf]
    rw [expand1, expand2, expand3] at h_nn
    rw [h11] at h_nn
    simp only [zero_add] at h_nn
    -- E(one, tf) = t * E(1, f) = t * e
    have h_one_tf : ds.energy one tf = t * e := by
      rw [htf_def, ds.energy_symm, ds.energy_smul_left, ds.energy_symm]
    -- E(tf, one) = E(one, tf) = t * e
    have h_tf_one : ds.energy tf one = t * e := by
      rw [ds.energy_symm]; exact h_one_tf
    -- E(tf, tf) = t^2 * E(f,f) = t^2 * a
    have h_tf_tf : ds.energy tf tf = t ^ 2 * a := by
      rw [htf_def, ds.energy_smul_left, ds.energy_symm, ds.energy_smul_left,
          ds.energy_symm]; ring
    rw [h_one_tf, h_tf_one, h_tf_tf] at h_nn
    linarith
  -- Now from key, setting t = -e/a or using sign analysis
  -- If e ≠ 0, pick t = -e (works when |e| is small relative to a, but let's
  -- handle this more carefully)
  rcases ne_iff_lt_or_gt.mp h with h_neg | h_pos
  · -- e < 0: pick t > 0 small enough that 2*t*e + t^2*a < 0
    -- Choose t = -e/a if a > 0, or t = 1 if a = 0
    by_cases ha : a = 0
    · -- If a = 0, then 2*t*e >= 0 for all t, but e < 0 means 2*1*e < 0
      have := key 1
      linarith [ha]
    · -- a > 0 (since a >= 0 and a ≠ 0)
      have ha_pos : 0 < a := lt_of_le_of_ne (ds.energy_nonneg f) (Ne.symm ha)
      -- 2*(-e/a)*e + (-e/a)^2*a = -e^2/a < 0, contradiction
      have key_val := key (-e / a)
      have h_eq : 2 * (-e / a) * e + (-e / a) ^ 2 * a = -(e ^ 2 / a) := by field_simp; ring
      have h_esq : 0 < e ^ 2 := sq_pos_of_ne_zero (ne_of_lt h_neg)
      linarith [div_pos h_esq ha_pos]
  · -- e > 0: pick t < 0 small enough
    by_cases ha : a = 0
    · have := key (-1)
      linarith [ha]
    · have ha_pos : 0 < a := lt_of_le_of_ne (ds.energy_nonneg f) (Ne.symm ha)
      have key_val := key (-e / a)
      have h_eq : 2 * (-e / a) * e + (-e / a) ^ 2 * a = -(e ^ 2 / a) := by field_simp; ring
      have h_esq : 0 < e ^ 2 := sq_pos_of_ne_zero (ne_of_gt h_pos)
      linarith [div_pos h_esq ha_pos]

/-- Energy of a constant on the right is zero. -/
theorem energy_const_right (f : X → ℝ) (c : ℝ) :
    ds.energy f (fun _ => c) = 0 := by
  rw [ds.energy_symm]; exact energy_const_left c f

/-- Energy is invariant under additive constants: E(f + c, f + c) = E(f, f).
This follows from bilinearity and the fact that constants have zero energy. -/
theorem energy_add_const (f : X → ℝ) (c : ℝ) :
    ds.energy (fun x => f x + c) (fun x => f x + c) = ds.energy f f := by
  have h1 : (fun x => f x + c) = f + (fun _ => c) := by ext x; simp [Pi.add_apply]
  set k : X → ℝ := fun _ => c with hk_def
  rw [h1]
  -- E(f+k, f+k) = E(f, f+k) + E(k, f+k)  [add_left]
  rw [ds.energy_add_left f k (f + k)]
  -- E(f, f+k) via symmetry then add_left: E(f, f+k) = E(f+k, f) = E(f,f) + E(k,f)
  conv_lhs => rw [ds.energy_symm f (f + k), ds.energy_add_left f k f, ds.energy_symm f f]
  -- E(k, f+k) via symmetry then add_left: E(k, f+k) = E(f+k, k) = E(f,k) + E(k,k)
  conv_lhs => rw [ds.energy_symm k (f + k), ds.energy_add_left f k k]
  -- Now substitute all the zero terms
  rw [energy_const_left c f, energy_const_right f c, ds.energy_const c]
  ring

/-- Energy of a scalar multiple: E(t • f, t • f) = t² · E(f, f). -/
theorem energy_smul (t : ℝ) (f : X → ℝ) :
    ds.energy (t • f) (t • f) = t ^ 2 * ds.energy f f := by
  rw [ds.energy_smul_left, ds.energy_symm, ds.energy_smul_left, ds.energy_symm]
  ring

/-! ### Rothaus linearization: LSI implies Poincaré

The standard proof that a log-Sobolev inequality implies a Poincaré
inequality with the same constant, following Rothaus (1985) and
Bakry-Gentil-Ledoux, Prop 5.1.3.

**Strategy.** For any mean-zero g (∫g dμ = 0), apply LSI to
f_t(x) = 1 + t·g(x):

  Ent(f_t²) ≤ (2/ρ) · E(f_t, f_t) = (2/ρ) · t² · E(g, g)

A Taylor expansion gives Ent((1+tg)²) = 2t² · ∫g² dμ + O(t³),
so dividing by t² and sending t → 0 yields

  2 · Var(g) ≤ (2/ρ) · E(g, g),  i.e.  Var(g) ≤ (1/ρ) · E(g, g).

**Note.** The pointwise inequality x log x ≥ (x-1) + (x-1)²/2 is
FALSE for x > 1 (e.g. at x = 2: 2 log 2 ≈ 1.39 < 1.5 = 1 + 1/2),
so the global bound Ent(f²) ≥ 2·Var(f) does not hold. The correct
argument requires the limit. -/

/-- **LSI implies Poincaré** (Rothaus, 1985; BGL Prop 5.1.3).

A log-Sobolev inequality with constant ρ implies a Poincaré inequality
with the same constant ρ.

The proof uses the Rothaus linearization: apply the LSI to the family
f_t = 1 + t·g for mean-zero g, expand Ent(f_t²) to second order in t,
and take t → 0. -/
theorem logSobolev_implies_poincare {ρ : ℝ} (h : SatisfiesLogSobolev (ds := ds) ρ) :
    SatisfiesPoincare (ds := ds) ρ := by
  refine ⟨h.1, fun f => ?_⟩
  -- The Rothaus linearization argument:
  -- For any g with ∫g = 0, and any t > 0, apply LSI to (1 + t·g):
  --   Ent((1+tg)²) ≤ (2/ρ) · t² · E(g,g)
  -- Then Ent((1+tg)²)/t² → 2·Var(g) as t → 0⁺, giving Var(g) ≤ (1/ρ)·E(g,g).
  -- Since Var and E are both invariant under adding constants,
  -- this extends to all f (not just mean-zero).
  --
  -- The analytic core (limit of entropy quotient) requires integration theory
  -- and Taylor expansion of x·log(x); we sorry this for now.
  sorry

end DirichletSpace

end
