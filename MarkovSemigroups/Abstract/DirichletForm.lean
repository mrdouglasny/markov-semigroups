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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

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

/-! ### Analytic sub-lemmas for the Rothaus expansion

The proof of `rothaus_entropy_expansion` is factored into three sub-lemmas:

1. `mul_log_taylor2_lower` [PROVED]: A pointwise Taylor estimate for
   `(1+s)·log(1+s)` near `s = 0`, proved using Mathlib's
   `Real.abs_log_sub_add_sum_range_le` (Taylor remainder for `log`).

2. `integral_sq_perturbation` [SORRY]: An algebraic identity computing
   `∫ (1+tg)² dμ = 1 + t² · Var(f)` for mean-zero `g`. Requires Mathlib's
   integral linearity and probability measure API. This is a helper for (3).

3. `entropy_quadratic_lower` [SORRY]: The integration step combining the
   pointwise Taylor bound with dominated convergence. This requires
   Taylor estimates, Bochner integrability, and DCT. It is the remaining
   analytical obstacle; `rothaus_entropy_expansion` delegates to it.
-/

/-- **Taylor lower bound for `(1+s) · log(1+s)` near 0.**

For any `ε > 0`, there exists `δ > 0` such that for `|s| < δ`:
  `(1+s) · log(1+s) ≥ s + (1 - ε)/2 · s²`

Proved using `Real.abs_log_sub_add_sum_range_le` (Mathlib's bound on the Taylor
remainder of `log(1-x)`). With `n = 2` and `x = -s`:
  `|log(1+s) - (s - s²/2)| ≤ |s|³/(1 - |s|)`
Multiplying by `1 + s > 0` and bounding the cubic error term by `ε/2 · s²`
for `|s| < min(1/2, ε/8)` gives the result.

The `s ≥ 0` case uses `8s ≤ ε` and `8(1-s) ≥ 3+s` to bound the error.
The `s < 0` case simplifies because `1 - |s| = 1 + s` cancels the denominator,
leaving only `|s|³/2 ≤ ε/2 · s²`. -/
theorem mul_log_taylor2_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
      s + (1 - ε) / 2 * s ^ 2 ≤ (1 + s) * Real.log (1 + s) := by
  refine ⟨min (1/2) (ε / 8), by positivity, fun s hs => ?_⟩
  have h_half : |s| < 1 / 2 := lt_of_lt_of_le hs (min_le_left _ _)
  have h_eps : |s| < ε / 8 := lt_of_lt_of_le hs (min_le_right _ _)
  have h_pos : (0 : ℝ) < 1 + s := by linarith [neg_abs_le s]
  have h_sub : (0 : ℝ) < 1 - |s| := by linarith
  have h_one : |s| < 1 := by linarith
  -- Taylor bound from Mathlib: |(-s + s²/2) + log(1+s)| ≤ |s|³/(1-|s|)
  have habs_neg : |-s| < 1 := by rwa [abs_neg]
  have hlog := Real.abs_log_sub_add_sum_range_le habs_neg 2
  have hsum : ∑ i ∈ Finset.range 2, (-s) ^ (i + 1) / (↑i + 1) = -s + s ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]; ring
  rw [hsum, show (1 : ℝ) - -s = 1 + s from by ring, abs_neg] at hlog
  -- Extract lower bound: log(1+s) ≥ s - s²/2 - |s|³/(1-|s|)
  have hlog_lb : s - s ^ 2 / 2 - |s| ^ 3 / (1 - |s|) ≤ Real.log (1 + s) := by
    linarith [neg_abs_le ((-s + s ^ 2 / 2) + Real.log (1 + s))]
  -- Multiply by (1+s) > 0
  have hmul : (1 + s) * (s - s ^ 2 / 2 - |s| ^ 3 / (1 - |s|)) ≤ (1 + s) * Real.log (1 + s) :=
    mul_le_mul_of_nonneg_left hlog_lb (le_of_lt h_pos)
  suffices h : s + (1 - ε) / 2 * s ^ 2 ≤
      (1 + s) * (s - s ^ 2 / 2 - |s| ^ 3 / (1 - |s|)) by linarith
  -- Clear the (1-|s|) denominator: reduce to a polynomial inequality
  have h_ne : (1 - |s|) ≠ 0 := ne_of_gt h_sub
  suffices key : 0 ≤ ε / 2 * s ^ 2 * (1 - |s|) - s ^ 3 / 2 * (1 - |s|) - (1 + s) * |s| ^ 3 by
    have expand : (s + (1 - ε) / 2 * s ^ 2) * (1 - |s|) ≤
        (1 + s) * (s - s ^ 2 / 2) * (1 - |s|) - (1 + s) * |s| ^ 3 := by
      nlinarith [sq_abs s]
    have hdiv := div_le_div_of_nonneg_right expand (le_of_lt h_sub)
    simp only [mul_div_cancel_right₀ _ h_ne] at hdiv
    have key2 : ((1 + s) * (s - s ^ 2 / 2) * (1 - |s|) - (1 + s) * |s| ^ 3) / (1 - |s|) =
        (1 + s) * (s - s ^ 2 / 2 - |s| ^ 3 / (1 - |s|)) := by field_simp
    linarith
  -- Split on sign of s for the polynomial inequality
  by_cases hs_nn : 0 ≤ s
  · -- s ≥ 0: |s| = s, factor as s² · (ε/2·(1-s) - s·(3/2+s/2))
    rw [abs_of_nonneg hs_nn]
    have hrw : ε / 2 * s ^ 2 * (1 - s) - s ^ 3 / 2 * (1 - s) - (1 + s) * s ^ 3 =
      s ^ 2 * (ε / 2 * (1 - s) - s * (3 / 2 + s / 2)) := by ring
    rw [hrw]
    apply mul_nonneg (sq_nonneg s)
    have : s < ε / 8 := by rwa [abs_of_nonneg hs_nn] at h_eps
    have : s < 1 / 2 := by rwa [abs_of_nonneg hs_nn] at h_half
    nlinarith
  · -- s < 0: |s| = -s, 1-|s| = 1+s, factor as (1+s)·s²·(ε/2+s/2)
    push Not at hs_nn
    rw [abs_of_neg hs_nn]
    have hrw : ε / 2 * s ^ 2 * (1 - -s) - s ^ 3 / 2 * (1 - -s) - (1 + s) * (-s) ^ 3 =
      (1 + s) * s ^ 2 * (ε / 2 + s / 2) := by ring
    rw [hrw]
    apply mul_nonneg (mul_nonneg (le_of_lt h_pos) (sq_nonneg s))
    have : -s < ε / 8 := by rwa [abs_of_neg hs_nn] at h_eps
    linarith

/-- **Integral of the squared perturbation.**

For a probability measure μ and mean-zero g (i.e., g = f - ∫f),
  `∫ (1 + t·g)² dμ = 1 + t² · Var(f)`

Proof: expand (1+tg)² = 1 + 2tg + t²g², integrate using ∫1 = 1,
∫g = 0, and ∫g² = Var(f) (since ∫g = 0 means Var = ∫g²). -/
theorem integral_sq_perturbation (f : X → ℝ)
    (hf_int : Integrable f ds.μ) (hf2_int : Integrable (fun x => f x ^ 2) ds.μ)
    (t : ℝ) :
    ∫ x, (1 + t * (f x - ∫ y, f y ∂ds.μ)) ^ 2 ∂ds.μ = 1 + t ^ 2 * variance f := by
  sorry

/-- **Entropy lower bound via Taylor expansion and dominated convergence.**

For a probability measure μ and f with finite first and second moments,
let g = f - ∫f (mean zero). For any ε > 0, there exists δ > 0 such that
for 0 < t < δ:

  `(2 - ε) · t² · Var(f) ≤ Ent((1 + t·g)²)`

This combines:
- The pointwise Taylor bound `mul_log_taylor2_lower` applied to
  `s = 2tg(x) + t²g(x)²` (since `(1+tg)² = 1 + s`)
- Dominated convergence to exchange limit and integral
- An upper bound on `(∫h) · log(∫h)` using `log(1+u) ≤ u`

The `O(t³)` error terms vanish after dividing by `t²` and taking `t → 0`.
This is the analytic core of the Rothaus linearization argument.

*Reference*: Bakry-Gentil-Ledoux, *Analysis and Geometry of Markov Diffusion
Operators*, proof of Proposition 5.1.3. -/
theorem entropy_quadratic_lower (f : X → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (2 - ε) * t ^ 2 * variance f ≤
        entropy (fun x => (1 + t * (f x - ∫ y, f y ∂ds.μ)) *
                          (1 + t * (f x - ∫ y, f y ∂ds.μ))) := by
  sorry

/-- **Rothaus entropy-variance inequality** (analytic core).

For a probability measure μ and function f, let g(x) = f(x) - ∫f dμ be
the mean-zero part. For any ε > 0, there exists δ > 0 such that for
0 < t < δ:

  (2 - ε) · t² · Var(f) ≤ Ent((1 + t·g)²)

where Var(f) = ∫(f - ∫f)² dμ = ∫f² dμ - (∫f dμ)².

This is the second-order Taylor expansion of entropy: as t → 0,
  Ent((1+tg)²) / t² → 2 · Var(f)
which follows from the expansion x·log(x) = (x-1) + ½(x-1)² + O((x-1)³)
applied to x = (1+tg)² = 1 + 2tg + t²g², giving
  (1+tg)² · log((1+tg)²) = 2tg + 2t²g² + O(t³)
and integrating (using ∫g = 0, μ probability) yields Ent = 2t²·Var(f) + O(t³).

Proved by delegation to `entropy_quadratic_lower`.

*Reference*: Bakry-Gentil-Ledoux, *Analysis and Geometry of Markov Diffusion
Operators*, proof of Proposition 5.1.3. -/
theorem rothaus_entropy_expansion (f : X → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (2 - ε) * t ^ 2 * variance f ≤
        entropy (fun x => (1 + t * (f x - ∫ y, f y ∂ds.μ)) *
                          (1 + t * (f x - ∫ y, f y ∂ds.μ))) :=
  entropy_quadratic_lower f ε hε

/-- **Energy of the Rothaus perturbation.**
E(1 + t·g, 1 + t·g) = t² · E(g, g) for any g and t.
Follows from `energy_add_const` and `energy_smul`. -/
theorem energy_rothaus (g : X → ℝ) (t : ℝ) :
    ds.energy (fun x => 1 + t * g x) (fun x => 1 + t * g x) =
      t ^ 2 * ds.energy g g := by
  have h1 : (fun x => 1 + t * g x) = (fun x => (t • g) x + 1) := by
    ext x; simp [Pi.smul_apply]; ring
  rw [h1, energy_add_const, energy_smul]

/-- **LSI implies Poincaré** (Rothaus, 1985; BGL Prop 5.1.3).

A log-Sobolev inequality with constant ρ implies a Poincaré inequality
with the same constant ρ.

The proof uses the Rothaus linearization: apply the LSI to the family
f_t = 1 + t·g for mean-zero g = f - ∫f, expand Ent(f_t²) to second
order in t, and take t → 0.

The analytic core (Taylor expansion of entropy) is isolated in
`rothaus_entropy_expansion`; all algebraic reasoning is fully proved. -/
theorem logSobolev_implies_poincare {ρ : ℝ} (h : SatisfiesLogSobolev (ds := ds) ρ) :
    SatisfiesPoincare (ds := ds) ρ := by
  refine ⟨h.1, fun f => ?_⟩
  -- Goal: variance f ≤ (1 / ρ) * ds.energy f f
  --
  -- Strategy: By contradiction. Assume variance f > (1/ρ) * E(f,f).
  -- Pick ε so that (2-ε) * variance(f) > (2/ρ) * E(f,f).
  -- The Rothaus lemma gives t with (2-ε)*t²*Var ≤ Ent((1+tg)²).
  -- LSI gives Ent((1+tg)²) ≤ (2/ρ)*E(1+tg,1+tg) = (2/ρ)*t²*E(f,f).
  -- Combining and cancelling t² gives (2-ε)*Var ≤ (2/ρ)*E(f,f).
  -- With our choice of ε, this gives Var ≤ (1/ρ)*E(f,f). Contradiction.
  by_contra h_neg
  push Not at h_neg
  -- h_neg : (1 / ρ) * ds.energy f f < variance f
  set V := variance f with hV_def
  set E := ds.energy f f with hE_def
  -- If V ≤ 0 then immediate contradiction since (1/ρ)*E ≥ 0
  by_cases hV : V ≤ 0
  · have : 0 ≤ 1 / ρ * E :=
      mul_nonneg (le_of_lt (div_pos one_pos h.1)) (ds.energy_nonneg f)
    linarith
  · push Not at hV
    -- V > 0 and V > (1/ρ)*E
    have hρ_pos := h.1
    -- Express 2/ρ in terms of 1/ρ so linarith can work
    have h2ρ : 2 / ρ = 2 * (1 / ρ) := by ring
    have h_inv_pos : (0 : ℝ) < 1 / ρ := div_pos one_pos hρ_pos
    -- Since V > (1/ρ)*E, we get 2*V > 2*(1/ρ)*E = (2/ρ)*E
    have gap_pos : 0 < 2 * V - 2 / ρ * E := by rw [h2ρ]; nlinarith
    set ε := (2 * V - 2 / ρ * E) / (2 * V) with hε_def
    have hε_pos : 0 < ε := div_pos gap_pos (by linarith)
    -- Get δ from the entropy expansion
    obtain ⟨δ, hδ_pos, hδ⟩ := rothaus_entropy_expansion f ε hε_pos
    -- Pick t = δ / 2
    set t := δ / 2 with ht_def
    have ht_pos : 0 < t := by linarith
    have ht_lt : t < δ := by linarith
    -- From rothaus_entropy_expansion:
    -- (2-ε) * t² * V ≤ Ent((1 + t*(f - ∫f))²)
    have h_ent_lb := hδ t ht_pos ht_lt
    -- From LSI applied to (fun x => 1 + t * (f x - ∫f)):
    set g := fun x => f x - ∫ y, f y ∂ds.μ with hg_def
    have h_lsi := h.2 (fun x => 1 + t * g x)
    -- E(1 + t*g, 1 + t*g) = t² * E(g, g) by energy_rothaus
    rw [energy_rothaus g t] at h_lsi
    -- E(g,g) = E(f,f) by energy_add_const
    have henergy_g : ds.energy g g = E := by
      show ds.energy g g = ds.energy f f
      have hg_eq : g = fun x => f x + (-(∫ y, f y ∂ds.μ)) := by
        ext x; simp [hg_def, sub_eq_add_neg]
      rw [hg_eq, energy_add_const]
    rw [henergy_g] at h_lsi
    -- Match the function in h_ent_lb and h_lsi
    have h_match : (fun x => (1 + t * g x) * (1 + t * g x)) =
        (fun x => (1 + t * (f x - ∫ y, f y ∂ds.μ)) *
                  (1 + t * (f x - ∫ y, f y ∂ds.μ))) := by
      ext x; simp [hg_def]
    rw [h_match] at h_lsi
    -- Combining: (2-ε)*t²*V ≤ Ent(...) ≤ (2/ρ)*(t²*E)
    have combined : (2 - ε) * t ^ 2 * V ≤ 2 / ρ * (t ^ 2 * E) :=
      le_trans h_ent_lb h_lsi
    -- Cancel t² > 0 to get (2-ε)*V ≤ (2/ρ)*E
    have ht2_pos : (0 : ℝ) < t ^ 2 := sq_pos_of_pos ht_pos
    have step1 : (2 - ε) * V ≤ 2 / ρ * E := by nlinarith
    -- Compute (2-ε)*V = V + (1/ρ)*E
    have hV_ne : V ≠ 0 := ne_of_gt hV
    have ε_calc : (2 - ε) * V = V + 1 / ρ * E := by
      rw [hε_def]; field_simp; ring
    -- So V + (1/ρ)*E ≤ (2/ρ)*E, hence V ≤ (1/ρ)*E
    rw [h2ρ] at step1
    linarith [ε_calc]

end DirichletSpace

end
