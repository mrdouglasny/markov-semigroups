/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Validation theorems for the Gaussian1D Bakry-Émery instance

Test theorems that *exercise* the definitions in `Euclidean.lean` on
concrete functions, validating that:

A. The Mehler integral `ouSemigroup` evaluates correctly on the
   first three Hermite polynomials (constants, `x`, `x² − 1`),
   producing the textbook eigenvalues `1`, `e^{−t}`, `e^{−2t}`.
   These proofs use only Mathlib's Gaussian moments, NOT any of the
   four atomic axioms in `Euclidean.lean`.

B. A concrete bounded smooth function (`f = cos`) lies in `IsCore`,
   and the abstract `bakryEmerySpace.satisfiesPoincare` /
   `variance_decay` consequences produce numerical inequalities on it
   with curvature `ρ = 1`.

C. A *conditional* coherence check: assuming a `LogConcaveMeasure ℝ`
   with `V(x) = x²/2` and `μ = γ`, the Brascamp–Lieb route to
   Gaussian Poincaré with `ρ = 1` agrees with what `satisfiesPoincare`
   delivers via Bakry–Émery on the same `γ`.

## References

- BGL Ch. 2 (Mehler/OU eigenfunctions)
- BGL §4.9 (Brascamp–Lieb)
-/

import MarkovSemigroups.Instances.WorkInProgress.Euclidean
import MarkovSemigroups.Instances.WorkInProgress.EuclideanStein
import MarkovSemigroups.Instances.BrascampLieb

open MeasureTheory ProbabilityTheory Filter Set Real

noncomputable section

namespace Gaussian1D

/-! ## A. Hermite eigenfunction tests for the Mehler kernel -/

/-- **Mehler eigenfunction, degree 0.** Constants are fixed:
    `P_t · 1 = 1`. -/
theorem ouSemigroup_const (t x c : ℝ) :
    ouSemigroup t (fun _ => c) x = c := by
  simp [ouSemigroup, integral_const]

/-- **Mehler eigenfunction, degree 1 (Hermite `H₁(x) = x`).**

For all `t ≥ 0`,
  `P_t (id) (x) = e^{−t} · x`.

The OU semigroup contracts `x` by the spectral factor `e^{−t}`,
confirming that the linear function is an eigenfunction with
eigenvalue `e^{−t}` (the first nontrivial Hermite eigenvalue). -/
theorem ouSemigroup_id (t x : ℝ) :
    ouSemigroup t (fun y => y) x = Real.exp (-t) * x := by
  -- Unfold the Mehler integral.
  show ∫ y, (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ
      = Real.exp (-t) * x
  set a := Real.exp (-t) with ha
  set b := Real.sqrt (1 - Real.exp (-2 * t)) with hb
  have h_int_const : Integrable (fun _ : ℝ => a * x) γ := integrable_const _
  have h_memLp_id : MemLp (id : ℝ → ℝ) 1 γ := memLp_id_gaussianReal 1
  have h_int_id : Integrable (fun y : ℝ => y) γ := h_memLp_id.integrable le_rfl
  have h_int_by : Integrable (fun y : ℝ => b * y) γ := h_int_id.const_mul b
  rw [integral_add h_int_const h_int_by, integral_const, integral_const_mul]
  -- ∫ y dγ = 0 (γ has mean 0)
  have h_mean : ∫ y, y ∂γ = 0 := by simp [γ, integral_id_gaussianReal]
  rw [h_mean]
  simp

/-- Helper: the second moment of the standard Gaussian. `∫ y² dγ = 1`.

Derived from `variance_id_gaussianReal` (= `1`) and `variance_eq_sub`
combined with `integral_id_gaussianReal` (= `0`). -/
theorem integral_sq_γ : ∫ y, y ^ 2 ∂γ = 1 := by
  have hmem : MemLp (id : ℝ → ℝ) 2 γ := memLp_id_gaussianReal' 2 (by simp)
  have hvar : Var[id; γ] = 1 := by simp [γ, variance_id_gaussianReal]
  have hmean : ∫ y, y ∂γ = 0 := by simp [γ, integral_id_gaussianReal]
  have hsub := variance_eq_sub (μ := γ) (X := id) hmem
  -- hsub : Var[id; γ] = γ[id^2] − γ[id]^2
  -- Convert γ[id^2] (which unfolds via Pi.pow) to ∫ y, y^2 ∂γ.
  have hid_sq : (γ[(id : ℝ → ℝ) ^ 2] : ℝ) = ∫ y, y ^ 2 ∂γ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (id ^ 2 : ℝ → ℝ) y = y ^ 2
    simp [Pi.pow_apply, sq]
  have hid_mean : (γ[(id : ℝ → ℝ)] : ℝ) = 0 := by
    simp [γ, integral_id_gaussianReal]
  rw [hid_sq, hid_mean] at hsub
  linarith

/-- **Mehler eigenfunction, degree 2 (Hermite `H₂(x) = x² − 1`).**

For all `t ≥ 0`,
  `P_t (y ↦ y² − 1) (x) = e^{−2t} · (x² − 1)`.

The OU semigroup contracts the rescaled second Hermite polynomial by
`e^{−2t}`, confirming the eigenvalue `e^{−2t}`. This is the central
identity behind the Mehler kernel expansion. -/
theorem ouSemigroup_hermite_two (t x : ℝ) (ht : 0 ≤ t) :
    ouSemigroup t (fun y => y ^ 2 - 1) x =
      Real.exp (-2 * t) * (x ^ 2 - 1) := by
  set a := Real.exp (-t) with ha
  set b := Real.sqrt (1 - Real.exp (-2 * t)) with hb
  have hb_sq : b ^ 2 = 1 - Real.exp (-2 * t) :=
    Real.sq_sqrt (one_sub_exp_nonneg t ht)
  have ha_sq : a ^ 2 = Real.exp (-2 * t) := by
    show Real.exp (-t) ^ 2 = Real.exp (-2 * t)
    rw [show (-2 * t : ℝ) = -t + -t from by ring, Real.exp_add]; ring
  show ∫ y, ((a * x + b * y) ^ 2 - 1) ∂γ = Real.exp (-2 * t) * (x ^ 2 - 1)
  -- Integrability of each polynomial component.
  have h_int_const : Integrable (fun _ : ℝ => a ^ 2 * x ^ 2 - 1) γ :=
    integrable_const _
  have h_int_id : Integrable (fun y : ℝ => y) γ :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have h_int_lin : Integrable (fun y : ℝ => (2 * a * b * x) * y) γ :=
    h_int_id.const_mul _
  have h_memLp2 : MemLp (fun y : ℝ => y) 2 γ := memLp_id_gaussianReal' 2 (by simp)
  have h_int_sq : Integrable (fun y : ℝ => y ^ 2) γ := h_memLp2.integrable_sq
  have h_int_quad : Integrable (fun y : ℝ => b ^ 2 * y ^ 2) γ :=
    h_int_sq.const_mul _
  -- Rewrite the integrand as a literal sum.
  have h_expand : (fun y : ℝ => (a * x + b * y) ^ 2 - 1) =
      (fun y => (a ^ 2 * x ^ 2 - 1) + (2 * a * b * x) * y + b ^ 2 * y ^ 2) := by
    funext y; ring
  rw [show (∫ y, ((a * x + b * y) ^ 2 - 1) ∂γ) =
        ∫ y, (a ^ 2 * x ^ 2 - 1) + (2 * a * b * x) * y + b ^ 2 * y ^ 2 ∂γ from by
      rw [h_expand]]
  -- Split the integral via additivity. Use named `f`, `g` to keep
  -- the rewrite pattern β-reduced.
  have h_int_sum : Integrable
      (fun y : ℝ => (a ^ 2 * x ^ 2 - 1) + (2 * a * b * x) * y) γ :=
    h_int_const.add h_int_lin
  rw [integral_add (μ := γ)
        (f := fun y => (a ^ 2 * x ^ 2 - 1) + (2 * a * b * x) * y)
        (g := fun y => b ^ 2 * y ^ 2) h_int_sum h_int_quad,
      integral_add (μ := γ)
        (f := fun _ => (a ^ 2 * x ^ 2 - 1))
        (g := fun y => (2 * a * b * x) * y) h_int_const h_int_lin,
      integral_const, integral_const_mul, integral_const_mul]
  have h_mean : ∫ y, y ∂γ = 0 := by simp [γ, integral_id_gaussianReal]
  rw [h_mean, integral_sq_γ]
  -- Goal: γ.real univ • (a²x² − 1) + 2abx · 0 + b² · 1 = exp(-2t) · (x² − 1)
  have h_univ : γ.real Set.univ = 1 := by
    show (γ Set.univ).toReal = 1
    rw [measure_univ]; rfl
  rw [h_univ, ha_sq, hb_sq]
  simp only [one_smul]
  ring

/-! ### Cube-moment helpers for `H₃` -/

/-- The function `y ↦ y³` is integrable under the standard Gaussian. -/
theorem integrable_cube_γ : Integrable (fun y : ℝ => y ^ 3) γ := by
  have hmem : MemLp (fun y : ℝ => y) 3 γ := memLp_id_gaussianReal' 3 (by simp)
  have h : Integrable (fun y : ℝ => ‖y‖ ^ 3) γ :=
    hmem.integrable_norm_pow (p := 3) (by norm_num)
  refine Integrable.mono' h
    ((measurable_id.pow_const 3).aestronglyMeasurable) ?_
  filter_upwards with y
  -- ‖y^3‖ = |y^3| = |y|^3 = ‖y‖^3.
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]

/-- **Third moment of the standard Gaussian is zero.**
    `∫ y³ dγ = 0` by the `y ↦ −y` symmetry of `γ = N(0,1)`. -/
theorem integral_cube_γ : ∫ y, y ^ 3 ∂γ = 0 := by
  have h_sym : γ.map (fun y : ℝ => -y) = γ := by
    show (gaussianReal 0 1).map (fun y => -y) = gaussianReal 0 1
    rw [gaussianReal_map_neg]; congr 1; simp
  -- ∫ y^3 dγ = ∫ y^3 d(γ.map neg) = ∫ (-y)^3 dγ = -∫ y^3 dγ
  have h_change : ∫ y, y ^ 3 ∂γ = ∫ y, (-y) ^ 3 ∂γ := by
    conv_lhs => rw [← h_sym]
    exact integral_map measurable_neg.aemeasurable
      ((measurable_id.pow_const 3).aestronglyMeasurable)
  have h_neg_pow : (fun y : ℝ => (-y) ^ 3) = fun y => -(y ^ 3) := by
    funext y; ring
  rw [h_neg_pow, integral_neg] at h_change
  linarith

/-- **Mehler eigenfunction, degree 3 (Hermite `H₃(x) = x³ − 3x`).**

For all `t ≥ 0`,
  `P_t (y ↦ y³ − 3y) (x) = e^{−3t} · (x³ − 3x)`.

Confirms the third Hermite eigenvalue `e^{−3t}`. Uses the second
moment `∫y² dγ = 1` and the third moment `∫y³ dγ = 0` (by symmetry). -/
theorem ouSemigroup_hermite_three (t x : ℝ) (ht : 0 ≤ t) :
    ouSemigroup t (fun y => y ^ 3 - 3 * y) x =
      Real.exp (-3 * t) * (x ^ 3 - 3 * x) := by
  set a := Real.exp (-t) with ha
  set b := Real.sqrt (1 - Real.exp (-2 * t)) with hb
  have hb_sq : b ^ 2 = 1 - Real.exp (-2 * t) :=
    Real.sq_sqrt (one_sub_exp_nonneg t ht)
  have ha_sq : a ^ 2 = Real.exp (-2 * t) := by
    show Real.exp (-t) ^ 2 = Real.exp (-2 * t)
    rw [show (-2 * t : ℝ) = -t + -t from by ring, Real.exp_add]; ring
  have ha_cube : a ^ 3 = Real.exp (-3 * t) := by
    show Real.exp (-t) ^ 3 = Real.exp (-3 * t)
    rw [show (-3 * t : ℝ) = -t + -t + -t from by ring,
        Real.exp_add, Real.exp_add]; ring
  show ∫ y, ((a * x + b * y) ^ 3 - 3 * (a * x + b * y)) ∂γ
      = Real.exp (-3 * t) * (x ^ 3 - 3 * x)
  -- Constants in y (degree-0 coefficient), linear, quadratic, cubic.
  set C0 : ℝ := a ^ 3 * x ^ 3 - 3 * a * x with hC0
  set C1 : ℝ := 3 * a ^ 2 * b * x ^ 2 - 3 * b with hC1
  set C2 : ℝ := 3 * a * b ^ 2 * x with hC2
  set C3 : ℝ := b ^ 3 with hC3
  -- Polynomial expansion.
  have h_expand : (fun y : ℝ => (a * x + b * y) ^ 3 - 3 * (a * x + b * y)) =
      (fun y => C0 + C1 * y + C2 * y ^ 2 + C3 * y ^ 3) := by
    funext y; simp only [C0, C1, C2, C3]; ring
  -- Integrability of each piece.
  have h_int_C0 : Integrable (fun _ : ℝ => C0) γ := integrable_const _
  have h_int_id : Integrable (fun y : ℝ => y) γ :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have h_int_lin : Integrable (fun y : ℝ => C1 * y) γ := h_int_id.const_mul _
  have h_memLp2 : MemLp (fun y : ℝ => y) 2 γ := memLp_id_gaussianReal' 2 (by simp)
  have h_int_sq : Integrable (fun y : ℝ => y ^ 2) γ := h_memLp2.integrable_sq
  have h_int_quad : Integrable (fun y : ℝ => C2 * y ^ 2) γ := h_int_sq.const_mul _
  have h_int_cube : Integrable (fun y : ℝ => C3 * y ^ 3) γ :=
    integrable_cube_γ.const_mul _
  -- Partial sums for the iterated additivity.
  have h_int_S1 : Integrable (fun y : ℝ => C0 + C1 * y) γ :=
    h_int_C0.add h_int_lin
  have h_int_S2 : Integrable (fun y : ℝ => C0 + C1 * y + C2 * y ^ 2) γ :=
    h_int_S1.add h_int_quad
  -- Rewrite the integrand into the expanded form.
  rw [show (∫ y, ((a * x + b * y) ^ 3 - 3 * (a * x + b * y)) ∂γ) =
        ∫ y, C0 + C1 * y + C2 * y ^ 2 + C3 * y ^ 3 ∂γ from by rw [h_expand]]
  -- Split the integral additively, left-associated.
  rw [integral_add (μ := γ)
        (f := fun y => C0 + C1 * y + C2 * y ^ 2) (g := fun y => C3 * y ^ 3)
        h_int_S2 h_int_cube,
      integral_add (μ := γ)
        (f := fun y => C0 + C1 * y) (g := fun y => C2 * y ^ 2)
        h_int_S1 h_int_quad,
      integral_add (μ := γ)
        (f := fun _ => C0) (g := fun y => C1 * y)
        h_int_C0 h_int_lin,
      integral_const, integral_const_mul, integral_const_mul, integral_const_mul]
  have h_mean : ∫ y, y ∂γ = 0 := by simp [γ, integral_id_gaussianReal]
  rw [h_mean, integral_sq_γ, integral_cube_γ]
  have h_univ : γ.real Set.univ = 1 := by
    show (γ Set.univ).toReal = 1
    rw [measure_univ]; rfl
  rw [h_univ]
  simp only [one_smul, mul_zero, add_zero, mul_one]
  -- Goal: C0 + C2 = exp(-3t) * (x³ − 3x).
  -- C0 + C2 = a³x³ − 3ax + 3ab²x = a³x³ + 3ax(b² − 1)
  --        = a³x³ − 3ax·exp(-2t) = exp(-3t)·x³ − 3·exp(-3t)·x.
  show C0 + C2 = Real.exp (-3 * t) * (x ^ 3 - 3 * x)
  simp only [C0, C2]
  have h_a_e2t : a * Real.exp (-2 * t) = Real.exp (-3 * t) := by
    show Real.exp (-t) * Real.exp (-2 * t) = Real.exp (-3 * t)
    rw [← Real.exp_add]; congr 1; ring
  have hb_minus_one : b ^ 2 - 1 = -Real.exp (-2 * t) := by
    rw [hb_sq]; ring
  -- a³x³ − 3ax + 3ab²x = a³x³ + 3ax(b² − 1) + 0 = a³x³ + 3ax·(−exp(-2t))
  have key : a ^ 3 * x ^ 3 - 3 * a * x + 3 * a * b ^ 2 * x =
      a ^ 3 * x ^ 3 - 3 * a * Real.exp (-2 * t) * x := by
    have : 3 * a * b ^ 2 * x = 3 * a * x + 3 * a * x * (b ^ 2 - 1) := by ring
    rw [this, hb_minus_one]; ring
  rw [key, ha_cube]
  -- Goal: exp(-3t)·x³ − 3·a·exp(-2t)·x = exp(-3t)·(x³ − 3x).
  linear_combination (-3 * x) * h_a_e2t

/-! ## B. Concrete Poincaré + variance decay on `cos` -/

/-- The cosine function lies in `IsCore`: it is `C^∞` with all
derivatives bounded by `1`. -/
theorem cos_isCore : IsCore Real.cos := by
  refine ⟨Real.contDiff_cos, ⟨1, fun x => ?_⟩⟩
  have h_cos : ‖Real.cos x‖ ≤ 1 := by
    rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one x
  have h_dcos : deriv Real.cos = fun y => -Real.sin y := by
    funext y; exact Real.deriv_cos
  have h_d2cos : deriv (deriv Real.cos) = fun y => -Real.cos y := by
    rw [h_dcos]
    funext y
    have h1 : HasDerivAt (fun z => -Real.sin z) (-Real.cos y) y := by
      have := (Real.hasDerivAt_sin y).neg
      simpa using this
    exact h1.deriv
  refine ⟨h_cos, ?_, ?_⟩
  · rw [h_dcos]
    have : ‖-Real.sin x‖ ≤ 1 := by
      rw [norm_neg, Real.norm_eq_abs]; exact Real.abs_sin_le_one x
    exact this
  · rw [h_d2cos]
    have : ‖-Real.cos x‖ ≤ 1 := by
      rw [norm_neg, Real.norm_eq_abs]; exact Real.abs_cos_le_one x
    exact this

/-- **Concrete Poincaré on `cos`.** PROVED via
`bakryEmerySpace.satisfiesPoincare` with `ρ = 1`.

  `Var_γ(cos) ≤ ∫ sin² dγ`.

This validates that the abstract Bakry–Émery Poincaré theorem, applied
to the concrete `Gaussian1D.bakryEmerySpace` instance, delivers the
expected pointwise gradient bound `(cos)' = -sin ⇒ (cos)'² = sin²`. -/
theorem cos_poincare :
    DirichletSpace.variance (ds := dirichletSpace) Real.cos ≤
      ∫ x, Real.sin x ^ 2 ∂γ := by
  have hP := bakryEmerySpace.satisfiesPoincare.2 Real.cos cos_isCore
  -- The Bakry-Émery energy on cos equals ∫ (cos)'² dγ = ∫ sin² dγ.
  -- bakryEmerySpace.toDirichletSpace.energy = ouEnergy by definition.
  have h_energy_eq :
      bakryEmerySpace.toDirichletSpace.energy Real.cos Real.cos =
        ∫ x, Real.sin x ^ 2 ∂γ := by
    show ouEnergy Real.cos Real.cos = ∫ x, Real.sin x ^ 2 ∂γ
    simp only [ouEnergy]
    have h_dcos : deriv Real.cos = fun y => -Real.sin y := by
      funext y; exact Real.deriv_cos
    rw [h_dcos]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (-Real.sin x) * (-Real.sin x) = Real.sin x ^ 2
    ring
  -- bakryEmerySpace.ρ = 1, so the constant collapses.
  have h_one : (1 : ℝ) / bakryEmerySpace.ρ = 1 := by
    show (1 : ℝ) / 1 = 1; norm_num
  rw [h_one, one_mul, h_energy_eq] at hP
  exact hP

/-- **Concrete variance decay on `cos`.** PROVED via
`bakryEmerySpace.variance_decay` with `ρ = 1`.

  `Var_γ(P_t cos) ≤ e^{−2t} · Var_γ(cos)`.

Validates that the OU semigroup mixes `cos` exponentially fast. -/
theorem cos_variance_decay (t : ℝ) (ht : 0 ≤ t) :
    DirichletSpace.variance (ds := dirichletSpace)
        (ouSemigroup t Real.cos) ≤
      Real.exp (-2 * t) *
        DirichletSpace.variance (ds := dirichletSpace) Real.cos := by
  have h := bakryEmerySpace.variance_decay Real.cos t ht cos_isCore
  -- bakryEmerySpace.ρ = 1, semigroup = ouSemigroup.
  have h_rho : bakryEmerySpace.ρ = 1 := rfl
  have h_sem : bakryEmerySpace.semigroup = ouSemigroup := rfl
  rw [h_rho, h_sem] at h
  -- Tidy the exponent: -2 * 1 * t = -2 * t.
  have h_exp : Real.exp (-2 * 1 * t) = Real.exp (-2 * t) := by
    congr 1; ring
  rw [h_exp] at h
  exact h

/-! ## C. Brascamp–Lieb on γ recovers Gaussian Poincaré -/

/-- Conditional coherence: if we are given a `LogConcaveMeasure ℝ` whose
underlying measure is `γ` and whose potential satisfies the Gaussian
uniform-convexity bound `(Hess V)(v,v) ≥ ‖v‖²` (i.e. `ρ = 1`), then
the Brascamp–Lieb route delivers the Gaussian Poincaré inequality with
the same constant that the Bakry–Émery route gives. -/
theorem brascampLieb_recovers_gaussian_poincare
    (m : LogConcaveMeasure ℝ)
    (hμ : m.μ = γ)
    (hρ : ∀ x v : ℝ, ‖v‖ ^ 2 ≤ hessianBilin m.V x v v)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hf_grad_int : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) m.μ)
    (hH_int : ∀ u : ℝ → ℝ, Integrable (fun x =>
      hessianBilin m.V x (gradient u x) (gradient u x)) m.μ) :
    m.variance f ≤ ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂γ := by
  -- Apply brascampLieb_poincare with ρ = 1.
  have hBL := m.brascampLieb_poincare 1 one_pos
    (fun x v => by simpa [one_mul] using hρ x v)
    f hf hf_grad_int hH_int
  -- 1 / 1 = 1, μ = γ ⇒ collapse the constants.
  rw [hμ] at hBL
  simpa using hBL

/-! ### Unconditional Gaussian LogConcaveMeasure instance

The standard Gaussian `γ = N(0,1)` on `ℝ` with potential `V(x) = x²/2`
forms a `LogConcaveMeasure ℝ`. The decomposition:

* **Constructive (provable from Mathlib):**
  - `V_gauss := fun x => x²/2`, `ContDiff ℝ 2 V_gauss`.
  - The Hessian bilinear form: `hessianBilin V_gauss x v w = v * w`.
  - Strict convexity / uniform curvature `‖v‖² ≤ Hess V(v, v)`.

* **Axiomatized (textbook Gaussian/OU theory, BGL §1.15-§1.16):**
  - `gaussianResolvent`: the function `u = (I − L)⁻¹(f − ⟨f⟩)` with
    `L = d²/dx² − x·d/dx` (Lax-Milgram on the OU Dirichlet form).
  - `gaussianResolvent_ibp`: Stein's identity `Var_γ(f) = ∫ f'·u' dγ`.
  - `gaussianResolvent_ibp_integrable`: integrand is integrable.
  - `gaussianBochner_identity`: integrated Bochner-Weitzenböck.

Net: 4 named axioms (replacing 1 monolithic existence axiom) — each
covers one textbook ingredient with a clear BGL citation. The
remaining LCM structure fields are filled constructively. -/

/-- The Gaussian potential `V(x) = x²/2`. -/
def V_gauss : ℝ → ℝ := fun x => x ^ 2 / 2

theorem hasDerivAt_V_gauss (x : ℝ) : HasDerivAt V_gauss x x := by
  have h₁ : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h₂ := h₁.div_const 2
  convert h₂ using 1; ring

theorem contDiff_V_gauss : ContDiff ℝ 2 V_gauss := by
  unfold V_gauss; fun_prop

/-- The continuous linear equivalence `ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)` sending
`x` to the multiplication-by-`x` map. The fderiv of `V_gauss` is
exactly this CLE (as a function), and since it is itself linear, its
own fderiv is the constant CLE. -/
noncomputable def toSpanCLE_ℝ : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ) :=
  (ContinuousLinearMap.toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ))

theorem fderiv_V_gauss : fderiv ℝ V_gauss = toSpanCLE_ℝ := by
  funext y
  have : fderiv ℝ V_gauss y = ContinuousLinearMap.toSpanSingleton ℝ y :=
    (hasDerivAt_V_gauss y).hasFDerivAt.fderiv
  rw [this]; rfl

/-- **The Hessian of `V_gauss = x²/2` is the identity bilinear form.**
`hessianBilin V_gauss x v w = v * w`. PROVED. -/
theorem hessianBilin_V_gauss (x v w : ℝ) :
    hessianBilin V_gauss x v w = v * w := by
  show ((fderiv ℝ (fderiv ℝ V_gauss) x) v) w = v * w
  -- fderiv (fderiv V_gauss) x = toSpanCLE_ℝ (the CLE is its own fderiv).
  have h2 : HasFDerivAt (fderiv ℝ V_gauss) toSpanCLE_ℝ.toContinuousLinearMap x := by
    rw [fderiv_V_gauss]
    exact toSpanCLE_ℝ.toContinuousLinearMap.hasFDerivAt
  rw [h2.fderiv]
  -- Goal: ((toSpanCLE_ℝ.toContinuousLinearMap : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ)) v) w = v * w
  show ((toSpanCLE_ℝ : ℝ → (ℝ →L[ℝ] ℝ)) v) w = v * w
  show (ContinuousLinearMap.toSpanSingleton ℝ v) w = v * w
  rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]

/-- **Strict convexity of `V_gauss`.** PROVED from `hessianBilin_V_gauss`. -/
theorem hV_gauss_convex (x v : ℝ) (hv : v ≠ 0) :
    (0 : ℝ) < hessianBilin V_gauss x v v := by
  rw [hessianBilin_V_gauss]
  exact mul_self_pos.mpr hv

/-- **Uniform curvature `ρ = 1` for `V_gauss`.** PROVED:
`‖v‖² ≤ hessianBilin V_gauss x v v` (with equality). -/
theorem hV_gauss_curvature (x v : ℝ) :
    ‖v‖ ^ 2 ≤ hessianBilin V_gauss x v v := by
  rw [hessianBilin_V_gauss, Real.norm_eq_abs, sq_abs, sq]

/-! ### Textbook axioms: the OU resolvent and its identities

These four axioms package the standard Gaussian OU resolvent theory
(BGL §1.15-1.16) for the `LogConcaveMeasure ℝ` fields. The full
discharge requires:
- Lax-Milgram on the Gaussian Dirichlet form `E(f, g) = ∫ f' g' dγ`
  to construct the resolvent.
- Stein's integration-by-parts identity for the Gaussian.
- The integrated Bochner-Weitzenböck identity for the OU generator. -/

/-- **OU resolvent for the Gaussian.** Sends a `C¹` function `f` to
the solution `u` of `Lu = -(f - ⟨f⟩_γ)` where `L = d²/dx² - x·d/dx`.

Reference: BGL §1.15 (Lax-Milgram on the OU Dirichlet form). -/
axiom gaussianResolvent : (ℝ → ℝ) → (ℝ → ℝ)

/-- **Resolvent integration by parts (Stein's identity).**
`Var_γ(f) = ∫ ⟨∇f, ∇u⟩ dγ` where `u = gaussianResolvent f`.

Reference: BGL §1.15; the Gaussian weighted divergence theorem. -/
axiom gaussianResolvent_ibp (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    (∫ x, (f x) ^ 2 ∂γ) - (∫ x, f x ∂γ) ^ 2 =
      ∫ x, (fderiv ℝ f x) (gradient (gaussianResolvent f) x) ∂γ

/-- **Integrability of the resolvent IBP integrand.** -/
axiom gaussianResolvent_ibp_integrable (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    Integrable
      (fun x => (fderiv ℝ f x) (gradient (gaussianResolvent f) x)) γ

/-- **Integrated Bochner-Weitzenböck identity (BGL §1.16).**

If `Var(f) = ∫ ⟨∇f, ∇u⟩ dγ` then `Var(f) = R + ∫ Hess V(∇u, ∇u) dγ`
for some `R ≥ 0` (where `R = ∫ ‖Hess u‖² dγ`).

Reference: BGL §1.16; pointwise Bochner formula
`½L(|∇u|²) = ⟨∇u, ∇(Lu)⟩ + ‖Hess u‖² + Hess V(∇u, ∇u)` integrated
against `γ` with `∫ Lh dγ = 0` and `Lu = -(f - ⟨f⟩)`. -/
axiom gaussianBochner_identity (f : ℝ → ℝ) (u : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hu : (∫ x, (f x) ^ 2 ∂γ) - (∫ x, f x ∂γ) ^ 2 =
          ∫ x, (fderiv ℝ f x) (gradient u x) ∂γ) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∫ x, (f x) ^ 2 ∂γ) - (∫ x, f x ∂γ) ^ 2 =
        R + ∫ x, hessianBilin V_gauss x (gradient u x) (gradient u x) ∂γ

/-- **The canonical Gaussian `LogConcaveMeasure ℝ` instance.**
Constructive: `V = x²/2` with computed Hessian; only the resolvent
fields are populated from the four named axioms above. -/
noncomputable def gaussianLogConcaveMeasure : LogConcaveMeasure ℝ where
  V := V_gauss
  hV_diff := contDiff_V_gauss
  hV_convex := hV_gauss_convex
  μ := γ
  hμ_prob := inferInstance
  resolvent := gaussianResolvent
  resolvent_ibp := gaussianResolvent_ibp
  resolvent_ibp_integrable := gaussianResolvent_ibp_integrable
  bochner_identity := gaussianBochner_identity

theorem gaussianLogConcaveMeasure_μ : gaussianLogConcaveMeasure.μ = γ := rfl

theorem gaussianLogConcaveMeasure_V :
    gaussianLogConcaveMeasure.V = V_gauss := rfl

theorem gaussianLogConcaveMeasure_curvature (x v : ℝ) :
    ‖v‖ ^ 2 ≤ hessianBilin gaussianLogConcaveMeasure.V x v v :=
  hV_gauss_curvature x v

/-- **Unconditional Gaussian Brascamp-Lieb / Poincaré.** PROVED from
the single existence axiom `gaussianLogConcaveMeasure_exists`.

  `Var_γ(f) ≤ ∫ ‖f'‖² dγ`

for `C¹` functions `f` with square-integrable gradient under `γ` (and
the technical integrability of `Hess V` applied to gradients of
arbitrary functions, which the BL hypothesis requires).

The variance is stated in the `DirichletSpace`-form `∫f² dγ − (∫f)²`,
matching the abstract Bakry-Émery route. Same constant `1/ρ = 1`,
confirming the two routes agree. -/
theorem gaussian_brascampLieb_poincare
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hf_grad_int : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) γ)
    (hH_int : ∀ u : ℝ → ℝ, Integrable (fun x =>
      hessianBilin gaussianLogConcaveMeasure.V x
        (gradient u x) (gradient u x)) γ) :
    (∫ x, (f x) ^ 2 ∂γ) - (∫ x, f x ∂γ) ^ 2 ≤
      ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂γ := by
  set m := gaussianLogConcaveMeasure with hm
  have hμ : m.μ = γ := gaussianLogConcaveMeasure_μ
  have hρ : ∀ x v : ℝ, ‖v‖ ^ 2 ≤ hessianBilin m.V x v v :=
    gaussianLogConcaveMeasure_curvature
  -- Transport integrability hypotheses to m.μ via μ = γ.
  have hf_grad_int' : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) m.μ := by
    rw [hμ]; exact hf_grad_int
  have hH_int' : ∀ u : ℝ → ℝ, Integrable
      (fun x => hessianBilin m.V x (gradient u x) (gradient u x)) m.μ := by
    intro u; rw [hμ]; exact hH_int u
  -- Apply the BL Poincaré bound with ρ = 1.
  have hBL := m.brascampLieb_poincare 1 one_pos
    (fun x v => by simpa [one_mul] using hρ x v)
    f hf hf_grad_int' hH_int'
  -- m.variance f unfolds to ∫f² − (∫f)² (over m.μ = γ).
  have h_var_eq : m.variance f = (∫ x, (f x) ^ 2 ∂γ) - (∫ x, f x ∂γ) ^ 2 := by
    show (∫ x, (f x) ^ 2 ∂m.μ) - (∫ x, f x ∂m.μ) ^ 2 =
      (∫ x, (f x) ^ 2 ∂γ) - (∫ x, f x ∂γ) ^ 2
    rw [hμ]
  rw [hμ, h_var_eq] at hBL
  simpa using hBL

end Gaussian1D

end
