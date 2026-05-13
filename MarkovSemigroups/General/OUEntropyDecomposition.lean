/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Atomic textbook axioms for the OU entropy decay bound

This file packages **two atomic textbook bridges** for the Gaussian
Ornstein-Uhlenbeck semigroup on `ℝ`:

* `ouSemigroup_fisher_info_decay` — Bakry-Émery gradient decay for the
  Fisher information (BGL Prop 5.5.2, Jensen-on-`x²/y` argument).
* `hasDerivAt_entropy_ouSemigroup` — de Bruijn identity: the entropy
  `∫ g · log g dγ` differentiated under the OU heat flow equals minus
  the Fisher information (BGL §5.5).

Together these two facts (plus FTC and a one-line algebraic identity)
discharge the previous broad axiom `ouSemigroup_entropy_sq_decay_bound`
(BGL Theorem 5.5.2). The discharge lives in
`Instances/WorkInProgress/EuclideanEntropyDecay.lean`.

Both axioms require a positive lower bound `g ≥ ε > 0` on the function;
this is the standard regularization handling `log 0` in the textbook
proof. The application to `f²` proceeds via `g := f² + ε` plus a limit
`ε → 0`.

## Why split into two axioms?

The original axiom bundled "rate identity" + "gradient decay" + "FTC"
into a single statement. Splitting yields:
1. Each piece is a standalone textbook fact, vettable independently.
2. The Fisher info decay (A1) closely parallels `ouSemigroup_gradient_decay`
   which we proved — same Jensen + γ-invariance structure, just with
   `(g')²/g` instead of `(g')²`.
3. The de Bruijn identity (A2) is parametric-integral differentiation
   structurally identical to `hasDerivAt_l2sq_ouSemigroup_pos` which
   we proved — but applied to the `s · log s` integrand instead of
   `s²`.
4. Both axioms are reusable for future `BakryEmerySpace` instances.

## References

* Bakry-Gentil-Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, §5.5 (de Bruijn identity, Fisher information decay,
  entropy decay under Bakry-Émery curvature).
* Bakry-Émery (1985) "Diffusions hypercontractives", §I.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MarkovSemigroups.Instances.WorkInProgress.Euclidean

open MeasureTheory Filter Set Real ProbabilityTheory Topology

open scoped ContDiff

noncomputable section

namespace Gaussian1D

/-- The Fisher information of `g : ℝ → ℝ` against the standard Gaussian:
`I(g) = ∫ (g'(y))² / g(y) dγ(y)`.

For our purposes `g` is bounded below by some `ε > 0`, so the division
is well-defined everywhere. -/
def fisherInfo (g : ℝ → ℝ) : ℝ :=
  ∫ y, (deriv g y) ^ 2 / g y ∂γ

/-- The Boltzmann-style entropy `H(g) = ∫ g · log g dγ` (no `(∫g) log(∫g)`
subtraction at this granularity — the centered version is in
`DirichletSpace.entropy`). For `g ≥ ε > 0`, this is a smooth functional. -/
def boltzmannEntropy (g : ℝ → ℝ) : ℝ :=
  ∫ y, g y * Real.log (g y) ∂γ

/-! ## Cauchy-Schwarz helper -/

/-- **Cauchy-Schwarz inequality for the standard Gaussian measure.**
For functions `A, B : ℝ → ℝ` with `A·B`, `A²`, `B²` all γ-integrable,
`(∫ A·B dγ)² ≤ (∫ A² dγ)·(∫ B² dγ)`.

Proved via the polynomial discriminant: for every `λ ∈ ℝ`,
`0 ≤ ∫ (A - λ·B)² dγ`, then expanded and optimized in `λ`. -/
private lemma cauchy_schwarz_gamma (A B : ℝ → ℝ)
    (hAB : Integrable (fun y => A y * B y) γ)
    (hA2 : Integrable (fun y => A y ^ 2) γ)
    (hB2 : Integrable (fun y => B y ^ 2) γ) :
    (∫ y, A y * B y ∂γ) ^ 2 ≤ (∫ y, A y ^ 2 ∂γ) * (∫ y, B y ^ 2 ∂γ) := by
  set IA := ∫ y, A y ^ 2 ∂γ with hIA
  set IB := ∫ y, B y ^ 2 ∂γ with hIB
  set IAB := ∫ y, A y * B y ∂γ with hIAB
  have hIA_nn : 0 ≤ IA :=
    integral_nonneg (fun y => sq_nonneg _)
  have hIB_nn : 0 ≤ IB :=
    integral_nonneg (fun y => sq_nonneg _)
  by_cases hIB0 : IB = 0
  · -- If ∫B² = 0, then B = 0 a.e., so ∫A·B = 0.
    have hB_ae : (fun y => B y ^ 2) =ᵐ[γ] 0 := by
      have h_nn_ae : ∀ᵐ y ∂γ, 0 ≤ B y ^ 2 :=
        Filter.Eventually.of_forall (fun y => sq_nonneg _)
      exact (integral_eq_zero_iff_of_nonneg_ae h_nn_ae hB2).mp hIB0
    have hAB_ae : (fun y => A y * B y) =ᵐ[γ] 0 := by
      filter_upwards [hB_ae] with y hy
      have : B y = 0 := sq_eq_zero_iff.mp hy
      simp [this]
    have hIAB0 : IAB = 0 := by
      rw [hIAB]; exact integral_eq_zero_of_ae hAB_ae
    rw [hIAB0, hIB0]; simp
  · have hIB_pos : 0 < IB := lt_of_le_of_ne hIB_nn (Ne.symm hIB0)
    -- Optimal λ := IAB / IB makes ∫(A - λB)² = IA - IAB²/IB ≥ 0.
    set lam : ℝ := IAB / IB with h_lam_def
    have h_expand : ∫ y, (A y - lam * B y) ^ 2 ∂γ
        = IA - 2 * lam * IAB + lam ^ 2 * IB := by
      have h_eq : ∀ y, (A y - lam * B y) ^ 2
          = A y ^ 2 - 2 * lam * (A y * B y) + lam ^ 2 * B y ^ 2 := fun y => by ring
      have h_sum_int :
          Integrable (fun y => A y ^ 2 - 2 * lam * (A y * B y) + lam ^ 2 * B y ^ 2) γ :=
        (hA2.sub (hAB.const_mul (2 * lam))).add (hB2.const_mul (lam ^ 2))
      calc ∫ y, (A y - lam * B y) ^ 2 ∂γ
          = ∫ y, A y ^ 2 - 2 * lam * (A y * B y) + lam ^ 2 * B y ^ 2 ∂γ :=
            integral_congr_ae (Filter.Eventually.of_forall h_eq)
        _ = (∫ y, A y ^ 2 - 2 * lam * (A y * B y) ∂γ) + ∫ y, lam ^ 2 * B y ^ 2 ∂γ :=
            integral_add (hA2.sub (hAB.const_mul (2 * lam))) (hB2.const_mul (lam ^ 2))
        _ = ((∫ y, A y ^ 2 ∂γ) - ∫ y, 2 * lam * (A y * B y) ∂γ)
            + ∫ y, lam ^ 2 * B y ^ 2 ∂γ := by
            rw [integral_sub hA2 (hAB.const_mul (2 * lam))]
        _ = IA - 2 * lam * IAB + lam ^ 2 * IB := by
            rw [integral_const_mul, integral_const_mul]
    have h_nn : 0 ≤ ∫ y, (A y - lam * B y) ^ 2 ∂γ :=
      integral_nonneg (fun y => sq_nonneg _)
    rw [h_expand] at h_nn
    -- Rewrite h_nn entirely in terms of IAB²/IB.
    have h_nn' : 0 ≤ IA - IAB ^ 2 / IB := by
      have h_alg : IA - 2 * lam * IAB + lam ^ 2 * IB = IA - IAB ^ 2 / IB := by
        rw [h_lam_def]; field_simp; ring
      linarith [h_alg ▸ h_nn]
    have h_step : IAB ^ 2 / IB ≤ IA := by linarith
    have := mul_le_mul_of_nonneg_right h_step hIB_nn
    rwa [div_mul_cancel₀ _ hIB0] at this

/-! ## A1: Fisher information gradient decay (BGL Prop 5.5.2) -/

/-- **Bakry-Émery gradient decay for the Fisher information.** AXIOM
(vetting-required textbook bridge).

For any `C¹` `g : ℝ → ℝ` with `g, g'` bounded and `g ≥ ε > 0` pointwise,
the Fisher information `I(P_t g)` decays exponentially:

  `I(P_t g) = ∫ ((P_t g)'(y))² / (P_t g)(y) dγ(y)
              ≤ exp(-2t) · ∫ (g'(y))² / g(y) dγ(y) = exp(-2t) · I(g)`.

## Proof in textbooks

Two steps:
1. The Mehler derivative formula gives `(P_t g)'(x) = e^{-t} P_t(g')(x)`
   (already proved as `hasDerivAt_ouSemigroup_C1`).
2. Apply Jensen's inequality to the convex function `φ(x, y) = x² / y`
   on `{y > 0}`:
   `((P_t g)'(x))² / (P_t g)(x) = (e^{-t} P_t(g'))² / P_t(g)
       = e^{-2t} · (P_t(g'))² / (P_t g)
       ≤ e^{-2t} · P_t((g')²/g)`
   by Jensen on the Mehler probability kernel.
3. Integrate against γ and use γ-invariance of P_t (Fubini +
   `ou_kernel_map`):
   `∫ ((P_t g)')² / P_t g dγ ≤ e^{-2t} · ∫ P_t((g')²/g) dγ
       = e^{-2t} · ∫ (g')²/g dγ`.

The Jensen step is the Bakry-Émery curvature condition `Γ₂ ≥ Γ` in
disguise (for OU on ℝ with `ρ = 1`, this curvature bound is exact).

## Discharge plan

Per Gemini 3.1-pro vetting (verdict: **Standard**, 2026-05-12): the
cleanest discharge avoids the 2D-Jensen-on-`x²/y` argument. Instead,
apply Cauchy-Schwarz on the Mehler probability kernel
`μ_x(dy) := P_t(x, dy)`:
  `(P_t g'(x))² = (∫ (g'/√g) · √g dμ_x)²
       ≤ (∫ (g')²/g dμ_x) · (∫ g dμ_x)`
giving `(P_t g'(x))² / P_t g(x) ≤ P_t((g')²/g)(x)`. Then `P_t g'(x) =
e^t · (P_t g)'(x)`... wait — by `hasDerivAt_ouSemigroup_C1`,
`(P_t g)'(x) = e^{-t} · P_t g'(x)`. So
`((P_t g)'(x))² / (P_t g)(x) = e^{-2t} (P_t g')² / P_t g ≤ e^{-2t}
P_t((g')²/g)`. Finally integrate against γ + γ-invariance.

Expected effort: ~150-250 lines (substantially less than the 2D-Jensen
route — most of the work is the Cauchy-Schwarz application + γ-invariance
manipulation).

## References

* Bakry-Gentil-Ledoux, Proposition 5.5.2 and §5.5.
* Bakry-Émery (1985), "Diffusions hypercontractives," Prop. 1.

## Vetting

**Standard** (gemini-3.1-pro-preview, 2026-05-12). Hypotheses tight;
`ε ≤ g ⇒ P_t g ≥ ε` for free since `P_t` averages against a probability
kernel; exponent `exp(-2t)` correct for OU(1) Bakry-Émery curvature
`ρ = 1`. No counterexamples. -/
theorem ouSemigroup_fisher_info_decay
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    {ε M : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hg'_bd : ∀ x, |deriv g x| ≤ M)
    (t : ℝ) (ht : 0 ≤ t) :
    fisherInfo (ouSemigroup t g) ≤ Real.exp (-2 * t) * fisherInfo g := by
  -- Notation
  set a := Real.exp (-t) with ha_def
  set b := Real.sqrt (1 - Real.exp (-2 * t)) with hb_def
  -- Basic facts
  have hε_nn : 0 ≤ ε := hε.le
  have hM_nn : 0 ≤ M := hε_nn.trans ((hg_lo 0).trans (hg_hi 0))
  have ha_pos : 0 < a := Real.exp_pos _
  have ha_nn : 0 ≤ a := ha_pos.le
  have ha_sq : a ^ 2 = Real.exp (-2 * t) := by
    show Real.exp (-t) ^ 2 = Real.exp (-2 * t)
    rw [show (-2 * t : ℝ) = -t + -t from by ring, Real.exp_add]; ring
  have h_gpos : ∀ x, 0 < g x := fun x => lt_of_lt_of_le hε (hg_lo x)
  have h_gabs : ∀ x, |g x| ≤ M := fun x => by
    rw [abs_of_pos (h_gpos x)]; exact hg_hi x
  have hg_norm : ∀ x, ‖g x‖ ≤ M := fun x => by
    rw [Real.norm_eq_abs]; exact h_gabs x
  have hg'_norm : ∀ x, ‖deriv g x‖ ≤ M := fun x => by
    rw [Real.norm_eq_abs]; exact hg'_bd x
  -- Measurability
  have hg_meas : Measurable g := hg.continuous.measurable
  have hg'_meas : Measurable (deriv g) :=
    (hg.continuous_deriv le_rfl).measurable
  -- Linear inner map (a*x + b*y), measurable in y for fixed x.
  -- Set the integrand functions for each fixed x.
  -- P_t g x ≥ ε.
  have h_Ptg_lo : ∀ x, ε ≤ ouSemigroup t g x := by
    intro x
    show ε ≤ ∫ y, g (a * x + b * y) ∂γ
    have h_int : Integrable (fun y => g (a * x + b * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hg_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with y; exact hg_norm _
    have h_le : ∀ y, (ε : ℝ) ≤ g (a * x + b * y) := fun y => hg_lo _
    calc (ε : ℝ) = ∫ _, ε ∂γ := by simp
      _ ≤ ∫ y, g (a * x + b * y) ∂γ :=
            integral_mono (integrable_const _) h_int h_le
  have h_Ptg_pos : ∀ x, 0 < ouSemigroup t g x := fun x =>
    lt_of_lt_of_le hε (h_Ptg_lo x)
  -- P_t g x ≤ M.
  have h_Ptg_hi : ∀ x, ouSemigroup t g x ≤ M := by
    intro x
    show ∫ y, g (a * x + b * y) ∂γ ≤ M
    have h_int : Integrable (fun y => g (a * x + b * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hg_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with y; exact hg_norm _
    calc ∫ y, g (a * x + b * y) ∂γ
        ≤ ∫ _, M ∂γ :=
            integral_mono h_int (integrable_const _) (fun y => hg_hi _)
      _ = M := by simp
  -- Mehler derivative formula.
  have h_deriv : ∀ x,
      HasDerivAt (ouSemigroup t g) (a * ouSemigroup t (deriv g) x) x := fun x =>
    hasDerivAt_ouSemigroup_C1 t hg hg_norm hg'_norm x
  have h_deriv_eq : ∀ x,
      deriv (ouSemigroup t g) x = a * ouSemigroup t (deriv g) x := fun x =>
    (h_deriv x).deriv
  -- Pointwise Cauchy-Schwarz.
  -- For each x: with Q(y) := g'(a*x + b*y), R(y) := g(a*x + b*y),
  -- (∫ Q dγ)² ≤ (∫ Q²/R dγ)·(∫ R dγ), since Q = (Q/√R)·√R and R ≥ ε > 0.
  have h_inv_lin_meas : Measurable (fun p : ℝ × ℝ => a * p.1 + b * p.2) :=
    (measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)
  -- Integrability of (g')²/g composed with kernel, over γ.prod γ.
  -- Bound: |g'|² / g ≤ M² / ε since |g'| ≤ M, g ≥ ε.
  have h_M2eps_nn : 0 ≤ M ^ 2 / ε := div_nonneg (sq_nonneg _) hε_nn
  have h_qsq_over_r_bd : ∀ x, (deriv g x) ^ 2 / g x ≤ M ^ 2 / ε := by
    intro x
    have h1 : (deriv g x) ^ 2 ≤ M ^ 2 := by
      have hxabs : |deriv g x| ≤ M := hg'_bd x
      have : (deriv g x) ^ 2 = |deriv g x| ^ 2 := by rw [sq_abs]
      rw [this]
      exact pow_le_pow_left₀ (abs_nonneg _) hxabs 2
    have h2 : (deriv g x) ^ 2 / g x ≤ (deriv g x) ^ 2 / ε :=
      div_le_div_of_nonneg_left (sq_nonneg _) hε (hg_lo x)
    have h3 : (deriv g x) ^ 2 / ε ≤ M ^ 2 / ε :=
      div_le_div_of_nonneg_right h1 hε_nn
    linarith
  have h_qsq_over_r_nn : ∀ x, 0 ≤ (deriv g x) ^ 2 / g x := fun x =>
    div_nonneg (sq_nonneg _) (h_gpos x).le
  -- Measurability of (deriv g y)² / g y.
  have h_qsq_over_r_meas : Measurable (fun y => (deriv g y) ^ 2 / g y) :=
    (hg'_meas.pow_const 2).div hg_meas
  -- The pointwise Cauchy-Schwarz bound:
  -- (∫ Q dγ)² ≤ (∫ Q²/R dγ) · (∫ R dγ)
  -- where Q(y) := g'(a*x + b*y), R(y) := g(a*x + b*y).
  -- Apply with A := Q/√R, B := √R; then A·B = Q, A² = Q²/R, B² = R.
  -- We need integrability of these functions.
  have h_cauchy : ∀ x,
      (ouSemigroup t (deriv g) x) ^ 2 ≤
        ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x * ouSemigroup t g x := by
    intro x
    -- Define A(y) := g'(a*x+b*y) / √(g(a*x+b*y)), B(y) := √(g(a*x+b*y))
    -- and apply cauchy_schwarz_gamma.
    set A : ℝ → ℝ := fun y => deriv g (a * x + b * y) / Real.sqrt (g (a * x + b * y))
    set B : ℝ → ℝ := fun y => Real.sqrt (g (a * x + b * y))
    have h_compose_pos : ∀ y, 0 < g (a * x + b * y) := fun y => h_gpos _
    have h_compose_lo : ∀ y, ε ≤ g (a * x + b * y) := fun y => hg_lo _
    have h_sqrt_pos : ∀ y, 0 < Real.sqrt (g (a * x + b * y)) := fun y =>
      Real.sqrt_pos.mpr (h_compose_pos y)
    have h_sqrt_sq : ∀ y, (Real.sqrt (g (a * x + b * y))) ^ 2 = g (a * x + b * y) := fun y =>
      Real.sq_sqrt (h_compose_pos y).le
    have h_AB : ∀ y, A y * B y = deriv g (a * x + b * y) := by
      intro y
      show (deriv g (a * x + b * y) / Real.sqrt (g (a * x + b * y))) *
          Real.sqrt (g (a * x + b * y)) = deriv g (a * x + b * y)
      have hsqrt_ne : Real.sqrt (g (a * x + b * y)) ≠ 0 := (h_sqrt_pos y).ne'
      field_simp
    have h_A2 : ∀ y, A y ^ 2 = (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y) := by
      intro y
      show (deriv g (a * x + b * y) / Real.sqrt (g (a * x + b * y))) ^ 2
          = (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y)
      rw [div_pow, h_sqrt_sq]
    have h_B2 : ∀ y, B y ^ 2 = g (a * x + b * y) := h_sqrt_sq
    -- Measurability of A, B.
    have h_kernel_meas : Measurable (fun y => a * x + b * y) :=
      measurable_const.add (measurable_const.mul measurable_id)
    have h_sqrt_meas : Measurable Real.sqrt := Real.continuous_sqrt.measurable
    have hA_meas : Measurable A :=
      (hg'_meas.comp h_kernel_meas).div (h_sqrt_meas.comp (hg_meas.comp h_kernel_meas))
    have hB_meas : Measurable B :=
      h_sqrt_meas.comp (hg_meas.comp h_kernel_meas)
    -- Integrability.
    have h_AB_int : Integrable (fun y => A y * B y) γ := by
      refine Integrable.mono' (integrable_const M)
        (hA_meas.mul hB_meas).aestronglyMeasurable ?_
      filter_upwards with y
      rw [h_AB]
      exact hg'_norm _
    have h_A2_int : Integrable (fun y => A y ^ 2) γ := by
      refine Integrable.mono' (integrable_const (M ^ 2 / ε)) ?_ ?_
      · exact (hA_meas.pow_const 2).aestronglyMeasurable
      · filter_upwards with y
        rw [Real.norm_eq_abs, abs_of_nonneg (by rw [h_A2]; exact h_qsq_over_r_nn _)]
        rw [h_A2]
        exact h_qsq_over_r_bd _
    have h_B2_int : Integrable (fun y => B y ^ 2) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hB_meas.pow_const 2).aestronglyMeasurable
      · filter_upwards with y
        rw [h_B2, Real.norm_eq_abs]
        exact h_gabs _
    have hCS := cauchy_schwarz_gamma A B h_AB_int h_A2_int h_B2_int
    -- Rewrite using h_AB, h_A2, h_B2.
    have h_lhs : (∫ y, A y * B y ∂γ) ^ 2 = (ouSemigroup t (deriv g) x) ^ 2 := by
      congr 1
      show ∫ y, A y * B y ∂γ = ∫ y, deriv g (a * x + b * y) ∂γ
      exact integral_congr_ae (Filter.Eventually.of_forall h_AB)
    have h_rhs_A2 : ∫ y, A y ^ 2 ∂γ
        = ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x := by
      show ∫ y, A y ^ 2 ∂γ = ∫ y, (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y) ∂γ
      exact integral_congr_ae (Filter.Eventually.of_forall h_A2)
    have h_rhs_B2 : ∫ y, B y ^ 2 ∂γ = ouSemigroup t g x := by
      show ∫ y, B y ^ 2 ∂γ = ∫ y, g (a * x + b * y) ∂γ
      exact integral_congr_ae (Filter.Eventually.of_forall h_B2)
    rw [h_lhs, h_rhs_A2, h_rhs_B2] at hCS
    exact hCS
  -- Combine with Mehler derivative:
  -- ((P_t g)'(x))² = a² · (P_t g'(x))² ≤ a² · P_t((g')²/g)(x) · P_t g(x).
  -- Divide by P_t g(x) ≥ ε > 0:
  -- ((P_t g)'(x))² / P_t g(x) ≤ a² · P_t((g')²/g)(x).
  have h_ptwise : ∀ x,
      (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x ≤
        a ^ 2 * ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x := by
    intro x
    have hPtg_pos := h_Ptg_pos x
    have h_step1 : (deriv (ouSemigroup t g) x) ^ 2 =
        a ^ 2 * (ouSemigroup t (deriv g) x) ^ 2 := by
      rw [h_deriv_eq x]; ring
    have h_step2 : a ^ 2 * (ouSemigroup t (deriv g) x) ^ 2 ≤
        a ^ 2 * (ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x * ouSemigroup t g x) :=
      mul_le_mul_of_nonneg_left (h_cauchy x) (sq_nonneg _)
    have h_combined : (deriv (ouSemigroup t g) x) ^ 2 ≤
        a ^ 2 * (ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x) * ouSemigroup t g x := by
      rw [h_step1, mul_assoc]
      exact h_step2
    -- Divide by P_t g(x) > 0.
    have h_div : (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x ≤
        a ^ 2 * ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x := by
      have := div_le_div_of_nonneg_right h_combined hPtg_pos.le
      -- (a² · P · Q) / Q = a² · P when Q > 0.
      have hQ_ne : ouSemigroup t g x ≠ 0 := hPtg_pos.ne'
      rw [mul_div_assoc, div_self hQ_ne, mul_one] at this
      exact this
    exact h_div
  -- Now integrate the pointwise bound against γ, and use γ-invariance of P_t.
  -- LHS: ∫ ((P_t g)')² / P_t g dγ = fisherInfo (P_t g).
  -- RHS: a² · ∫ P_t((g')²/g) dγ = a² · ∫ (g')²/g dγ = a² · fisherInfo g.
  -- γ-invariance of P_t for (g')²/g.
  have h_inv : ∫ x, ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x ∂γ =
      ∫ y, (deriv g y) ^ 2 / g y ∂γ := by
    set φ : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
    have hφ_meas : Measurable φ := h_inv_lin_meas
    have hmap := ou_kernel_map t ht
    have hg'_over_g_φ_int : Integrable
        (fun p => (deriv g (φ p)) ^ 2 / g (φ p)) (γ.prod γ) := by
      refine Integrable.mono' (integrable_const (M ^ 2 / ε)) ?_ ?_
      · exact ((h_qsq_over_r_meas.comp hφ_meas)).aestronglyMeasurable
      · filter_upwards with p
        rw [Real.norm_eq_abs, abs_of_nonneg (h_qsq_over_r_nn _)]
        exact h_qsq_over_r_bd _
    have h_fubini :
        ∫ x, (∫ y, (deriv g (a*x + b*y)) ^ 2 / g (a*x + b*y) ∂γ) ∂γ =
          ∫ p, (deriv g (φ p)) ^ 2 / g (φ p) ∂(γ.prod γ) :=
      (integral_prod _ hg'_over_g_φ_int).symm
    have h_law : HasLaw φ γ (γ.prod γ) := ⟨hφ_meas.aemeasurable, hmap⟩
    have h_push : ∫ p, (deriv g (φ p)) ^ 2 / g (φ p) ∂(γ.prod γ) =
        ∫ z, (deriv g z) ^ 2 / g z ∂γ :=
      h_law.integral_comp h_qsq_over_r_meas.aestronglyMeasurable
    show ∫ x, (∫ y, (deriv g (a*x + b*y)) ^ 2 / g (a*x + b*y) ∂γ) ∂γ
        = ∫ y, (deriv g y) ^ 2 / g y ∂γ
    rw [h_fubini, h_push]
  -- Integrability of the LHS integrand: ((P_t g)')² / P_t g.
  -- Bounds: |(P_t g)'(x)| ≤ M (since |a · P_t(g') x| ≤ 1 · M ≤ M, and
  -- in any case ((P_t g)')² / P_t g ≤ M² / ε.)
  have h_Ptg_meas : Measurable (ouSemigroup t g) := by
    -- (x ↦ ∫ y, g(a*x + b*y) dγ y) is measurable as integral_prod_right'.
    show Measurable fun x => ∫ y, g (a * x + b * y) ∂γ
    have h_sm : StronglyMeasurable
        (fun p : ℝ × ℝ => g (a * p.1 + b * p.2)) :=
      (hg_meas.comp ((measurable_const.mul measurable_fst).add
        (measurable_const.mul measurable_snd))).stronglyMeasurable
    exact (h_sm.integral_prod_right' (ν := γ)).measurable
  have h_Ptdg_meas : Measurable (ouSemigroup t (deriv g)) := by
    show Measurable fun x => ∫ y, deriv g (a * x + b * y) ∂γ
    have h_sm : StronglyMeasurable
        (fun p : ℝ × ℝ => deriv g (a * p.1 + b * p.2)) :=
      (hg'_meas.comp ((measurable_const.mul measurable_fst).add
        (measurable_const.mul measurable_snd))).stronglyMeasurable
    exact (h_sm.integral_prod_right' (ν := γ)).measurable
  -- Pointwise: (deriv (P_t g) x)² / (P_t g) x ≤ a² · M² / ε.
  have h_lhs_bd : ∀ x,
      (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x ≤ a ^ 2 * (M ^ 2 / ε) := by
    intro x
    have hPtg_pos := h_Ptg_pos x
    have h1 : (deriv (ouSemigroup t g) x) ^ 2 = a ^ 2 * (ouSemigroup t (deriv g) x) ^ 2 := by
      rw [h_deriv_eq x]; ring
    have h_Ptdg_bd : |ouSemigroup t (deriv g) x| ≤ M := by
      show |∫ y, deriv g (a * x + b * y) ∂γ| ≤ M
      have h_int : Integrable (fun y => deriv g (a * x + b * y)) γ := by
        refine Integrable.mono' (integrable_const M) ?_ ?_
        · exact (hg'_meas.comp
            (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
        · filter_upwards with y; exact hg'_norm _
      calc |∫ y, deriv g (a * x + b * y) ∂γ|
          ≤ ∫ y, |deriv g (a * x + b * y)| ∂γ := abs_integral_le_integral_abs
        _ ≤ ∫ _, M ∂γ :=
              integral_mono h_int.abs (integrable_const _) (fun y => hg'_bd _)
        _ = M := by simp
    have h_Ptdg_sq_bd : (ouSemigroup t (deriv g) x) ^ 2 ≤ M ^ 2 := by
      have : (ouSemigroup t (deriv g) x) ^ 2 = |ouSemigroup t (deriv g) x| ^ 2 := by rw [sq_abs]
      rw [this]
      exact pow_le_pow_left₀ (abs_nonneg _) h_Ptdg_bd 2
    have h2 : a ^ 2 * (ouSemigroup t (deriv g) x) ^ 2 ≤ a ^ 2 * M ^ 2 :=
      mul_le_mul_of_nonneg_left h_Ptdg_sq_bd (sq_nonneg _)
    have h3 : a ^ 2 * M ^ 2 / ouSemigroup t g x ≤ a ^ 2 * M ^ 2 / ε := by
      apply div_le_div_of_nonneg_left _ hε (h_Ptg_lo x)
      positivity
    have h4 : (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x ≤ a ^ 2 * M ^ 2 / ε := by
      rw [h1]
      calc a ^ 2 * (ouSemigroup t (deriv g) x) ^ 2 / ouSemigroup t g x
          ≤ a ^ 2 * M ^ 2 / ouSemigroup t g x :=
            div_le_div_of_nonneg_right h2 (h_Ptg_pos x).le
        _ ≤ a ^ 2 * M ^ 2 / ε := h3
    calc (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x
        ≤ a ^ 2 * M ^ 2 / ε := h4
      _ = a ^ 2 * (M ^ 2 / ε) := by ring
  have h_lhs_nn : ∀ x, 0 ≤ (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x := fun x =>
    div_nonneg (sq_nonneg _) (h_Ptg_pos x).le
  have h_lhs_int : Integrable (fun x => (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x) γ := by
    refine Integrable.mono' (integrable_const (a ^ 2 * (M ^ 2 / ε))) ?_ ?_
    · -- Measurability: deriv (ouSemigroup t g) x = a · ouSemigroup t (deriv g) x.
      have h_eq : (fun x => (deriv (ouSemigroup t g) x) ^ 2 / ouSemigroup t g x) =
          (fun x => (a * ouSemigroup t (deriv g) x) ^ 2 / ouSemigroup t g x) := by
        funext x; rw [h_deriv_eq x]
      rw [h_eq]
      refine Measurable.aestronglyMeasurable ?_
      exact ((measurable_const.mul h_Ptdg_meas).pow_const 2).div h_Ptg_meas
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (h_lhs_nn _)]
      exact h_lhs_bd _
  -- Integrability of RHS integrand: a² · P_t((g')²/g) x.
  have h_Pt_qsq_over_r_meas : Measurable
      (fun x => ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x) := by
    show Measurable fun x => ∫ y, (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y) ∂γ
    have h_sm : StronglyMeasurable
        (fun p : ℝ × ℝ => (deriv g (a * p.1 + b * p.2)) ^ 2 / g (a * p.1 + b * p.2)) :=
      (h_qsq_over_r_meas.comp ((measurable_const.mul measurable_fst).add
        (measurable_const.mul measurable_snd))).stronglyMeasurable
    exact (h_sm.integral_prod_right' (ν := γ)).measurable
  have h_rhs_int : Integrable (fun x => a ^ 2 *
      ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x) γ := by
    refine Integrable.mono' (integrable_const (a ^ 2 * (M ^ 2 / ε))) ?_ ?_
    · exact (measurable_const.mul h_Pt_qsq_over_r_meas).aestronglyMeasurable
    · filter_upwards with x
      have h_inner_bd : ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x ≤ M ^ 2 / ε := by
        show ∫ y, (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y) ∂γ ≤ M ^ 2 / ε
        have h_int : Integrable
            (fun y => (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y)) γ := by
          refine Integrable.mono' (integrable_const (M ^ 2 / ε)) ?_ ?_
          · exact (h_qsq_over_r_meas.comp
              (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
          · filter_upwards with y
            rw [Real.norm_eq_abs, abs_of_nonneg (h_qsq_over_r_nn _)]
            exact h_qsq_over_r_bd _
        calc ∫ y, (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y) ∂γ
            ≤ ∫ _, (M ^ 2 / ε) ∂γ :=
                integral_mono h_int (integrable_const _) (fun y => h_qsq_over_r_bd _)
          _ = M ^ 2 / ε := by simp
      have h_inner_nn : 0 ≤ ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x := by
        show 0 ≤ ∫ y, (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y) ∂γ
        exact integral_nonneg (fun y => h_qsq_over_r_nn _)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) h_inner_nn)]
      exact mul_le_mul_of_nonneg_left h_inner_bd (sq_nonneg _)
  -- Assemble: integrate the pointwise bound.
  show fisherInfo (ouSemigroup t g) ≤ Real.exp (-2 * t) * fisherInfo g
  unfold fisherInfo
  calc ∫ y, (deriv (ouSemigroup t g) y) ^ 2 / ouSemigroup t g y ∂γ
      ≤ ∫ x, a ^ 2 * ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x ∂γ := by
        exact integral_mono h_lhs_int h_rhs_int h_ptwise
    _ = a ^ 2 * ∫ x, ouSemigroup t (fun y => (deriv g y) ^ 2 / g y) x ∂γ := by
        rw [integral_const_mul]
    _ = a ^ 2 * ∫ y, (deriv g y) ^ 2 / g y ∂γ := by rw [h_inv]
    _ = Real.exp (-2 * t) * ∫ y, (deriv g y) ^ 2 / g y ∂γ := by rw [ha_sq]

/-! ## A2: De Bruijn identity (entropy derivative = -Fisher info) -/

/-- **De Bruijn identity for the OU semigroup.** AXIOM
(vetting-required textbook bridge).

For any `C¹` `g : ℝ → ℝ` with `g, g'` bounded and `g ≥ ε > 0` pointwise,
the Boltzmann entropy `H(P_s g) = ∫ P_s g · log(P_s g) dγ` is
differentiable in `s` at any `t > 0` with derivative

  `(d/dt) H(P_t g) = -I(P_t g)`.

## Proof in textbooks

Differentiate under the integral sign:
  `(d/dt) ∫ P_t g · log(P_t g) dγ
     = ∫ ((d/dt) P_t g) · (1 + log P_t g) dγ`
     `= ∫ L(P_t g) · (1 + log P_t g) dγ`  (heat equation
                                            `hasDerivAt_t_ouSemigroup`)
     `= ∫ L(P_t g) · log(P_t g) dγ`  (since `∫ L(h) dγ = 0` for any
                                       `h` integrable, by γ-invariance)
     `= -∫ Γ(P_t g, log(P_t g)) dγ`  (integration by parts,
                                       `gaussian_dirichlet_form_identity`-style)
     `= -∫ ((P_t g)')² / P_t g dγ`  (since `Γ(f, log g) = f' · g'/g` and
                                       here `f = g = P_t g`).

The parametric differentiation requires the integrand
`(s, y) ↦ P_s g(y) · log(P_s g(y))` to satisfy a uniform dominator —
since `g ≥ ε > 0` and `|g| ≤ M`, `P_s g` also stays in `[ε, M]`, and
`s · log s` is continuous and bounded on `[ε, M]`.

## Discharge plan

Per Gemini 3.1-pro vetting (verdict: **Standard**, 2026-05-12). Two
sub-steps:

1. **Bilinear Dirichlet form identity** (auxiliary, ~50-100 lines):
   `∫ f · L h dγ = -∫ f' · h' dγ` for suitable test functions. Provable
   via 1D IBP using the identity `(h'(y) · e^{-y²/2})' = (Lh)(y) ·
   e^{-y²/2}`. This generalizes our existing
   `gaussian_dirichlet_form_identity` (which is the diagonal case
   `f = h = g`).
2. **Parametric differentiation** (~150-250 lines): differentiate
   `s ↦ ∫ P_s g · log(P_s g) dγ` under the integral via the heat
   equation `(d/ds) P_s g = L(P_s g)` and the chain rule. Use the
   bilinear Dirichlet form identity to get
   `∫ L(P_t g) · (1 + log P_t g) dγ = -∫ ((P_t g)')² / P_t g dγ`
   (taking `f := P_t g`, `h := 1 + log P_t g`, so `h' = (P_t g)'/P_t g`).
   The `(d/ds) = (d/dt)`-style step uses Mathlib's
   `hasDerivAt_integral_of_dominated_loc_of_deriv_le`; dominator is
   `|L(P_t g)|·(M·log M + 1)` which is γ-integrable (linear growth
   times Gaussian).

The C¹ restriction on `g` (not `C^∞`) is intentional: for `t > 0`,
`P_t g` is automatically `C^∞` (by `ouSemigroup_contDiff_bounded`,
discharged in `EuclideanHermite.lean`), so the differentiation works
cleanly. At `t = 0` the right-derivative is established by FTC + DCT
limit (the auxiliary `hasDerivWithinAt_entropy_ouSemigroup_zero`).

## References

* Bakry-Gentil-Ledoux, §5.5 (de Bruijn identity).
* Stam (1959), "Some inequalities satisfied by the quantities of
  information of Fisher and Shannon."

## Vetting

**Standard** (gemini-3.1-pro-preview, 2026-05-12). For `t > 0`, the
parametric differentiation goes through cleanly because `P_t g` is
`C^∞` and the integrand `(LP_tg)(1 + log P_tg)` has at-most-linear
growth × Gaussian decay → γ-integrable. The boundary version at
`t = 0` (which has only `C¹` regularity) is correct via the FTC+DCT
route: `lim_{t↘0} I(P_t g) = I(g)` by DCT, so the right-derivative
matches. Hypotheses tight; both `g ≤ M` and `|g'| ≤ M` are needed
for clean dominator bounds. -/
axiom hasDerivAt_entropy_ouSemigroup
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    {ε M : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hg'_bd : ∀ x, |deriv g x| ≤ M)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => boltzmannEntropy (ouSemigroup s g))
      (-fisherInfo (ouSemigroup t g)) t

/-- **Boundary case of de Bruijn at `t = 0+`.** AXIOM.

The de Bruijn identity extends to a right-derivative at `t = 0`:
`HasDerivWithinAt (s ↦ H(P_s g)) (-I(g)) (Ici 0) 0`.

Required for the FTC application that integrates from 0 to t. -/
axiom hasDerivWithinAt_entropy_ouSemigroup_zero
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    {ε M : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hg'_bd : ∀ x, |deriv g x| ≤ M) :
    HasDerivWithinAt (fun s => boltzmannEntropy (ouSemigroup s g))
      (-fisherInfo g) (Set.Ici 0) 0

end Gaussian1D

end
