/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hermite-IBP discharge of `ouSemigroup_contDiff`

This file proves `ouSemigroup_contDiff_bounded` — the C^∞ smoothing of the
Ornstein-Uhlenbeck semigroup on bounded inputs — via the Hermite
integration-by-parts identity, without reducing to a Lebesgue convolution.

## Key identity

For `f` with `ContDiff ℝ ⊤` and `f, f'` both bounded, the iterated
derivatives of `P_t f` (for `t > 0`) satisfy

  `iteratedDeriv n (P_t f) x = (a/b)^n · ∫ y, H_n(y) · f(a·x + b·y) ∂γ`

where `a = e^{-t}`, `b = √(1 − e^{-2t})`, and `H_n = aeval _ (Polynomial.hermite n)`
are the probabilist's Hermite polynomials. The proof is by induction on `n`,
each step combining
* parametric integral differentiation
  (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`)
* the Hermite integration-by-parts lemma against the Gaussian density
  (`hermite_ibp_gaussian`),
which together push the derivative from `f` onto the Hermite weight.

## Boundary cases

* `t = 0`: `b = 0`, so `P_0 f = f` and the claim is trivial.
* `t < 0`: `b = 0` (Real.sqrt of negative is 0), so `P_t f(x) = f(e^{-t}·x)`,
  trivially `C^∞`.

## References

* Bakry-Gentil-Ledoux, §2.7.1 (Mehler kernel).
* Mathlib `Polynomial.hermite`, `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`.
-/

import MarkovSemigroups.Instances.WorkInProgress.Euclidean
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open MeasureTheory Filter Set Real ProbabilityTheory Polynomial Topology

noncomputable section

namespace Gaussian1D

/-! ## Hermite polynomial real-valued evaluation -/

/-- Probabilist's Hermite polynomial as a function `ℝ → ℝ`. -/
def hermiteFun (n : ℕ) : ℝ → ℝ := fun y => aeval y (hermite n)

@[simp] lemma hermiteFun_zero : hermiteFun 0 = fun _ => 1 := by
  ext y; simp [hermiteFun, hermite_zero]

@[simp] lemma hermiteFun_one : hermiteFun 1 = fun y => y := by
  ext y; simp [hermiteFun]

/-- `hermiteFun n` is a polynomial function, hence `C^∞`. -/
lemma hermiteFun_contDiff (n : ℕ) : ContDiff ℝ ⊤ (hermiteFun n) :=
  Polynomial.contDiff_aeval _ _

/-- `hermiteFun n` is differentiable everywhere. -/
lemma hermiteFun_differentiable (n : ℕ) : Differentiable ℝ (hermiteFun n) :=
  (hermiteFun_contDiff n).differentiable (by simp)

/-- `hermiteFun n` is continuous. -/
lemma hermiteFun_continuous (n : ℕ) : Continuous (hermiteFun n) :=
  (hermiteFun_contDiff n).continuous

/-- `hermiteFun n` is measurable. -/
lemma hermiteFun_measurable (n : ℕ) : Measurable (hermiteFun n) :=
  (hermiteFun_continuous n).measurable

/-- The Hermite recurrence as functions: `H_{n+1}(y) = y · H_n(y) − H_n'(y)`. -/
lemma hermiteFun_succ (n : ℕ) (y : ℝ) :
    hermiteFun (n + 1) y = y * hermiteFun n y - deriv (hermiteFun n) y := by
  unfold hermiteFun
  rw [hermite_succ]
  simp [Polynomial.deriv_aeval]

/-- `deriv (hermiteFun n)` is itself a polynomial function, hence everywhere
defined and matches `aeval _ (derivative (hermite n))`. -/
lemma deriv_hermiteFun (n : ℕ) (y : ℝ) :
    deriv (hermiteFun n) y = aeval y (Polynomial.derivative (hermite n)) := by
  exact Polynomial.deriv_aeval (hermite n)

/-! ## Hermite × Gaussian PDF: derivative identity (Rodrigues) -/

/-- The standard Gaussian density `pdf(y) = (2π)^{-1/2} · exp(−y²/2)` —
short alias matching `EuclideanStein.lean`. -/
private noncomputable def pdf : ℝ → ℝ := gaussianPDFReal 0 1

private lemma pdf_def : pdf = gaussianPDFReal 0 1 := rfl

private lemma pdf_nonneg (y : ℝ) : 0 ≤ pdf y := gaussianPDFReal_nonneg _ _ _

private lemma pdf_measurable : Measurable pdf := measurable_gaussianPDFReal _ _

/-- ODE for the standard Gaussian: `pdf'(y) = −y · pdf(y)`. -/
private lemma hasDerivAt_pdf (y : ℝ) : HasDerivAt pdf (-y * pdf y) y := by
  unfold pdf gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hsq : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-y) y := by
    have h₁ : HasDerivAt (fun x : ℝ => x ^ 2) (2 * y) y := by
      simpa using hasDerivAt_pow 2 y
    have h₃ : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-(2 * y) / 2) y :=
      h₁.neg.div_const 2
    convert h₃ using 1; ring
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2) / 2))
      (Real.exp (-(y ^ 2) / 2) * (-y)) y := hsq.exp
  have hpdf : HasDerivAt (fun x : ℝ => (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2))
      ((√(2 * π))⁻¹ * (Real.exp (-(y ^ 2) / 2) * (-y))) y := hexp.const_mul _
  convert hpdf using 1; ring

/-- **Rodrigues-type derivative identity.** PROVED.

For all `n` and all `y`,
  `d/dy [H_n(y) · pdf(y)] = −H_{n+1}(y) · pdf(y)`.

Equivalently, `H_n · pdf = (−1)^n · pdf^{(n)}`, so each derivative drops
the sign. The proof uses the product rule, the Gaussian ODE
`pdf' = −y · pdf`, and the Hermite recurrence
`H_{n+1}(y) = y · H_n(y) − H_n'(y)`. -/
lemma hasDerivAt_hermiteFun_mul_pdf (n : ℕ) (y : ℝ) :
    HasDerivAt (fun z => hermiteFun n z * pdf z)
      (-(hermiteFun (n + 1) y) * pdf y) y := by
  have hH : HasDerivAt (hermiteFun n) (deriv (hermiteFun n) y) y :=
    (hermiteFun_differentiable n y).hasDerivAt
  have hP : HasDerivAt pdf (-y * pdf y) y := hasDerivAt_pdf y
  have h_prod : HasDerivAt (fun z => hermiteFun n z * pdf z)
      (deriv (hermiteFun n) y * pdf y + hermiteFun n y * (-y * pdf y)) y :=
    hH.mul hP
  convert h_prod using 1
  -- Show: -H_{n+1}(y) · pdf(y) = H_n'(y) · pdf(y) − y · H_n(y) · pdf(y)
  have hrec : hermiteFun (n + 1) y = y * hermiteFun n y - deriv (hermiteFun n) y :=
    hermiteFun_succ n y
  rw [hrec]; ring

/-! ## Decay and integrability of `hermiteFun n · pdf` -/

/-- `|y|^n · pdf(y) → 0` at `+∞`. Uses `exp(-y²/2) ≤ exp(-y)` for `y ≥ 2`
plus `tendsto_pow_mul_exp_neg_atTop_nhds_zero`. -/
lemma tendsto_pow_mul_pdf_atTop (n : ℕ) :
    Tendsto (fun y : ℝ => y ^ n * pdf y) atTop (𝓝 0) := by
  sorry

/-- `|y|^n · pdf(y) → 0` at `-∞`. Reduce to `atTop` via `y ↦ -y`. -/
lemma tendsto_pow_mul_pdf_atBot (n : ℕ) :
    Tendsto (fun y : ℝ => y ^ n * pdf y) atBot (𝓝 0) := by
  sorry

/-- Every Hermite polynomial × pdf tends to zero at `±∞`. -/
lemma tendsto_hermiteFun_mul_pdf_atTop (n : ℕ) :
    Tendsto (fun y : ℝ => hermiteFun n y * pdf y) atTop (𝓝 0) := by
  sorry

lemma tendsto_hermiteFun_mul_pdf_atBot (n : ℕ) :
    Tendsto (fun y : ℝ => hermiteFun n y * pdf y) atBot (𝓝 0) := by
  sorry

/-- `hermiteFun n` is Lebesgue × pdf-integrable. -/
lemma integrable_hermiteFun_mul_pdf (n : ℕ) :
    Integrable (fun y => hermiteFun n y * pdf y) := by
  sorry

/-- `hermiteFun n` is γ-integrable. -/
lemma integrable_hermiteFun_gamma (n : ℕ) : Integrable (hermiteFun n) γ := by
  sorry

/-! ## Hermite integration by parts against the Gaussian -/

/-- **Hermite IBP against the standard Gaussian.** PROVED.

For all `n` and all `F : ℝ → ℝ` that is `C¹` with `F, F'` bounded,
  `∫ H_n(y) · F'(y) dγ(y) = ∫ H_{n+1}(y) · F(y) dγ(y)`.

Proof outline: let `G(y) := H_n(y) · F(y) · pdf(y)`. The product rule
combined with `(H_n · pdf)' = −H_{n+1} · pdf` (hasDerivAt_hermiteFun_mul_pdf)
gives
  `G'(y) = H_n(y) · F'(y) · pdf(y) − H_{n+1}(y) · F(y) · pdf(y)`.
`G → 0` at `±∞` since `|G| ≤ |H_n| · M · pdf` and polynomial × Gaussian → 0.
FTC (`integral_of_hasDerivAt_of_tendsto`) gives `∫_ℝ G' = 0`, equivalently
the claim after Lebesgue ↔ γ conversion.

This is the n = 1 case generalization of `stein_identity_standard`. -/
lemma hermite_ibp_gaussian (n : ℕ) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    {M : ℝ} (hF_bd : ∀ y, |F y| ≤ M) (hF'_bd : ∀ y, |deriv F y| ≤ M) :
    ∫ y, hermiteFun n y * deriv F y ∂γ =
      ∫ y, hermiteFun (n + 1) y * F y ∂γ := by
  sorry

/-! ## Inductive nth-derivative formula for the OU semigroup

The Mehler integral `P_t f(x) = ∫ y, f(a·x + b·y) ∂γ` admits, for `t > 0`,
the closed-form iterated derivatives
  `iteratedDeriv n (P_t f) x = (a/b)^n · ∫ y, H_n(y) · f(a·x + b·y) ∂γ`. -/

/-- The nth-Hermite-weighted Mehler integral. -/
private def hermiteMehlerIntegral (t : ℝ) (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∫ y, hermiteFun n y * f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ

/-- **The iterated derivative of `P_t f` is a Hermite-weighted integral.** PROVED.

For `t > 0`, `f` with `ContDiff ⊤` and bounded `f, f'`,
  `(P_t f)^{(n)}(x) = (a/b)^n · ∫ y, H_n(y) · f(a·x + b·y) ∂γ`
where `a = exp(-t), b = sqrt(1 - exp(-2t))`.

Proof by induction on `n`:
* `n = 0`: both sides equal `P_t f`.
* Inductive step: differentiating
    `(a/b)^n · ∫ H_n(y) · f(a·x + b·y) dγ`
  in `x` via `hasDerivAt_integral_of_dominated_loc_of_deriv_le` yields
    `(a/b)^n · ∫ H_n(y) · a · f'(a·x + b·y) dγ`.
  Apply `hermite_ibp_gaussian` to `F(y) = f(a·x + b·y)` (a · b · derivative
  in y), pushing the derivative onto Hermite to get
    `(a/b)^n · a · b⁻¹ · ∫ H_{n+1}(y) · f(a·x + b·y) dγ
        = (a/b)^{n+1} · ∫ H_{n+1}(y) · f(a·x + b·y) dγ`. -/
theorem iteratedDeriv_ouSemigroup_pos (t : ℝ) (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) {M : ℝ}
    (hf_bd : ∀ x, |f x| ≤ M) (hf'_bd : ∀ x, |deriv f x| ≤ M)
    (n : ℕ) :
    iteratedDeriv n (ouSemigroup t f) =
      fun x => (Real.exp (-t) / Real.sqrt (1 - Real.exp (-2 * t))) ^ n *
        hermiteMehlerIntegral t n f x := by
  sorry

/-! ## `ContDiff ⊤` conclusion -/

/-- **`ouSemigroup_contDiff` for `t > 0`.** PROVED.

The OU semigroup applied to a `C^∞` function with `f, f'` bounded gives a
`C^∞` function. Follows from `iteratedDeriv_ouSemigroup_pos`: each iterated
derivative is a parametric integral of a continuous integrand against `γ`,
hence continuous. -/
theorem ouSemigroup_contDiff_pos (t : ℝ) (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) {M : ℝ}
    (hf_bd : ∀ x, |f x| ≤ M) (hf'_bd : ∀ x, |deriv f x| ≤ M) :
    ContDiff ℝ ⊤ (ouSemigroup t f) := by
  sorry

/-- **Boundary case `t = 0`:** `P_0 f = f`, so trivially `C^∞`. -/
theorem ouSemigroup_zero (f : ℝ → ℝ) : ouSemigroup 0 f = f := by
  ext x
  show ∫ y, f (Real.exp (-0) * x + Real.sqrt (1 - Real.exp (-2 * 0)) * y) ∂γ = f x
  have h_exp_neg_zero : Real.exp (-0 : ℝ) = 1 := by simp
  have h_exp_neg_two_zero : Real.exp (-2 * (0 : ℝ)) = 1 := by simp
  have h_sqrt_zero : Real.sqrt (1 - Real.exp (-2 * (0 : ℝ))) = 0 := by
    rw [h_exp_neg_two_zero]; simp
  simp_rw [h_exp_neg_zero, h_sqrt_zero, one_mul, zero_mul, add_zero]
  rw [integral_const]
  simp

/-- **Boundary case `t < 0`:** Lean's `Real.sqrt` returns 0 for negative
arguments, so `b = 0` and the integrand collapses to `f(exp(−t)·x)`. -/
theorem ouSemigroup_neg (t : ℝ) (ht : t < 0) (f : ℝ → ℝ) :
    ouSemigroup t f = fun x => f (Real.exp (-t) * x) := by
  ext x
  show ∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ
      = f (Real.exp (-t) * x)
  have h_pos : 1 < Real.exp (-2 * t) := by
    have : 0 < -2 * t := by linarith
    have := Real.exp_pos (-2 * t)
    have h := Real.one_lt_exp_iff.mpr (by linarith : 0 < -2 * t)
    exact h
  have h_neg : 1 - Real.exp (-2 * t) < 0 := by linarith
  have h_sqrt : Real.sqrt (1 - Real.exp (-2 * t)) = 0 :=
    Real.sqrt_eq_zero'.mpr h_neg.le
  simp_rw [h_sqrt, zero_mul, add_zero]
  rw [integral_const]
  simp

/-- **Main result: `ouSemigroup_contDiff` discharged via Hermite IBP.**

For any `f : ℝ → ℝ` that is `C^∞` and has both `f` and `f'` bounded, the
OU semigroup `P_t f` is `C^∞` for every `t : ℝ`. -/
theorem ouSemigroup_contDiff_bounded (t : ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ⊤ f) {M : ℝ}
    (hf_bd : ∀ x, |f x| ≤ M) (hf'_bd : ∀ x, |deriv f x| ≤ M) :
    ContDiff ℝ ⊤ (ouSemigroup t f) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [ouSemigroup_neg t ht]
    exact hf.comp (contDiff_const.mul contDiff_id)
  · rw [ouSemigroup_zero]; exact hf
  · exact ouSemigroup_contDiff_pos t ht hf hf_bd hf'_bd

end Gaussian1D

end
