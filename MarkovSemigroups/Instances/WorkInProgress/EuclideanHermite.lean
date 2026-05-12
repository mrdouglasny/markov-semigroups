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

/-- `|y|^n · pdf(y) → 0` at `+∞`. Uses `exp(-y²/2) ≤ exp(-y/2)` for `y ≥ 1`
plus `tendsto_pow_mul_exp_neg_atTop_nhds_zero`. -/
lemma tendsto_pow_mul_pdf_atTop (n : ℕ) :
    Tendsto (fun y : ℝ => y ^ n * pdf y) atTop (𝓝 0) := by
  -- Step 1: y^n * exp(-y/2) tends to 0 as y → ∞, via composition with `y/2`.
  have hhalf : Tendsto (fun y : ℝ => y / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have hpow_exp : Tendsto (fun y : ℝ => y ^ n * Real.exp (-(y / 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => u ^ n * Real.exp (-u)) atTop (𝓝 0) :=
      tendsto_pow_mul_exp_neg_atTop_nhds_zero n
    have h2 : Tendsto (fun y : ℝ => (y / 2) ^ n * Real.exp (-(y / 2))) atTop (𝓝 0) :=
      h1.comp hhalf
    have h3 : Tendsto (fun y : ℝ => (2 : ℝ) ^ n * ((y / 2) ^ n * Real.exp (-(y / 2))))
        atTop (𝓝 ((2 : ℝ) ^ n * 0)) :=
      tendsto_const_nhds.mul h2
    rw [mul_zero] at h3
    refine h3.congr' ?_
    filter_upwards with y
    have h2ne : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)
    rw [div_pow]
    field_simp
  -- Step 2: multiply by constant (√(2π))⁻¹.
  set c : ℝ := (Real.sqrt (2 * π))⁻¹ with hc_def
  have hc_nonneg : 0 ≤ c := by
    have : 0 ≤ Real.sqrt (2 * π) := Real.sqrt_nonneg _
    positivity
  have hconst : Tendsto (fun y : ℝ => c * (y ^ n * Real.exp (-(y / 2)))) atTop
      (𝓝 (c * 0)) := tendsto_const_nhds.mul hpow_exp
  rw [mul_zero] at hconst
  -- Step 3: For y ≥ 1, 0 ≤ y^n * pdf y ≤ c * y^n * exp(-y/2). Use squeeze.
  refine squeeze_zero' (f := fun y : ℝ => y ^ n * pdf y)
    (g := fun y : ℝ => c * (y ^ n * Real.exp (-(y / 2)))) ?_ ?_ hconst
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with y hy
    exact mul_nonneg (pow_nonneg hy n) (pdf_nonneg y)
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with y hy
    have hy_pos : 0 ≤ y := le_trans zero_le_one hy
    have hyn_nonneg : 0 ≤ y ^ n := pow_nonneg hy_pos n
    -- pdf y = c * exp(-y²/2)
    have hpdf_eq : pdf y = c * Real.exp (-(y ^ 2) / 2) := by
      show gaussianPDFReal 0 1 y = c * Real.exp (-(y ^ 2) / 2)
      unfold gaussianPDFReal
      simp [hc_def]
    -- y² ≥ y for y ≥ 1
    have hy_sq : y ≤ y ^ 2 := by
      have h : y * 1 ≤ y * y := mul_le_mul_of_nonneg_left hy hy_pos
      simpa [pow_two] using h
    -- exp(-y²/2) ≤ exp(-y/2)
    have hexp_le : Real.exp (-(y ^ 2) / 2) ≤ Real.exp (-(y / 2)) := by
      apply Real.exp_le_exp.mpr
      have h_neg : -(y ^ 2) ≤ -y := by linarith
      linarith
    rw [hpdf_eq]
    calc y ^ n * (c * Real.exp (-(y ^ 2) / 2))
        = c * (y ^ n * Real.exp (-(y ^ 2) / 2)) := by ring
      _ ≤ c * (y ^ n * Real.exp (-(y / 2))) := by
          apply mul_le_mul_of_nonneg_left _ hc_nonneg
          exact mul_le_mul_of_nonneg_left hexp_le hyn_nonneg

/-- `pdf` is even: `pdf(-y) = pdf(y)`. -/
private lemma pdf_neg (y : ℝ) : pdf (-y) = pdf y := by
  show gaussianPDFReal 0 1 (-y) = gaussianPDFReal 0 1 y
  unfold gaussianPDFReal
  simp

/-- `|y|^n · pdf(y) → 0` at `-∞`. Reduce to `atTop` via `y ↦ -y`. -/
lemma tendsto_pow_mul_pdf_atBot (n : ℕ) :
    Tendsto (fun y : ℝ => y ^ n * pdf y) atBot (𝓝 0) := by
  -- Substitute y ↦ -y. `(-y)^n * pdf(-y) = (-1)^n * y^n * pdf y`.
  have h_top : Tendsto (fun y : ℝ => y ^ n * pdf y) atTop (𝓝 0) :=
    tendsto_pow_mul_pdf_atTop n
  -- Composed with Neg.neg : ℝ → ℝ which takes atBot to atTop.
  have hneg : Tendsto (fun y : ℝ => -y) atBot atTop := tendsto_neg_atBot_atTop
  have h_comp : Tendsto (fun y : ℝ => (-y) ^ n * pdf (-y)) atBot (𝓝 0) :=
    h_top.comp hneg
  -- (-y)^n * pdf(-y) = (-1)^n * (y^n * pdf y)
  have hrewrite : ∀ y : ℝ, (-y) ^ n * pdf (-y) = (-1) ^ n * (y ^ n * pdf y) := by
    intro y; rw [pdf_neg, neg_pow]; ring
  have h_comp' : Tendsto (fun y : ℝ => (-1 : ℝ) ^ n * (y ^ n * pdf y)) atBot (𝓝 0) := by
    refine h_comp.congr ?_
    intro y; exact hrewrite y
  -- Multiply by (-1)^n to recover y^n * pdf y.
  have h_const : Tendsto (fun y : ℝ => (-1 : ℝ) ^ n * ((-1) ^ n * (y ^ n * pdf y)))
      atBot (𝓝 ((-1 : ℝ) ^ n * 0)) :=
    tendsto_const_nhds.mul h_comp'
  rw [mul_zero] at h_const
  refine h_const.congr ?_
  intro y
  rw [← mul_assoc, ← pow_add, ← two_mul]
  have : ((-1 : ℝ)) ^ (2 * n) = 1 := by
    rw [pow_mul]; simp
  rw [this, one_mul]

/-- Polynomial expansion: `hermiteFun n y = ∑ i ∈ range (deg+1), c_i * y^i`,
where `c_i := ((hermite n).coeff i : ℝ)`. -/
private lemma hermiteFun_eq_sum (n : ℕ) (y : ℝ) :
    hermiteFun n y =
      ∑ i ∈ Finset.range ((hermite n).natDegree + 1),
        ((hermite n).coeff i : ℝ) * y ^ i := by
  unfold hermiteFun
  rw [aeval_eq_sum_range (R := ℤ) (S := ℝ) (p := hermite n) y]
  apply Finset.sum_congr rfl
  intros i _
  rw [Algebra.smul_def]
  simp

/-- Every Hermite polynomial × pdf tends to zero at `+∞`. -/
lemma tendsto_hermiteFun_mul_pdf_atTop (n : ℕ) :
    Tendsto (fun y : ℝ => hermiteFun n y * pdf y) atTop (𝓝 0) := by
  have h_sum_tendsto : Tendsto
      (fun y : ℝ => ∑ i ∈ Finset.range ((hermite n).natDegree + 1),
          ((hermite n).coeff i : ℝ) * (y ^ i * pdf y))
      atTop (𝓝 (∑ i ∈ Finset.range ((hermite n).natDegree + 1),
          ((hermite n).coeff i : ℝ) * (0 : ℝ))) := by
    refine tendsto_finset_sum _ (fun i _ => ?_)
    exact tendsto_const_nhds.mul (tendsto_pow_mul_pdf_atTop i)
  have hzero : (∑ i ∈ Finset.range ((hermite n).natDegree + 1),
      ((hermite n).coeff i : ℝ) * (0 : ℝ)) = 0 := by simp
  rw [hzero] at h_sum_tendsto
  refine h_sum_tendsto.congr ?_
  intro y
  rw [hermiteFun_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intros; ring

lemma tendsto_hermiteFun_mul_pdf_atBot (n : ℕ) :
    Tendsto (fun y : ℝ => hermiteFun n y * pdf y) atBot (𝓝 0) := by
  have h_sum_tendsto : Tendsto
      (fun y : ℝ => ∑ i ∈ Finset.range ((hermite n).natDegree + 1),
          ((hermite n).coeff i : ℝ) * (y ^ i * pdf y))
      atBot (𝓝 (∑ i ∈ Finset.range ((hermite n).natDegree + 1),
          ((hermite n).coeff i : ℝ) * (0 : ℝ))) := by
    refine tendsto_finset_sum _ (fun i _ => ?_)
    exact tendsto_const_nhds.mul (tendsto_pow_mul_pdf_atBot i)
  have hzero : (∑ i ∈ Finset.range ((hermite n).natDegree + 1),
      ((hermite n).coeff i : ℝ) * (0 : ℝ)) = 0 := by simp
  rw [hzero] at h_sum_tendsto
  refine h_sum_tendsto.congr ?_
  intro y
  rw [hermiteFun_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intros; ring

/-- Each monomial `y^i` is γ-integrable. -/
private lemma integrable_pow_gamma (i : ℕ) : Integrable (fun y : ℝ => y ^ i) γ := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    simp only [pow_zero]
    exact integrable_const _
  -- For i ≥ 1, use MemLp id i and integrable_norm_pow.
  have hmem : MemLp (id : ℝ → ℝ) (i : NNReal) γ :=
    memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) (i : NNReal)
  have h_int_norm : Integrable (fun y : ℝ => ‖y‖ ^ i) γ :=
    hmem.integrable_norm_pow (p := i) hi.ne'
  -- |y^i| = ‖y‖^i, so y^i is integrable.
  have h_meas : AEStronglyMeasurable (fun y : ℝ => y ^ i) γ :=
    (continuous_pow i).aestronglyMeasurable
  refine (integrable_norm_iff h_meas).mp ?_
  refine h_int_norm.congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  simp only [norm_pow]

/-- `hermiteFun n` is γ-integrable. -/
lemma integrable_hermiteFun_gamma (n : ℕ) : Integrable (hermiteFun n) γ := by
  -- hermiteFun n y = ∑ i, c_i * y^i. Each y^i is integrable; sum of integrables is integrable.
  have h_rewrite : (hermiteFun n) =
      fun y => ∑ i ∈ Finset.range ((hermite n).natDegree + 1),
        ((hermite n).coeff i : ℝ) * y ^ i := by
    ext y; exact hermiteFun_eq_sum n y
  rw [h_rewrite]
  apply integrable_finset_sum
  intros i _
  exact (integrable_pow_gamma i).const_mul _

/-- `hermiteFun n` is Lebesgue × pdf-integrable. -/
lemma integrable_hermiteFun_mul_pdf (n : ℕ) :
    Integrable (fun y => hermiteFun n y * pdf y) := by
  -- Use: Integrable f γ ↔ Integrable (fun y => pdf y * f y) volume, then multiplication commutes.
  have h_gamma : Integrable (hermiteFun n) γ := integrable_hermiteFun_gamma n
  -- γ = volume.withDensity (gaussianPDF 0 1)
  have hγ_eq : (γ : Measure ℝ) = (volume : Measure ℝ).withDensity (gaussianPDF 0 1) := by
    show gaussianReal 0 1 = _
    have h1ne : ((1 : NNReal)) ≠ 0 := one_ne_zero
    exact gaussianReal_of_var_ne_zero _ h1ne
  rw [hγ_eq] at h_gamma
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)] at h_gamma
  refine h_gamma.congr ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  show (gaussianPDF 0 1 y).toReal • hermiteFun n y = hermiteFun n y * pdf y
  rw [smul_eq_mul, mul_comm]
  congr 1
  -- pdf y = (gaussianPDF 0 1 y).toReal
  show (ENNReal.ofReal (gaussianPDFReal 0 1 y)).toReal = pdf y
  rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  rfl

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
  -- Setup: basic regularity of the data.
  have hM_nn : 0 ≤ M := (abs_nonneg _).trans (hF_bd 0)
  have hF_diff : Differentiable ℝ F := hF.differentiable (by simp)
  have hF_meas : Measurable F := hF.continuous.measurable
  have hF'_meas : Measurable (deriv F) := (hF.continuous_deriv (by simp)).measurable
  have hH_meas : Measurable (hermiteFun n) := hermiteFun_measurable n
  have hH'_meas : Measurable (hermiteFun (n+1)) := hermiteFun_measurable (n+1)
  have hpdf_nn : ∀ y, 0 ≤ pdf y := pdf_nonneg
  -- Derivative of G(z) := hermiteFun n z * F z * pdf z.
  -- Product rule on (hermiteFun n · pdf) · F using
  --   (hermiteFun n · pdf)'(y) = -hermiteFun (n+1) y · pdf y  and  F'(y) = deriv F y.
  have hG_deriv : ∀ y, HasDerivAt (fun z => hermiteFun n z * F z * pdf z)
      (hermiteFun n y * deriv F y * pdf y -
        hermiteFun (n + 1) y * F y * pdf y) y := by
    intro y
    have hK : HasDerivAt (fun z => hermiteFun n z * pdf z)
        (-(hermiteFun (n + 1) y) * pdf y) y := hasDerivAt_hermiteFun_mul_pdf n y
    have hF_at : HasDerivAt F (deriv F y) y := hF_diff.differentiableAt.hasDerivAt
    have h_prod : HasDerivAt (fun z => hermiteFun n z * pdf z * F z)
        (-(hermiteFun (n + 1) y) * pdf y * F y +
          hermiteFun n y * pdf y * deriv F y) y := hK.mul hF_at
    have h_fun_eq :
        (fun z => hermiteFun n z * pdf z * F z) =
        (fun z => hermiteFun n z * F z * pdf z) := by
      funext z; ring
    rw [h_fun_eq] at h_prod
    convert h_prod using 1
    ring
  -- Auxiliary: `|hermiteFun k y * pdf y|` is Lebesgue-integrable.
  have h_int_abs_Hpdf : ∀ k : ℕ,
      Integrable (fun y => |hermiteFun k y * pdf y|) := fun k =>
    (integrable_hermiteFun_mul_pdf k).abs
  -- Tendsto: G → 0 at ±∞. Bound: ‖G y‖ ≤ M · |hermiteFun n y * pdf y|, RHS → 0.
  have h_M_Hpdf_atTop :
      Tendsto (fun y => M * |hermiteFun n y * pdf y|) atTop (𝓝 0) := by
    have h_abs : Tendsto (fun y => |hermiteFun n y * pdf y|) atTop (𝓝 0) := by
      have := (tendsto_hermiteFun_mul_pdf_atTop n).abs
      simpa [abs_zero] using this
    have := h_abs.const_mul M
    simpa using this
  have h_M_Hpdf_atBot :
      Tendsto (fun y => M * |hermiteFun n y * pdf y|) atBot (𝓝 0) := by
    have h_abs : Tendsto (fun y => |hermiteFun n y * pdf y|) atBot (𝓝 0) := by
      have := (tendsto_hermiteFun_mul_pdf_atBot n).abs
      simpa [abs_zero] using this
    have := h_abs.const_mul M
    simpa using this
  have hG_atTop : Tendsto (fun y => hermiteFun n y * F y * pdf y) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun y => norm_nonneg _) (fun y => ?_) h_M_Hpdf_atTop
    show ‖hermiteFun n y * F y * pdf y‖ ≤ M * |hermiteFun n y * pdf y|
    have h_abs_eq : |hermiteFun n y * F y * pdf y| =
        |F y| * |hermiteFun n y * pdf y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hpdf_nn y), abs_mul,
          abs_of_nonneg (hpdf_nn y)]
      ring
    rw [Real.norm_eq_abs, h_abs_eq]
    exact mul_le_mul_of_nonneg_right (hF_bd y) (abs_nonneg _)
  have hG_atBot : Tendsto (fun y => hermiteFun n y * F y * pdf y) atBot (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun y => norm_nonneg _) (fun y => ?_) h_M_Hpdf_atBot
    show ‖hermiteFun n y * F y * pdf y‖ ≤ M * |hermiteFun n y * pdf y|
    have h_abs_eq : |hermiteFun n y * F y * pdf y| =
        |F y| * |hermiteFun n y * pdf y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hpdf_nn y), abs_mul,
          abs_of_nonneg (hpdf_nn y)]
      ring
    rw [Real.norm_eq_abs, h_abs_eq]
    exact mul_le_mul_of_nonneg_right (hF_bd y) (abs_nonneg _)
  -- Integrability of the two pieces of G'.
  have h_int_HF'pdf :
      Integrable (fun y => hermiteFun n y * deriv F y * pdf y) := by
    refine Integrable.mono' ((h_int_abs_Hpdf n).const_mul M)
      ((hH_meas.mul hF'_meas).mul pdf_measurable |>.aestronglyMeasurable) ?_
    filter_upwards with y
    show ‖hermiteFun n y * deriv F y * pdf y‖ ≤ M * |hermiteFun n y * pdf y|
    have h_abs_eq : |hermiteFun n y * deriv F y * pdf y| =
        |deriv F y| * |hermiteFun n y * pdf y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hpdf_nn y), abs_mul,
          abs_of_nonneg (hpdf_nn y)]
      ring
    rw [Real.norm_eq_abs, h_abs_eq]
    exact mul_le_mul_of_nonneg_right (hF'_bd y) (abs_nonneg _)
  have h_int_HFpdf :
      Integrable (fun y => hermiteFun (n + 1) y * F y * pdf y) := by
    refine Integrable.mono' ((h_int_abs_Hpdf (n + 1)).const_mul M)
      ((hH'_meas.mul hF_meas).mul pdf_measurable |>.aestronglyMeasurable) ?_
    filter_upwards with y
    show ‖hermiteFun (n + 1) y * F y * pdf y‖ ≤ M * |hermiteFun (n + 1) y * pdf y|
    have h_abs_eq : |hermiteFun (n + 1) y * F y * pdf y| =
        |F y| * |hermiteFun (n + 1) y * pdf y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hpdf_nn y), abs_mul,
          abs_of_nonneg (hpdf_nn y)]
      ring
    rw [Real.norm_eq_abs, h_abs_eq]
    exact mul_le_mul_of_nonneg_right (hF_bd y) (abs_nonneg _)
  have h_int_G' :
      Integrable (fun y => hermiteFun n y * deriv F y * pdf y -
        hermiteFun (n + 1) y * F y * pdf y) := h_int_HF'pdf.sub h_int_HFpdf
  -- ∫_ℝ G' = 0 by FTC at both infinities.
  have h_int_zero :
      ∫ y, hermiteFun n y * deriv F y * pdf y -
        hermiteFun (n + 1) y * F y * pdf y = 0 := by
    have := integral_of_hasDerivAt_of_tendsto hG_deriv h_int_G' hG_atBot hG_atTop
    simpa using this
  have h_lebesgue :
      ∫ y, hermiteFun n y * deriv F y * pdf y =
        ∫ y, hermiteFun (n + 1) y * F y * pdf y := by
    have h := h_int_zero
    rw [integral_sub h_int_HF'pdf h_int_HFpdf] at h
    linarith
  -- Convert γ-integrals to Lebesgue via integral_gaussianReal_eq_integral_smul.
  have h_v_ne : (1 : NNReal) ≠ 0 := ne_of_gt zero_lt_one
  have h_lhs :
      ∫ y, hermiteFun n y * deriv F y ∂γ =
        ∫ y, hermiteFun n y * deriv F y * pdf y := by
    show ∫ y, hermiteFun n y * deriv F y ∂(gaussianReal (0 : ℝ) (1 : NNReal)) = _
    rw [integral_gaussianReal_eq_integral_smul h_v_ne]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show pdf y • (hermiteFun n y * deriv F y) = hermiteFun n y * deriv F y * pdf y
    rw [smul_eq_mul]; ring
  have h_rhs :
      ∫ y, hermiteFun (n + 1) y * F y ∂γ =
        ∫ y, hermiteFun (n + 1) y * F y * pdf y := by
    show ∫ y, hermiteFun (n + 1) y * F y ∂(gaussianReal (0 : ℝ) (1 : NNReal)) = _
    rw [integral_gaussianReal_eq_integral_smul h_v_ne]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show pdf y • (hermiteFun (n + 1) y * F y) = hermiteFun (n + 1) y * F y * pdf y
    rw [smul_eq_mul]; ring
  rw [h_lhs, h_rhs, h_lebesgue]

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
