/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gaussian Concentration of Lipschitz Functions from LSI

This file contains the standard Borell-style / Herbst concentration
theorem: a measure satisfying a log-Sobolev inequality (LSI) with
constant `c > 0` makes Lipschitz functions sub-Gaussian, with rate
`c / L²` where `L` is the Lipschitz constant. Quantitatively:

  μ({x : F x − E_μ F > t}) ≤ exp(−c · t² / (2 L²)).

This is the Otto-Villani / Herbst concentration consequence of LSI.
For the DZ layer's `global_lsi_of_zegarlinski`, this composes to give
sub-Gaussian concentration of Lipschitz observables on the Gibbs
measure. The corollary `lipschitz_concentration_of_zegarlinski`
(in `DobrushinZegarlinski/`) bundles them.

## Status

* `herbst_mgf_bound` — textbook axiom: the moment-generating function
  of `F − E_μ F` is bounded by `exp(L²t²/(2c))` (sub-Gaussian with
  parameter `L²/c`). This is Herbst's lemma proper (BGL §5.4).
* `lipschitz_concentration_of_lsi` — *proven theorem* from
  `herbst_mgf_bound` + Mathlib's Chernoff
  (`measure_ge_le_exp_mul_mgf`).
* `lipschitz_concentration_left_of_lsi` — *proven* by reflection on
  `-F` against the right-tail concentration theorem.

The factoring isolates the deep step (Herbst's lemma — requires
truncation/mollification of test function `exp(λF/2)`) from the
mechanical Chernoff optimization. The latter is now fully proven.

## References

* Bakry, Gentil, Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, §5.4 (Herbst's argument).
* Ledoux, *The Concentration of Measure Phenomenon*, AMS, 2001, §1.
* Otto and Villani, "Generalization of an inequality by Talagrand and
  links with the logarithmic Sobolev inequality," *J. Funct. Anal.*
  173 (2000), §3.
-/

import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Topology.MetricSpace.Lipschitz
import MarkovSemigroups.DobrushinZegarlinski.LocalLSI

noncomputable section

namespace MarkovSemigroups.Abstract

open MeasureTheory MarkovSemigroups.DobrushinZegarlinski ProbabilityTheory
open Real
open scoped NNReal

/-- **Borell-Herbst concentration from LSI (textbook axiom).**

For a measure `μ` on a finite-dimensional inner-product space `E`
satisfying a log-Sobolev inequality with constant `c > 0`, every
`L`-Lipschitz function `F : E → ℝ` is sub-Gaussian:

  μ({x : F x − E_μ F > t}) ≤ exp(−c · t² / (2 L²)).

Reference: Bakry, Gentil, Ledoux, *Analysis and Geometry of Markov
Diffusion Operators*, Springer, 2014, Proposition 5.4.1 (Herbst
argument). Also Ledoux 2001 §1 and Otto-Villani 2000 §3.

Strategy: Apply LSI to the test function `exp(λF/2)`. The entropy
and gradient calculations yield, for the cumulant generating function
`K(λ) = log E_μ exp(λ(F − E_μ F))`,

  λ K'(λ) − K(λ) ≤ L² λ² / (2 c).

Dividing by `λ²` and integrating from `0` (using
`lim_{λ→0⁺} K(λ)/λ = 0` since `F − E_μ F` is centered) gives

  K(λ) ≤ L² λ² / (2 c).

Combined with the Chernoff bound (Markov on `exp(λ X)`), this yields
the sub-Gaussian tail. The argument is standard but technically
delicate to formalize because applying LSI to `exp(λF/2)` requires
exponential integrability that is *equivalent* to the conclusion;
the rigorous treatment uses truncation `F_n = max(min(F, n), -n)`
and a limit argument. We axiomatize the final bound to avoid this
bookkeeping.

(NOT VERIFIED — axiom stands until peer review or full formalization
of the Herbst argument with truncation.)

We axiomatize the *MGF bound* (Herbst's lemma proper); the
concentration `lipschitz_concentration_of_lsi` is then a *theorem*
proved by Mathlib's Chernoff bound `measure_ge_le_exp_mul_mgf`.
This factoring isolates the deep step (Herbst's lemma — derived from
LSI via the test function `exp(λF/2)`) from the mechanical step
(Chernoff optimization). -/
axiom herbst_mgf_bound
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    {F : E → ℝ} {L : ℝ≥0} (hF_lip : LipschitzWith L F)
    (hF_int : Integrable F μ) (t : ℝ) :
    Integrable (fun x => Real.exp (t * (F x - ∫ y, F y ∂μ))) μ ∧
    mgf (fun x => F x - ∫ y, F y ∂μ) μ t
      ≤ Real.exp ((L : ℝ) ^ 2 * t ^ 2 / (2 * c))

/-- **Borell-Herbst concentration from LSI (theorem).**

For `μ` satisfying LSI with constant `c > 0` and an `L`-Lipschitz `F`:

  μ({x : F x − E_μ F > t}) ≤ exp(−c · t² / (2 L²)).

Derived from `herbst_mgf_bound` (the textbook axiom) by Chernoff
optimization. The optimal multiplier in the Chernoff bound is
`τ = c · t / L²`, which substitutes into the MGF bound
`mgf X μ τ ≤ exp(L² τ² / (2 c))` to give the optimized exponent. -/
theorem lipschitz_concentration_of_lsi
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    {F : E → ℝ} {L : ℝ≥0} (hF_lip : LipschitzWith L F)
    (hF_int : Integrable F μ)
    (t : ℝ) (ht : 0 ≤ t) :
    (μ {x | F x - ∫ y, F y ∂μ > t}).toReal
      ≤ Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2)) := by
  set X : E → ℝ := fun x => F x - ∫ y, F y ∂μ with hX
  -- Case split on L = 0 (constant F).
  rcases eq_or_lt_of_le (NNReal.coe_nonneg L) with hL_zero | hL_pos
  · -- L = 0: RHS = exp(0) = 1; LHS is a probability ≤ 1.
    have hL_eq : (L : ℝ) = 0 := hL_zero.symm
    have h_rhs_one :
        Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2)) = 1 := by
      rw [hL_eq]; simp
    rw [h_rhs_one]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp only [ENNReal.ofReal_one]
    exact (measure_mono (Set.subset_univ _)).trans (le_of_eq measure_univ)
  -- L > 0: choose Chernoff multiplier τ = c · t / L².
  have hc_pos : 0 < c := h_lsi.c_pos
  set τ : ℝ := c * t / (L : ℝ) ^ 2 with hτ
  have hτ_nn : 0 ≤ τ := by
    apply div_nonneg
    · exact mul_nonneg hc_pos.le ht
    · exact sq_nonneg _
  obtain ⟨h_int_τ, h_mgf_τ⟩ := herbst_mgf_bound h_lsi hF_lip hF_int τ
  have h_cher := measure_ge_le_exp_mul_mgf (X := X) (μ := μ) t hτ_nn h_int_τ
  have h_combined :
      μ.real {x | t ≤ X x}
        ≤ Real.exp (-τ * t) * Real.exp ((L : ℝ) ^ 2 * τ ^ 2 / (2 * c)) :=
    h_cher.trans (mul_le_mul_of_nonneg_left h_mgf_τ (Real.exp_pos _).le)
  -- Algebra: -τ·t + L²·τ²/(2c) = -c·t²/(2L²) where τ = c·t/L².
  have h_exp_eq :
      Real.exp (-τ * t) * Real.exp ((L : ℝ) ^ 2 * τ ^ 2 / (2 * c))
        = Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    have hLsq_ne : (L : ℝ) ^ 2 ≠ 0 := ne_of_gt (pow_pos hL_pos 2)
    have hc_ne : c ≠ 0 := ne_of_gt hc_pos
    show -τ * t + (L : ℝ) ^ 2 * τ ^ 2 / (2 * c)
          = -c * t ^ 2 / (2 * (L : ℝ) ^ 2)
    rw [hτ]
    field_simp
    ring
  rw [h_exp_eq] at h_combined
  -- Pass from {≥ t} to {> t}.
  have h_subset : {x | X x > t} ⊆ {x | t ≤ X x} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact hx.le
  have h_mono : (μ {x | X x > t}).toReal ≤ μ.real {x | t ≤ X x} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h_subset)
  exact h_mono.trans h_combined

/-- **Left-tail concentration.**

Direct application of the axiom to `-F`: `μ({x : F x − E_μ F < −t}) ≤
exp(−c · t² / (2 L²))`. The factor-of-2 two-sided bound is obtained
by combining this with the right-tail axiom via the union bound,
and is left to the caller. -/
theorem lipschitz_concentration_left_of_lsi
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    {F : E → ℝ} {L : ℝ≥0} (hF_lip : LipschitzWith L F)
    (hF_int : Integrable F μ)
    (t : ℝ) (ht : 0 ≤ t) :
    (μ {x | F x - ∫ y, F y ∂μ < -t}).toReal
      ≤ Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2)) := by
  have h := lipschitz_concentration_of_lsi h_lsi hF_lip.neg hF_int.neg t ht
  -- The set `{x | (-F) x - ∫ y, (-F) y ∂μ > t}` equals `{x | F x - ∫ y, F y ∂μ < -t}`.
  have h_set_eq :
      {x | (-F) x - ∫ y, (-F) y ∂μ > t}
        = {x | F x - ∫ y, F y ∂μ < -t} := by
    ext x
    simp only [Set.mem_setOf_eq, Pi.neg_apply, integral_neg]
    constructor
    · intro hx; linarith
    · intro hx; linarith
  rw [h_set_eq] at h
  exact h

/-! ### Mathlib `HasSubgaussianMGF` interop

For downstream use with Mathlib's sub-Gaussian framework
(`ProbabilityTheory.HasSubgaussianMGF`): the centered Lipschitz
function under LSI is sub-Gaussian with variance proxy `L²/c`.
This bridge lets consumers feed our Herbst MGF bound into any
Mathlib lemma that expects `HasSubgaussianMGF`. -/

/-- **Bridge: LSI ⇒ HasSubgaussianMGF.**

The centered random variable `F − E_μ F` is sub-Gaussian (in
Mathlib's sense) with variance proxy `L² / c`, given LSI(c) and
`L`-Lipschitz `F`. -/
theorem hasSubgaussianMGF_of_lsi
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    {F : E → ℝ} {L : ℝ≥0} (hF_lip : LipschitzWith L F)
    (hF_int : Integrable F μ) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun x => F x - ∫ y, F y ∂μ)
      ⟨(L : ℝ) ^ 2 / c, div_nonneg (sq_nonneg _) h_lsi.c_pos.le⟩
      μ where
  integrable_exp_mul := fun t =>
    (herbst_mgf_bound h_lsi hF_lip hF_int t).1
  mgf_le := fun t => by
    -- Mathlib form: `mgf X μ t ≤ exp(c_sg · t² / 2)` where c_sg = L²/c.
    -- Our form: `mgf X μ t ≤ exp(L² · t² / (2c))`.
    -- These coincide: `c_sg · t² / 2 = (L²/c) · t² / 2 = L² · t² / (2c)`.
    have h_mgf := (herbst_mgf_bound h_lsi hF_lip hF_int t).2
    refine h_mgf.trans (le_of_eq ?_)
    congr 1
    show (L : ℝ) ^ 2 * t ^ 2 / (2 * c)
          = (⟨(L : ℝ) ^ 2 / c, _⟩ : ℝ≥0) * t ^ 2 / 2
    have hc_ne : c ≠ 0 := ne_of_gt h_lsi.c_pos
    show (L : ℝ) ^ 2 * t ^ 2 / (2 * c)
          = ((L : ℝ) ^ 2 / c) * t ^ 2 / 2
    field_simp

/-- **L^p integrability of Lipschitz F under LSI.**

Direct corollary of `hasSubgaussianMGF_of_lsi` via Mathlib's
`HasSubgaussianMGF.memLp`: any L-Lipschitz F is in `L^p(μ)` for
every `p`, given LSI(c) and `Integrable F μ`. The sub-Gaussian
tails imply finite moments of all orders. -/
theorem memLp_of_lsi
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    {F : E → ℝ} {L : ℝ≥0} (hF_lip : LipschitzWith L F)
    (hF_int : Integrable F μ) (p : ℝ≥0) :
    MeasureTheory.MemLp (fun x => F x - ∫ y, F y ∂μ) p μ :=
  (hasSubgaussianMGF_of_lsi h_lsi hF_lip hF_int).memLp p

/-- **Two-sided Lipschitz concentration from LSI.**

Combines the one-sided concentration with its left-tail companion
via a union bound:

  μ({|F − E_μ F| > t}) ≤ 2 · exp(−c · t² / (2 L²)).

Proof: `{|X| > t} = {X > t} ∪ {-X > t}` (where X = F − E F), apply
the one-sided bound to X and to -X (which is L-Lipschitz with the
same constant), union bound. -/
theorem lipschitz_concentration_two_sided_of_lsi
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    {F : E → ℝ} {L : ℝ≥0} (hF_lip : LipschitzWith L F)
    (hF_int : Integrable F μ)
    (t : ℝ) (ht : 0 ≤ t) :
    (μ {x | t < |F x - ∫ y, F y ∂μ|}).toReal
      ≤ 2 * Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2)) := by
  set X : E → ℝ := fun x => F x - ∫ y, F y ∂μ with hX
  -- {|X| > t} ⊆ {X > t} ∪ {-X > t}
  have h_subset :
      {x | t < |X x|} ⊆ {x | X x > t} ∪ {x | -X x > t} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rcases abs_cases (X x) with ⟨heq, _⟩ | ⟨heq, _⟩
    · -- |X x| = X x (≥ 0): conclude X x > t.
      left; rw [heq] at hx; exact hx
    · -- |X x| = -X x: conclude -X x > t.
      right
      simp only [Set.mem_union, Set.mem_setOf_eq]
      rw [heq] at hx; exact hx
  have h_right := lipschitz_concentration_of_lsi h_lsi hF_lip hF_int t ht
  -- For -F: still L-Lipschitz, integrable; gives {(-F) − ∫(-F) > t}.
  -- That set equals {-X > t} since (-F) − ∫(-F) = -F + ∫F = -X.
  have h_left_raw :=
    lipschitz_concentration_of_lsi h_lsi hF_lip.neg hF_int.neg t ht
  have h_left_set_eq :
      {x | (- F) x - ∫ y, (- F) y ∂μ > t} = {x | -X x > t} := by
    ext x
    simp only [Set.mem_setOf_eq, Pi.neg_apply, integral_neg, hX]
    constructor
    · intro hx; linarith
    · intro hx; linarith
  rw [h_left_set_eq] at h_left_raw
  -- Combine.
  calc (μ {x | t < |X x|}).toReal
      ≤ (μ ({x | X x > t} ∪ {x | -X x > t})).toReal := by
        refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
        exact measure_mono h_subset
    _ ≤ (μ {x | X x > t}).toReal + (μ {x | -X x > t}).toReal := by
        rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        refine ENNReal.toReal_mono ?_ (measure_union_le _ _)
        rw [Ne, ENNReal.add_eq_top, not_or]
        exact ⟨measure_ne_top _ _, measure_ne_top _ _⟩
    _ ≤ Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2))
        + Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2)) := by
        linarith
    _ = 2 * Real.exp (- c * t ^ 2 / (2 * (L : ℝ) ^ 2)) := by ring

/-! ### LSI ⇒ Poincaré → variance bound -/

/-- **LSI implies Poincaré (textbook axiom).**

`SatisfiesLSI μ c` implies the Poincaré inequality with the same
constant: for every differentiable `f : E → ℝ` with `f, f²` integrable
and `‖∇f‖²` integrable,

  Var_μ(f) ≤ (1/c) · ∫ ‖∇f‖² dμ.

Reference: Bakry, Gentil, Ledoux, *Analysis and Geometry of Markov
Diffusion Operators*, Springer, 2014, Proposition 5.1.3.

Strategy: linearize the LSI on `f = 1 + εg` and take ε → 0; the
quadratic term yields exactly the Poincaré inequality. Equivalently,
follows from `logSobolev_implies_poincare_bounded` in
`Abstract/DirichletForm.lean` once a bridge between the thin
`SatisfiesLSI` predicate and the Dirichlet-form `SatisfiesLogSobolev`
is in place (see REFACTOR_NOTES §2).

(NOT VERIFIED — axiom stands until peer review or formalization of
the linearization argument / DirichletForm bridge.) -/
axiom poincare_of_lsi
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    (f : E → ℝ) (hf : Differentiable ℝ f)
    (hf_int : Integrable f μ)
    (hf_sq_int : Integrable (fun x => (f x) ^ 2) μ)
    (hgrad_int : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) μ) :
    ProbabilityTheory.variance f μ ≤ (1 / c) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ

/-- **Variance bound for Lipschitz observables under LSI.**

For an L-Lipschitz `F` under `LSI(c)`,

  Var_μ(F) ≤ L² / c.

Direct corollary of `poincare_of_lsi` plus the bound `‖∇F‖ ≤ L` a.e.
for L-Lipschitz F (Rademacher in finite dim).

Currently `sorry` in the gradient bound: `Differentiable F` doesn't
syntactically carry `‖fderiv ℝ F x‖ ≤ L` for L-Lipschitz; this is
true but requires a separate Mathlib-level lemma (the operator-norm
of fderiv of a Lipschitz function is bounded by the Lipschitz
constant, e.g. `LipschitzWith.norm_fderiv_le`). The remaining
hypotheses (integrability) are user-supplied. -/
theorem variance_lipschitz_le_of_lsi
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsProbabilityMeasure μ] {c : ℝ}
    (h_lsi : SatisfiesLSI μ c)
    {F : E → ℝ} {L : ℝ≥0} (hF_lip : LipschitzWith L F)
    (hF_diff : Differentiable ℝ F)
    (hF_int : Integrable F μ)
    (hF_sq_int : Integrable (fun x => (F x) ^ 2) μ)
    (hgrad_int : Integrable (fun x => ‖fderiv ℝ F x‖ ^ 2) μ) :
    ProbabilityTheory.variance F μ ≤ ((L : ℝ) ^ 2) / c := by
  have h_poincare := poincare_of_lsi h_lsi F hF_diff hF_int hF_sq_int hgrad_int
  -- Bound: ∫ ‖fderiv ℝ F x‖² ∂μ ≤ L²·μ(univ) = L².
  have h_grad_pt : ∀ x, ‖fderiv ℝ F x‖ ≤ (L : ℝ) :=
    fun x => norm_fderiv_le_of_lipschitz ℝ hF_lip
  have h_grad_sq_le : ∀ x, ‖fderiv ℝ F x‖ ^ 2 ≤ (L : ℝ) ^ 2 := fun x =>
    pow_le_pow_left₀ (norm_nonneg _) (h_grad_pt x) 2
  have h_int_grad_le : ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂μ ≤ (L : ℝ) ^ 2 := by
    calc ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂μ
        ≤ ∫ _, (L : ℝ) ^ 2 ∂μ :=
          integral_mono hgrad_int (integrable_const _) h_grad_sq_le
      _ = (L : ℝ) ^ 2 := by
          rw [integral_const]
          simp
  have hc_pos : 0 < c := h_lsi.c_pos
  have hc_inv_nn : 0 ≤ 1 / c := div_nonneg zero_le_one hc_pos.le
  calc ProbabilityTheory.variance F μ
      ≤ (1 / c) * ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂μ := h_poincare
    _ ≤ (1 / c) * (L : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left h_int_grad_le hc_inv_nn
    _ = (L : ℝ) ^ 2 / c := by ring

end MarkovSemigroups.Abstract

end
