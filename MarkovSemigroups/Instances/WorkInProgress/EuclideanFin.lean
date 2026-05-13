/- 
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multivariate Gaussian Bakry-Emery Instance

Concrete finite-dimensional Gaussian data for the Stage N1 multivariate
Bakry-Emery construction.
-/

import MarkovSemigroups.Instances.WorkInProgress.Euclidean
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory Filter Set Real ProbabilityTheory

noncomputable section

namespace GaussianFin

open scoped BigOperators

variable {n : ℕ}

/-- The standard Gaussian product measure on `Fin n → ℝ`. -/
def γFin (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => Gaussian1D.γ)

instance instIsProbabilityMeasureγFin (n : ℕ) : IsProbabilityMeasure (γFin n) := by
  unfold γFin
  infer_instance

/-- The affine Mehler shift on `(Fin n → ℝ)`. -/
def ouShiftFin (t : ℝ) (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => exp (-t) * x i + sqrt (1 - exp (-2 * t)) * y i

/-- The multivariate Ornstein-Uhlenbeck semigroup via the Mehler formula. -/
def ouSemigroupFin (t : ℝ) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => ∫ y, f (ouShiftFin t x y) ∂γFin n

/-- Coordinate partial derivative along the `i`-th standard basis vector. -/
def partialDeriv (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- Second coordinate derivative along the `i`-th standard basis vector. -/
def secondPartial (i : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ (partialDeriv i f) x (Pi.single i 1)

/-- The multivariate carré du champ: sum of squared coordinate derivatives. -/
def ouGammaFin (f g : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => ∑ i : Fin n, partialDeriv i f x * partialDeriv i g x

/-- Core test functions for the finite-dimensional Gaussian OU semigroup.

We require:
- `C^∞` regularity;
- a global bound on the function values;
- a uniform global bound on all coordinate first and second partials.

This is the direct finite-dimensional analogue of `Gaussian1D.IsCore`. -/
def IsCoreFin (f : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ⊤ f ∧ ∃ M : ℝ,
    ∀ x, ‖f x‖ ≤ M ∧
      (∀ i : Fin n, ‖partialDeriv i f x‖ ≤ M) ∧
      ∀ i : Fin n, ‖secondPartial i f x‖ ≤ M

theorem IsCoreFin.contDiff {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ContDiff ℝ ⊤ f := hf.1

theorem IsCoreFin.bound_exists {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨_, M, hM⟩ := hf
  exact ⟨M, fun x => (hM x).1⟩

theorem IsCoreFin.continuous {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    Continuous f := hf.contDiff.continuous

theorem IsCoreFin.measurable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    Measurable f := hf.continuous.measurable

theorem IsCoreFin.stronglyMeasurable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    StronglyMeasurable f := hf.continuous.stronglyMeasurable

theorem IsCoreFin.partial_contDiff {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) :
    ContDiff ℝ ⊤ (partialDeriv i f) := by
  unfold partialDeriv
  simpa using (hf.contDiff.fderiv_right (m := ⊤) (by simp)).clm_apply contDiff_const

theorem IsCoreFin.partial_differentiable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) :
    Differentiable ℝ (partialDeriv i f) :=
  (hf.partial_contDiff i).differentiable (by simp)

theorem IsCoreFin.partial_continuous {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) :
    Continuous (partialDeriv i f) := (hf.partial_contDiff i).continuous

theorem IsCoreFin.partial_measurable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) :
    Measurable (partialDeriv i f) := (hf.partial_continuous i).measurable

theorem IsCoreFin.partial_stronglyMeasurable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) : StronglyMeasurable (partialDeriv i f) :=
  (hf.partial_continuous i).stronglyMeasurable

/-- Restrict a multivariate function to the `i`-th coordinate line through `x`. -/
def coordSection (i : Fin n) (x : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) : ℝ → ℝ :=
  fun s => f (Function.update x i s)

theorem section_contDiff {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ⊤ f)
    (i : Fin n) (x : Fin n → ℝ) :
    ContDiff ℝ ⊤ (coordSection i x f) := by
  unfold coordSection
  exact hf.comp (contDiff_update ⊤ x i)

theorem section_hasDerivAt {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ⊤ f)
    (i : Fin n) (x : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (coordSection i x f)
      (partialDeriv i f (Function.update x i s)) s := by
  unfold coordSection partialDeriv
  have h_update := hasDerivAt_update x i s
  have h_f : HasFDerivAt f (fderiv ℝ f (Function.update x i s)) (Function.update x i s) :=
    ((hf.differentiable (by simp)).differentiableAt).hasFDerivAt
  simpa [partialDeriv] using h_f.comp_hasDerivAt s h_update

theorem section_deriv {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ⊤ f)
    (i : Fin n) (x : Fin n → ℝ) :
    deriv (coordSection i x f) = fun s => partialDeriv i f (Function.update x i s) := by
  funext s
  exact (section_hasDerivAt hf i x s).deriv

theorem partialDeriv_update_hasDerivAt {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) (x : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun t => partialDeriv i f (Function.update x i t))
      (secondPartial i f (Function.update x i s)) s := by
  unfold partialDeriv secondPartial
  have h_update := hasDerivAt_update x i s
  have h_f : HasFDerivAt (partialDeriv i f)
      (fderiv ℝ (partialDeriv i f) (Function.update x i s))
      (Function.update x i s) :=
    ((hf.partial_differentiable i).differentiableAt).hasFDerivAt
  simpa [secondPartial] using h_f.comp_hasDerivAt s h_update

theorem section_secondDeriv {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) (x : Fin n → ℝ) :
    deriv (deriv (coordSection i x f)) = fun s => secondPartial i f (Function.update x i s) := by
  funext s
  rw [section_deriv hf.contDiff i x]
  exact (partialDeriv_update_hasDerivAt hf i x s).deriv

theorem hasDerivAt_coordSection_ouSemigroupFin_C1
    (t : ℝ) {f : (Fin n → ℝ) → ℝ} (hf_C1 : ContDiff ℝ 1 f)
    (i : Fin n) {M : ℝ} (hM0 : ∀ x, ‖f x‖ ≤ M) (hM1 : ∀ x, ‖partialDeriv i f x‖ ≤ M)
    (x : Fin n → ℝ) (s₀ : ℝ) :
    HasDerivAt (fun s => ouSemigroupFin t f (Function.update x i s))
      (exp (-t) * ouSemigroupFin t (partialDeriv i f) (Function.update x i s₀)) s₀ := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  set F : ℝ → (Fin n → ℝ) → ℝ := fun s y => f (ouShiftFin t (Function.update x i s) y)
  set F' : ℝ → (Fin n → ℝ) → ℝ := fun s y =>
    a * partialDeriv i f (ouShiftFin t (Function.update x i s) y)
  have hs : Set.Ioo (s₀ - 1) (s₀ + 1) ∈ nhds s₀ :=
    Ioo_mem_nhds (sub_lt_self _ zero_lt_one) (lt_add_of_pos_right _ zero_lt_one)
  have hF_meas : ∀ s, AEStronglyMeasurable (F s) (γFin n) := by
    intro s
    have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t (Function.update x i s) y) := by
      continuity
    have hmeas : Measurable (fun y => F s y) := (hf_C1.continuous.comp hcont_shift).measurable
    exact hmeas.aestronglyMeasurable
  have hF_int : Integrable (F s₀) (γFin n) := by
    refine Integrable.mono' (integrable_const M) (hF_meas s₀) ?_
    exact Filter.Eventually.of_forall (fun y => hM0 _)
  have hF'_meas : AEStronglyMeasurable (F' s₀) (γFin n) := by
    have hpartial_cont : Continuous (partialDeriv i f) := by
      unfold partialDeriv
      simpa using (hf_C1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t (Function.update x i s₀) y) := by
      continuity
    have hmeas : Measurable (fun y => F' s₀ y) :=
      (measurable_const.mul (hpartial_cont.comp hcont_shift).measurable)
    exact hmeas.aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂γFin n, ∀ s ∈ Set.Ioo (s₀ - 1) (s₀ + 1), ‖F' s y‖ ≤ |a| * M := by
    refine Filter.Eventually.of_forall ?_
    intro y s hs_mem
    show ‖a * partialDeriv i f (ouShiftFin t (Function.update x i s) y)‖ ≤ |a| * M
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |partialDeriv i f (ouShiftFin t (Function.update x i s) y)| ≤ M := by
      rw [← Real.norm_eq_abs]
      exact hM1 _
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
  have h_bound_int : Integrable (fun _ : Fin n → ℝ => |a| * M) (γFin n) := integrable_const _
  have h_diff :
      ∀ᵐ y ∂γFin n, ∀ s ∈ Set.Ioo (s₀ - 1) (s₀ + 1), HasDerivAt (F · y) (F' s y) s := by
    refine Filter.Eventually.of_forall ?_
    intro y s hs_mem
    show HasDerivAt (fun u => f (ouShiftFin t (Function.update x i u) y))
      (a * partialDeriv i f (ouShiftFin t (Function.update x i s) y)) s
    have h_affine : HasDerivAt (fun u : ℝ => a * u + b * y i) a s := by
      simpa [a, b] using (((hasDerivAt_id s).const_mul a).add_const (b * y i))
    set z : Fin n → ℝ := ouShiftFin t x y
    have h_inner_eq :
        (fun u : ℝ => ouShiftFin t (Function.update x i u) y) =
          fun u => Function.update z i (a * u + b * y i) := by
      funext u
      ext j
      by_cases hji : j = i
      · subst hji
        simp [ouShiftFin, z, a, b]
      · simp [ouShiftFin, z, a, b, hji]
    have h_inner :
        HasDerivAt (fun u : ℝ => ouShiftFin t (Function.update x i u) y)
          (Pi.single i a) s := by
      have htmp : HasDerivAt (fun u : ℝ => Function.update z i (a * u + b * y i))
          (Pi.single i a) s := by
        have hraw :=
          (HasFDerivAt.comp s
            (hasFDerivAt_update z (i := i) (a * s + b * y i))
            h_affine.hasFDerivAt).hasDerivAt
        convert hraw using 1
        ext j
        by_cases hji : j = i
        · subst hji
          simp [ContinuousLinearMap.toSpanSingleton_apply]
        · simp [Pi.single_apply, hji, ContinuousLinearMap.toSpanSingleton_apply]
      simpa [h_inner_eq] using htmp
    have h_f :
        HasFDerivAt f (fderiv ℝ f (ouShiftFin t (Function.update x i s) y))
          (ouShiftFin t (Function.update x i s) y) :=
      ((hf_C1.differentiable (by simp)).differentiableAt).hasFDerivAt
    have h_comp := h_f.comp_hasDerivAt s h_inner
    have htarget :
        (fderiv ℝ f (ouShiftFin t (Function.update x i s) y)) (Pi.single i a) =
          a * partialDeriv i f (ouShiftFin t (Function.update x i s) y) := by
      rw [partialDeriv]
      have hsingle : Pi.single i a = a • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
        ext j
        by_cases hji : j = i
        · subst hji
          simp
        · simp [Pi.single_eq_of_ne hji]
      rw [hsingle, ContinuousLinearMap.map_smul]
      simp [smul_eq_mul]
    simpa [F, F', htarget] using h_comp
  obtain ⟨_, h_deriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
      (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas h_bound h_bound_int h_diff
  have h_lhs : (fun s => ∫ y, F s y ∂γFin n) =
      fun s => ouSemigroupFin t f (Function.update x i s) := rfl
  have h_rhs :
      ∫ y, F' s₀ y ∂γFin n =
        a * ouSemigroupFin t (partialDeriv i f) (Function.update x i s₀) := by
    rw [show (fun y => F' s₀ y) =
        (fun y => a * partialDeriv i f (ouShiftFin t (Function.update x i s₀) y)) from rfl]
    rw [integral_const_mul]
    rfl
  simpa [h_lhs, h_rhs, a] using h_deriv

theorem section_deriv_ouSemigroupFin_eq {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (t : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    deriv (fun s => ouSemigroupFin t f (Function.update x i s)) =
      fun s => exp (-t) * ouSemigroupFin t (partialDeriv i f) (Function.update x i s) := by
  have hf_core : IsCoreFin f := hf
  have hf_cont : ContDiff ℝ ⊤ f := hf.contDiff
  obtain ⟨_, M, hM⟩ := hf
  funext s
  exact (hasDerivAt_coordSection_ouSemigroupFin_C1 (t := t)
    (hf_C1 := hf_cont.of_le (by simp : (1 : WithTop ℕ∞) ≤ ⊤))
    (i := i)
    (hM0 := fun z => (hM z).1)
    (hM1 := fun z => (hM z).2.1 i)
    (x := x) (s₀ := s)).deriv

theorem section_secondDeriv_ouSemigroupFin_eq {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (t : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    deriv (deriv (fun s => ouSemigroupFin t f (Function.update x i s))) =
      fun s => exp (-2 * t) * ouSemigroupFin t (secondPartial i f) (Function.update x i s) := by
  have hf_core : IsCoreFin f := hf
  have hf_partial : ContDiff ℝ ⊤ (partialDeriv i f) := hf.partial_contDiff i
  obtain ⟨_, M, hM⟩ := hf
  funext s
  have h :=
    hasDerivAt_coordSection_ouSemigroupFin_C1 (t := t)
      (hf_C1 := hf_partial.of_le (by simp : (1 : WithTop ℕ∞) ≤ ⊤))
      (i := i)
      (hM0 := fun z => (hM z).2.1 i)
      (hM1 := fun z => (hM z).2.2 i)
      (x := x) (s₀ := s)
  calc
    deriv (deriv (fun s => ouSemigroupFin t f (Function.update x i s))) s
        = deriv (fun s => exp (-t) * ouSemigroupFin t (partialDeriv i f) (Function.update x i s)) s := by
            rw [section_deriv_ouSemigroupFin_eq hf_core t i x]
    _ = exp (-2 * t) * ouSemigroupFin t (secondPartial i f) (Function.update x i s) := by
          have hscaled : HasDerivAt
              (fun s => exp (-t) * ouSemigroupFin t (partialDeriv i f) (Function.update x i s))
              (exp (-t) * (exp (-t) * ouSemigroupFin t (secondPartial i f) (Function.update x i s))) s := by
            simpa [secondPartial] using h.const_mul (exp (-t))
          have hdscaled := hscaled.deriv
          rw [show exp (-2 * t) = exp (-t) * exp (-t) by
            rw [show (-2 * t : ℝ) = -t + -t by ring, exp_add]]
          simpa [mul_assoc] using hdscaled

theorem IsCoreFin.section_isCore {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) (x : Fin n → ℝ) :
    Gaussian1D.IsCore (coordSection i x f) := by
  obtain ⟨hf_smooth, M, hM⟩ := hf
  have hf_core : IsCoreFin f := ⟨hf_smooth, M, hM⟩
  refine ⟨section_contDiff hf_smooth i x, ⟨M, fun s => ?_⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [coordSection] using (hM (Function.update x i s)).1
  · rw [section_deriv hf_smooth i x]
    simpa [coordSection] using (hM (Function.update x i s)).2.1 i
  · rw [section_secondDeriv hf_core i x]
    simpa [coordSection] using (hM (Function.update x i s)).2.2 i

theorem IsCoreFin.integrable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    Integrable f (γFin n) := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  refine Integrable.mono' (integrable_const M) hf.stronglyMeasurable.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall hM

theorem IsCoreFin.integrable_partial_mul {f g : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (hg : IsCoreFin g) (i : Fin n) :
    Integrable (fun x => partialDeriv i f x * partialDeriv i g x) (γFin n) := by
  obtain ⟨hf_smooth, Mf, hfM⟩ := hf
  obtain ⟨hg_smooth, Mg, hgM⟩ := hg
  have hf_core : IsCoreFin f := ⟨hf_smooth, Mf, hfM⟩
  have hg_core : IsCoreFin g := ⟨hg_smooth, Mg, hgM⟩
  let M := Mf * Mg
  have hmf : Measurable (partialDeriv i f) :=
    (hf_core.partial_continuous i).measurable
  have hmg : Measurable (partialDeriv i g) :=
    (hg_core.partial_continuous i).measurable
  refine Integrable.mono' (integrable_const M)
    (hmf.mul hmg).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  rw [norm_mul]
  have hMf_nn : 0 ≤ Mf := (norm_nonneg _).trans (hfM 0).1
  exact mul_le_mul ((hfM x).2.1 i) ((hgM x).2.1 i) (norm_nonneg _) hMf_nn

theorem IsCoreFin.integrable_sq {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    Integrable (fun x => (f x) ^ 2) (γFin n) := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  refine Integrable.mono' (integrable_const (M ^ 2))
    ((hf.measurable.pow_const 2).aemeasurable.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hx : |f x| ≤ M := by
    rw [← Real.norm_eq_abs]
    exact hM x
  have hx2 : (f x) ^ 2 ≤ M ^ 2 := by
    have : |f x| ^ 2 ≤ M ^ 2 := by nlinarith [abs_nonneg (f x)]
    rwa [sq_abs] at this
  have hnorm : ‖M ^ 2‖ = M ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  linarith

/-- Dirichlet energy for the multivariate Gaussian candidate. -/
def ouEnergyFin (f g : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, ouGammaFin f g x ∂γFin n

@[simp] theorem partialDeriv_const (i : Fin n) (c : ℝ) :
    partialDeriv i (fun _ : Fin n → ℝ => c) = 0 := by
  funext x
  simp [partialDeriv]

@[simp] theorem secondPartial_const (i : Fin n) (c : ℝ) :
    secondPartial i (fun _ : Fin n → ℝ => c) = 0 := by
  funext x
  simp [secondPartial]

theorem IsCoreFin_const (c : ℝ) : IsCoreFin (fun _ : Fin n → ℝ => c) := by
  refine ⟨contDiff_const, ⟨‖c‖, fun x => ?_⟩⟩
  refine ⟨le_rfl, ?_, ?_⟩
  · intro i
    simp [partialDeriv_const]
  · intro i
    simp [secondPartial_const]

theorem IsCoreFin_add {f g : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (hg : IsCoreFin g) :
    IsCoreFin (f + g) := by
  obtain ⟨hf_smooth, Mf, hfM⟩ := hf
  obtain ⟨hg_smooth, Mg, hgM⟩ := hg
  refine ⟨hf_smooth.add hg_smooth, ⟨Mf + Mg, fun x => ?_⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · calc
      ‖(f + g) x‖ = ‖f x + g x‖ := rfl
      _ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
      _ ≤ Mf + Mg := add_le_add (hfM x).1 (hgM x).1
  · intro i
    have hdf : DifferentiableAt ℝ f x := (hf_smooth.differentiable (by simp)).differentiableAt
    have hdg : DifferentiableAt ℝ g x := (hg_smooth.differentiable (by simp)).differentiableAt
    unfold partialDeriv
    rw [fderiv_add hdf hdg, ContinuousLinearMap.add_apply]
    calc
      ‖partialDeriv i f x + partialDeriv i g x‖
        ≤ ‖partialDeriv i f x‖ + ‖partialDeriv i g x‖ := norm_add_le _ _
      _ ≤ Mf + Mg := add_le_add ((hfM x).2.1 i) ((hgM x).2.1 i)
  · intro i
    have hpartialf_smooth : ContDiff ℝ ⊤ (partialDeriv i f) := by
      unfold partialDeriv
      simpa using (hf_smooth.fderiv_right (m := ⊤) (by simp)).clm_apply contDiff_const
    have hpartialg_smooth : ContDiff ℝ ⊤ (partialDeriv i g) := by
      unfold partialDeriv
      simpa using (hg_smooth.fderiv_right (m := ⊤) (by simp)).clm_apply contDiff_const
    have hdf' : DifferentiableAt ℝ (partialDeriv i f) x := (hpartialf_smooth.differentiable (by simp)).differentiableAt
    have hdg' : DifferentiableAt ℝ (partialDeriv i g) x := (hpartialg_smooth.differentiable (by simp)).differentiableAt
    unfold secondPartial
    have hpartial_add : partialDeriv i (f + g) = fun y => partialDeriv i f y + partialDeriv i g y := by
      funext y
      have hdfy : DifferentiableAt ℝ f y := (hf_smooth.differentiable (by simp)).differentiableAt
      have hdgy : DifferentiableAt ℝ g y := (hg_smooth.differentiable (by simp)).differentiableAt
      unfold partialDeriv
      rw [fderiv_add hdfy hdgy, ContinuousLinearMap.add_apply]
    rw [hpartial_add]
    change ‖(fderiv ℝ ((partialDeriv i f) + (partialDeriv i g)) x) (Pi.single i 1)‖ ≤ Mf + Mg
    rw [fderiv_add hdf' hdg', ContinuousLinearMap.add_apply]
    calc
      ‖secondPartial i f x + secondPartial i g x‖
        ≤ ‖secondPartial i f x‖ + ‖secondPartial i g x‖ := norm_add_le _ _
      _ ≤ Mf + Mg := add_le_add ((hfM x).2.2 i) ((hgM x).2.2 i)

theorem IsCoreFin_smul (c : ℝ) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    IsCoreFin (c • f) := by
  obtain ⟨hf_smooth, M, hM⟩ := hf
  refine ⟨hf_smooth.const_smul c, ⟨‖c‖ * M, fun x => ?_⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · calc
      ‖(c • f) x‖ = ‖c * f x‖ := by simp [Pi.smul_apply]
      _ = ‖c‖ * ‖f x‖ := norm_mul _ _
      _ ≤ ‖c‖ * M := mul_le_mul_of_nonneg_left (hM x).1 (norm_nonneg _)
  · intro i
    have hsmul : fderiv ℝ (c • f) x = c • fderiv ℝ f x := by
      exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (f := f) (c := c)) x
    rw [partialDeriv, hsmul]
    simp only [smul_eq_mul, ContinuousLinearMap.smul_apply]
    calc
      ‖c * partialDeriv i f x‖ = ‖c‖ * ‖partialDeriv i f x‖ := norm_mul _ _
      _ ≤ ‖c‖ * M := mul_le_mul_of_nonneg_left ((hM x).2.1 i) (norm_nonneg _)
  · intro i
    rw [secondPartial]
    have hpartial :
        partialDeriv i (c • f) = fun y => c * partialDeriv i f y := by
      funext y
      have hsmul : fderiv ℝ (c • f) y = c • fderiv ℝ f y := by
        exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (f := f) (c := c)) y
      rw [partialDeriv, hsmul]
      simp [partialDeriv, smul_eq_mul, ContinuousLinearMap.smul_apply]
    rw [hpartial]
    change ‖(fderiv ℝ (c • partialDeriv i f) x) (Pi.single i 1)‖ ≤ ‖c‖ * M
    have hsmul : fderiv ℝ (c • partialDeriv i f) x =
        c • fderiv ℝ (partialDeriv i f) x := by
      exact congrFun
        (fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (f := partialDeriv i f) (c := c)) x
    rw [hsmul]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    calc
      ‖c * secondPartial i f x‖ = ‖c‖ * ‖secondPartial i f x‖ := norm_mul _ _
      _ ≤ ‖c‖ * M := mul_le_mul_of_nonneg_left ((hM x).2.2 i) (norm_nonneg _)

theorem partialDeriv_mul (i : Fin n) {f g : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) :
    partialDeriv i (f * g) = fun x => partialDeriv i f x * g x + f x * partialDeriv i g x := by
  funext x
  have hdf : DifferentiableAt ℝ f x := (hf.differentiable (by simp)).differentiableAt
  have hdg : DifferentiableAt ℝ g x := (hg.differentiable (by simp)).differentiableAt
  unfold partialDeriv
  rw [fderiv_mul hdf hdg, ContinuousLinearMap.add_apply]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem IsCoreFin_mul {f g : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (hg : IsCoreFin g) :
    IsCoreFin (f * g) := by
  obtain ⟨hf_smooth, Mf, hfM⟩ := hf
  obtain ⟨hg_smooth, Mg, hgM⟩ := hg
  refine ⟨hf_smooth.mul hg_smooth, ⟨Mf * Mg + 2 * (Mf * Mg) + Mf * Mg, fun x => ?_⟩⟩
  have hMf_nn : 0 ≤ Mf := (norm_nonneg _).trans (hfM 0).1
  have hMg_nn : 0 ≤ Mg := (norm_nonneg _).trans (hgM 0).1
  refine ⟨?_, ?_, ?_⟩
  · calc
      ‖(f * g) x‖ = ‖f x * g x‖ := rfl
      _ = ‖f x‖ * ‖g x‖ := norm_mul _ _
      _ ≤ Mf * Mg := mul_le_mul (hfM x).1 (hgM x).1 (norm_nonneg _) hMf_nn
      _ ≤ Mf * Mg + 2 * (Mf * Mg) + Mf * Mg := by nlinarith
  · intro i
    rw [partialDeriv_mul i hf_smooth hg_smooth]
    have h1 : ‖partialDeriv i f x * g x‖ ≤ Mf * Mg := by
      rw [norm_mul]
      exact mul_le_mul ((hfM x).2.1 i) (hgM x).1 (norm_nonneg _) hMf_nn
    have h2 : ‖f x * partialDeriv i g x‖ ≤ Mf * Mg := by
      rw [norm_mul]
      exact mul_le_mul (hfM x).1 ((hgM x).2.1 i) (norm_nonneg _) hMf_nn
    calc
      ‖partialDeriv i f x * g x + f x * partialDeriv i g x‖
        ≤ ‖partialDeriv i f x * g x‖ + ‖f x * partialDeriv i g x‖ := norm_add_le _ _
      _ ≤ Mf * Mg + Mf * Mg := add_le_add h1 h2
      _ ≤ Mf * Mg + 2 * (Mf * Mg) + Mf * Mg := by nlinarith
  · intro i
    have hdf : DifferentiableAt ℝ f x := (hf_smooth.differentiable (by simp)).differentiableAt
    have hdg : DifferentiableAt ℝ g x := (hg_smooth.differentiable (by simp)).differentiableAt
    have hpartialf_smooth : ContDiff ℝ ⊤ (partialDeriv i f) := by
      unfold partialDeriv
      simpa using (hf_smooth.fderiv_right (m := ⊤) (by simp)).clm_apply contDiff_const
    have hpartialg_smooth : ContDiff ℝ ⊤ (partialDeriv i g) := by
      unfold partialDeriv
      simpa using (hg_smooth.fderiv_right (m := ⊤) (by simp)).clm_apply contDiff_const
    have hdf' : DifferentiableAt ℝ (partialDeriv i f) x :=
      (hpartialf_smooth.differentiable (by simp)).differentiableAt
    have hdg' : DifferentiableAt ℝ (partialDeriv i g) x :=
      (hpartialg_smooth.differentiable (by simp)).differentiableAt
    rw [secondPartial, partialDeriv_mul i hf_smooth hg_smooth]
    set u : (Fin n → ℝ) → ℝ := fun y => partialDeriv i f y * g y
    set v : (Fin n → ℝ) → ℝ := fun y => f y * partialDeriv i g y
    change ‖(fderiv ℝ (u + v) x) (Pi.single i 1)‖ ≤ Mf * Mg + 2 * (Mf * Mg) + Mf * Mg
    have hadd : fderiv ℝ (u + v) x = fderiv ℝ u x + fderiv ℝ v x := by
      simpa [u, v] using fderiv_add (hdf'.mul hdg) (hdf.mul hdg')
    rw [hadd]
    rw [ContinuousLinearMap.add_apply]
    have hmul1' : fderiv ℝ ((partialDeriv i f) * g) x =
        partialDeriv i f x • fderiv ℝ g x + g x • fderiv ℝ (partialDeriv i f) x := by
      exact fderiv_mul hdf' hdg
    have hmul1 :
        (fderiv ℝ (fun y => partialDeriv i f y * g y) x) (Pi.single i 1) =
          secondPartial i f x * g x + partialDeriv i f x * partialDeriv i g x := by
      rw [show (fun y => partialDeriv i f y * g y) = ((partialDeriv i f) * g) by rfl, hmul1',
        ContinuousLinearMap.add_apply]
      simp [secondPartial, partialDeriv, smul_eq_mul, Pi.smul_apply]
      ring
    have hmul2' : fderiv ℝ (f * partialDeriv i g) x =
        f x • fderiv ℝ (partialDeriv i g) x + partialDeriv i g x • fderiv ℝ f x := by
      exact fderiv_mul hdf hdg'
    have hmul2 :
        (fderiv ℝ (fun y => f y * partialDeriv i g y) x) (Pi.single i 1) =
          partialDeriv i f x * partialDeriv i g x + f x * secondPartial i g x := by
      rw [show (fun y => f y * partialDeriv i g y) = (f * partialDeriv i g) by rfl, hmul2',
        ContinuousLinearMap.add_apply]
      simp [secondPartial, partialDeriv, smul_eq_mul, Pi.smul_apply]
      ring
    rw [hmul1, hmul2]
    have e1 : ‖secondPartial i f x * g x‖ ≤ Mf * Mg := by
      rw [norm_mul]
      exact mul_le_mul ((hfM x).2.2 i) (hgM x).1 (norm_nonneg _) hMf_nn
    have e2 : ‖partialDeriv i f x * partialDeriv i g x‖ ≤ Mf * Mg := by
      rw [norm_mul]
      exact mul_le_mul ((hfM x).2.1 i) ((hgM x).2.1 i) (norm_nonneg _) hMf_nn
    have e3 : ‖f x * secondPartial i g x‖ ≤ Mf * Mg := by
      rw [norm_mul]
      exact mul_le_mul (hfM x).1 ((hgM x).2.2 i) (norm_nonneg _) hMf_nn
    calc
      ‖secondPartial i f x * g x + partialDeriv i f x * partialDeriv i g x +
          (partialDeriv i f x * partialDeriv i g x + f x * secondPartial i g x)‖
        ≤ ‖secondPartial i f x * g x‖ + ‖partialDeriv i f x * partialDeriv i g x‖ +
            (‖partialDeriv i f x * partialDeriv i g x‖ + ‖f x * secondPartial i g x‖) := by
              exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
      _ ≤ Mf * Mg + Mf * Mg + (Mf * Mg + Mf * Mg) := by gcongr
      _ = Mf * Mg + 2 * (Mf * Mg) + Mf * Mg := by ring

@[simp] theorem partialDeriv_smul (i : Fin n) (c : ℝ) {f : (Fin n → ℝ) → ℝ} :
    partialDeriv i (c • f) = fun x => c * partialDeriv i f x := by
  funext x
  have hsmul : fderiv ℝ (c • f) x = c • fderiv ℝ f x := by
    exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (f := f) (c := c)) x
  rw [partialDeriv, hsmul]
  simp [partialDeriv, smul_eq_mul, ContinuousLinearMap.smul_apply]

theorem partialDeriv_add (i : Fin n) {f g : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) :
    partialDeriv i (f + g) = fun x => partialDeriv i f x + partialDeriv i g x := by
  funext x
  have hdf : DifferentiableAt ℝ f x := (hf.differentiable (by simp)).differentiableAt
  have hdg : DifferentiableAt ℝ g x := (hg.differentiable (by simp)).differentiableAt
  unfold partialDeriv
  rw [fderiv_add hdf hdg, ContinuousLinearMap.add_apply]

theorem IsCoreFin.integrable_gamma {f g : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (hg : IsCoreFin g) :
    Integrable (ouGammaFin f g) (γFin n) := by
  simpa [ouGammaFin] using
    (integrable_finset_sum (s := Finset.univ)
      (f := fun i x => partialDeriv i f x * partialDeriv i g x)
      (fun i _ => hf.integrable_partial_mul hg i))

@[reducible]
def dirichletSpaceFin (n : ℕ) : DirichletSpace (Fin n → ℝ) where
  μ := γFin n
  hμ := inferInstance
  energy := ouEnergyFin
  energy_symm := fun f g => by
    simp [ouEnergyFin, ouGammaFin, mul_comm]
  energy_nonneg := fun f => by
    unfold ouEnergyFin ouGammaFin
    refine integral_nonneg ?_
    intro x
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (partialDeriv i f x))
  IsCore := IsCoreFin
  IsCore_const := IsCoreFin_const
  IsCore_add := fun hf hg => IsCoreFin_add hf hg
  IsCore_smul := fun c _ hf => IsCoreFin_smul c hf
  energy_add_left := fun f₁ f₂ g hf₁ hf₂ hg => by
    have hΓ :
        ouGammaFin (f₁ + f₂) g = fun x => ouGammaFin f₁ g x + ouGammaFin f₂ g x := by
      ext x
      unfold ouGammaFin
      have hsum :
          (fun i : Fin n => partialDeriv i (f₁ + f₂) x * partialDeriv i g x) =
            fun i : Fin n =>
              partialDeriv i f₁ x * partialDeriv i g x +
                partialDeriv i f₂ x * partialDeriv i g x := by
        funext i
        rw [partialDeriv_add i hf₁.contDiff hf₂.contDiff]
        ring
      rw [hsum]
      rw [Finset.sum_add_distrib]
    rw [ouEnergyFin, hΓ, integral_add (hf₁.integrable_gamma hg) (hf₂.integrable_gamma hg)]
    rfl
  energy_smul_left := fun c f g hf hg => by
    have hΓ : ouGammaFin (c • f) g = fun x => c * ouGammaFin f g x := by
      ext x
      unfold ouGammaFin
      simp_rw [partialDeriv_smul]
      rw [Finset.mul_sum]
      congr with i
      ring
    rw [ouEnergyFin, hΓ, integral_const_mul]
    rw [ouEnergyFin]
  energy_const := fun c => by
    simp [ouEnergyFin, ouGammaFin, partialDeriv_const]

theorem ouGammaFin_symm {f g : (Fin n → ℝ) → ℝ} :
    ouGammaFin f g = ouGammaFin g f := by
  ext x
  simp [ouGammaFin, mul_comm]

theorem ouGammaFin_nonneg {f : (Fin n → ℝ) → ℝ} (x : Fin n → ℝ) :
    0 ≤ ouGammaFin f f x := by
  unfold ouGammaFin
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (partialDeriv i f x))

theorem ouGammaFin_leibniz {f g h : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (hg : IsCoreFin g) (_hh : IsCoreFin h) (x : Fin n → ℝ) :
    ouGammaFin (f * g) h x = f x * ouGammaFin g h x + g x * ouGammaFin f h x := by
  unfold ouGammaFin
  have hsum :
      (fun i : Fin n => partialDeriv i (f * g) x * partialDeriv i h x) =
        fun i : Fin n =>
          f x * (partialDeriv i g x * partialDeriv i h x) +
            g x * (partialDeriv i f x * partialDeriv i h x) := by
    funext i
    rw [partialDeriv_mul i hf.contDiff hg.contDiff]
    ring
  rw [hsum, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

@[simp] theorem ouGammaFin_const_left (c : ℝ) (f : (Fin n → ℝ) → ℝ) :
    ouGammaFin (fun _ => c) f = 0 := by
  ext x
  simp [ouGammaFin, partialDeriv_const]

@[simp] theorem ouGammaFin_const_right (c : ℝ) (f : (Fin n → ℝ) → ℝ) :
    ouGammaFin f (fun _ => c) = 0 := by
  rw [ouGammaFin_symm, ouGammaFin_const_left]

/-- Linear Gaussian mixing map `(x,y) ↦ a x + b y` on the product space. -/
def mixCLM (a b : ℝ) : ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin n =>
    a • (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)) +
    b • (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))

@[simp] theorem mixCLM_apply (a b : ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    mixCLM (n := n) a b p = fun i => a * p.1 i + b * p.2 i := by
  ext i
  simp [mixCLM, ContinuousLinearMap.pi_apply, Pi.smul_apply]

theorem charFunDual_gamma1D (L : StrongDual ℝ ℝ) :
    charFunDual Gaussian1D.γ L = Complex.exp (-(L 1) ^ 2 / 2) := by
  rw [charFunDual_eq_charFun_map_one, Gaussian1D.γ, gaussianReal_map_continuousLinearMap,
    charFun_gaussianReal]
  congr 1
  simp [sq_nonneg]
  ring

theorem charFunDual_γFin (L : StrongDual ℝ (Fin n → ℝ)) :
    charFunDual (γFin n) L = Complex.exp (-((∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2)) / 2) := by
  rw [show charFunDual (γFin n) L =
      ∏ i : Fin n, charFunDual Gaussian1D.γ (L.comp (.single ℝ (fun _ : Fin n => ℝ) i)) by
    simpa [γFin] using (charFunDual_pi (μ := fun _ : Fin n => Gaussian1D.γ) L)]
  simp_rw [charFunDual_gamma1D]
  simp_rw [ContinuousLinearMap.comp_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp [ContinuousLinearMap.single_apply]
  calc
    ∑ x : Fin n, -↑(L (Pi.single x (1 : ℝ))) ^ 2 / (2 : ℂ)
        = ∑ x : Fin n, (↑(L (Pi.single x (1 : ℝ))) ^ 2 : ℂ) * (-((1 : ℂ) / 2)) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
    _ = (∑ x : Fin n, (↑(L (Pi.single x (1 : ℝ))) ^ 2 : ℂ)) * (-((1 : ℂ) / 2)) := by
          rw [Finset.sum_mul]
    _ = (-∑ x : Fin n, (↑(L (Pi.single x (1 : ℝ))) ^ 2 : ℂ)) / (2 : ℂ) := by
          ring

theorem comp_mixCLM_inl_apply_single (a b : ℝ) (L : StrongDual ℝ (Fin n → ℝ)) (i : Fin n) :
    (((L.comp (mixCLM (n := n) a b)).comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) =
      a * L (Pi.single i (1 : ℝ)) := by
  have hfun :
      (fun j : Fin n => a * (Pi.single i (1 : ℝ) : Fin n → ℝ) j) =
        a • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    ext j
    simp [Pi.smul_apply, smul_eq_mul]
  simp [mixCLM, Pi.smul_apply, smul_eq_mul]
  rw [hfun, map_smul]
  simp [smul_eq_mul]

theorem comp_mixCLM_inr_apply_single (a b : ℝ) (L : StrongDual ℝ (Fin n → ℝ)) (i : Fin n) :
    (((L.comp (mixCLM (n := n) a b)).comp
      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) =
      b * L (Pi.single i (1 : ℝ)) := by
  have hfun :
      (fun j : Fin n => b * (Pi.single i (1 : ℝ) : Fin n → ℝ) j) =
        b • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    ext j
    simp [Pi.smul_apply, smul_eq_mul]
  simp [mixCLM, Pi.smul_apply, smul_eq_mul]
  rw [hfun, map_smul]
  simp [smul_eq_mul]

/-- Any orthogonal scalar mix `(x,y) ↦ a x + b y` preserves the standard
Gaussian product law. -/
theorem ou_kernel_map_coeff (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((γFin n).prod (γFin n)).map (mixCLM (n := n) a b) = γFin n := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_γFin, charFunDual_γFin, charFunDual_γFin]
  have hinl :
      ∑ i : Fin n,
        ((((L.comp (mixCLM (n := n) a b)).comp
          (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2) =
        a ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
    calc
      _ = ∑ i : Fin n, (a * L (Pi.single i (1 : ℝ))) ^ 2 := by
            congr with i
            rw [comp_mixCLM_inl_apply_single]
      _ = _ := by
            rw [Finset.mul_sum]
            congr with i
            ring
  have hinr :
      ∑ i : Fin n,
        ((((L.comp (mixCLM (n := n) a b)).comp
          (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2) =
        b ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
    calc
      _ = ∑ i : Fin n, (b * L (Pi.single i (1 : ℝ))) ^ 2 := by
            congr with i
            rw [comp_mixCLM_inr_apply_single]
      _ = _ := by
            rw [Finset.mul_sum]
            congr with i
            ring
  rw [hinl, hinr]
  rw [← Complex.exp_add]
  congr 1
  let S : ℝ := ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2
  have hs : a ^ 2 * S + b ^ 2 * S = S := by
    calc
      a ^ 2 * S + b ^ 2 * S = (a ^ 2 + b ^ 2) * S := by ring
      _ = S := by rw [hab, one_mul]
  have hgoal :
      -(↑(a ^ 2 * S) : ℂ) / (2 : ℂ) + -(↑(b ^ 2 * S) : ℂ) / (2 : ℂ) =
        -(↑S : ℂ) / (2 : ℂ) := by
    calc
      -(↑(a ^ 2 * S) : ℂ) / (2 : ℂ) + -(↑(b ^ 2 * S) : ℂ) / (2 : ℂ)
          = (↑(a ^ 2 * S) : ℂ) * (-((1 : ℂ) / 2)) +
              (↑(b ^ 2 * S) : ℂ) * (-((1 : ℂ) / 2)) := by ring
      _ = ((↑(a ^ 2 * S) : ℂ) + (↑(b ^ 2 * S) : ℂ)) * (-((1 : ℂ) / 2)) := by ring
      _ = (↑(a ^ 2 * S + b ^ 2 * S) : ℂ) * (-((1 : ℂ) / 2)) := by norm_num
      _ = (↑S : ℂ) * (-((1 : ℂ) / 2)) := by rw [hs]
      _ = -(↑S : ℂ) / (2 : ℂ) := by ring
  simpa [S] using hgoal

theorem ou_kernel_map_fin (t : ℝ) (ht : 0 ≤ t) :
    ((γFin n).prod (γFin n)).map
      (mixCLM (n := n) (exp (-t)) (sqrt (1 - exp (-2 * t)))) = γFin n := by
  apply ou_kernel_map_coeff
  have hnonneg : 0 ≤ 1 - exp (-2 * t) := Gaussian1D.one_sub_exp_nonneg t ht
  rw [sq_sqrt hnonneg, sq, ← exp_add]
  ring

/-- Orthogonal Gaussian rotation on `(Fin n → ℝ) × (Fin n → ℝ)`. -/
def rotCLM (a b : ℝ) :
    ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (mixCLM (n := n) a b).prod (mixCLM (n := n) b (-a))

theorem comp_rotCLM_inl_apply_single (a b : ℝ)
    (L : StrongDual ℝ ((Fin n → ℝ) × (Fin n → ℝ))) (i : Fin n) :
    (((L.comp (rotCLM (n := n) a b)).comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) =
      a * ((L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)))
        (Pi.single i (1 : ℝ))) +
      b * ((L.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)))
        (Pi.single i (1 : ℝ))) := by
  have hpair :
      rotCLM (n := n) a b ((Pi.single i (1 : ℝ)), (0 : Fin n → ℝ)) =
        a • ((Pi.single i (1 : ℝ) : Fin n → ℝ), 0) +
          b • (0, (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
    apply Prod.ext
    · ext j
      simp [rotCLM, mixCLM_apply, Pi.smul_apply, smul_eq_mul]
    · ext j
      simp [rotCLM, mixCLM_apply, Pi.smul_apply, smul_eq_mul]
  simp [ContinuousLinearMap.comp_apply]
  rw [hpair, map_add, map_smul, map_smul]
  simp [smul_eq_mul]

theorem comp_rotCLM_inr_apply_single (a b : ℝ)
    (L : StrongDual ℝ ((Fin n → ℝ) × (Fin n → ℝ))) (i : Fin n) :
    (((L.comp (rotCLM (n := n) a b)).comp
      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) =
      b * ((L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)))
        (Pi.single i (1 : ℝ))) -
      a * ((L.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)))
        (Pi.single i (1 : ℝ))) := by
  have hpair :
      rotCLM (n := n) a b ((0 : Fin n → ℝ), Pi.single i (1 : ℝ)) =
        b • ((Pi.single i (1 : ℝ) : Fin n → ℝ), 0) +
          (-a) • (0, (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
    apply Prod.ext
    · ext j
      simp [rotCLM, mixCLM_apply, Pi.smul_apply, smul_eq_mul]
    · ext j
      simp [rotCLM, mixCLM_apply, Pi.smul_apply, smul_eq_mul]
  simp [ContinuousLinearMap.comp_apply]
  rw [hpair, map_add, map_smul, map_smul]
  simp [smul_eq_mul]
  rw [sub_eq_add_neg]

/-- Orthogonal rotations preserve the Gaussian product law on
`(Fin n → ℝ) × (Fin n → ℝ)`. -/
theorem rotCLM_map_coeff (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((γFin n).prod (γFin n)).map (rotCLM (n := n) a b) =
      (γFin n).prod (γFin n) := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_γFin, charFunDual_γFin,
    charFunDual_prod, charFunDual_γFin, charFunDual_γFin]
  let A : Fin n → ℝ := fun i =>
    ((L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)))
      (Pi.single i (1 : ℝ)))
  let B : Fin n → ℝ := fun i =>
    ((L.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)))
      (Pi.single i (1 : ℝ)))
  let S₁ : ℝ := ∑ i : Fin n,
    ((((L.comp (rotCLM (n := n) a b)).comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)))
      (Pi.single i (1 : ℝ))) ^ 2)
  let S₂ : ℝ := ∑ i : Fin n,
    ((((L.comp (rotCLM (n := n) a b)).comp
      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)))
      (Pi.single i (1 : ℝ))) ^ 2)
  let T₁ : ℝ := ∑ i : Fin n, (A i) ^ 2
  let T₂ : ℝ := ∑ i : Fin n, (B i) ^ 2
  have hsum : S₁ + S₂ = T₁ + T₂ := by
    calc
      S₁ + S₂ = ∑ i : Fin n, ((a * A i + b * B i) ^ 2 + (b * A i - a * B i) ^ 2) := by
        rw [show S₁ = ∑ i : Fin n, (a * A i + b * B i) ^ 2 by
          unfold S₁ A
          congr with i
          rw [comp_rotCLM_inl_apply_single]
            ,
          show S₂ = ∑ i : Fin n, (b * A i - a * B i) ^ 2 by
          unfold S₂ A B
          congr with i
          rw [comp_rotCLM_inr_apply_single]]
        rw [← Finset.sum_add_distrib]
      _ = ∑ i : Fin n, (A i ^ 2 + B i ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        calc
          (a * A i + b * B i) ^ 2 + (b * A i - a * B i) ^ 2
            = (a ^ 2 + b ^ 2) * (A i ^ 2 + B i ^ 2) := by ring
          _ = A i ^ 2 + B i ^ 2 := by rw [hab, one_mul]
      _ = T₁ + T₂ := by
        unfold T₁ T₂
        rw [Finset.sum_add_distrib]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  calc
    -(↑S₁ : ℂ) / (2 : ℂ) + -(↑S₂ : ℂ) / (2 : ℂ)
        = (↑(S₁ + S₂) : ℂ) * (-((1 : ℂ) / 2)) := by
            norm_num
            ring
    _ = (↑(T₁ + T₂) : ℂ) * (-((1 : ℂ) / 2)) := by rw [hsum]
    _ = -(↑T₁ : ℂ) / (2 : ℂ) + -(↑T₂ : ℂ) / (2 : ℂ) := by
          norm_num
          ring

theorem mixCLM_rotCLM (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    mixCLM (n := n) a b (rotCLM (n := n) a b p) = p.1 := by
  ext i
  simp [rotCLM, mixCLM_apply]
  calc
    a * (a * p.1 i + b * p.2 i) + b * (b * p.1 i + -(a * p.2 i))
          = (a ^ 2 + b ^ 2) * p.1 i := by ring
    _ = p.1 i := by rw [hab, one_mul]

/-- Scalar multiplication on `Fin n → ℝ` as a continuous linear map. -/
def smulFinCLM (c : ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  c • ContinuousLinearMap.id ℝ (Fin n → ℝ)

theorem comp_smulFinCLM_apply_single (c : ℝ)
    (L : StrongDual ℝ (Fin n → ℝ)) (i : Fin n) :
    ((L.comp (smulFinCLM (n := n) c)) (Pi.single i (1 : ℝ))) =
      c * L (Pi.single i (1 : ℝ)) := by
  simp [smulFinCLM, smul_eq_mul]

/-- Mixed Gaussian coordinates with variance `a² + b² = c²` equal the scalar
pushforward of the standard Gaussian by `c`. -/
theorem ou_kernel_map_coeff_scaled (a b c : ℝ)
    (hvar : a ^ 2 + b ^ 2 = c ^ 2) (_hc : 0 ≤ c) :
    ((γFin n).prod (γFin n)).map (mixCLM (n := n) a b) =
      (γFin n).map (smulFinCLM (n := n) c) := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_γFin, charFunDual_γFin,
    charFunDual_map, charFunDual_γFin]
  have hmix :
      ∑ i : Fin n,
        ((((L.comp (mixCLM (n := n) a b)).comp
          (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2) +
      ∑ i : Fin n,
        ((((L.comp (mixCLM (n := n) a b)).comp
          (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2) =
      c ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
    calc
      _ = a ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 +
            b ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
              rw [show ∑ i : Fin n,
                    ((((L.comp (mixCLM (n := n) a b)).comp
                      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)))
                      (Pi.single i (1 : ℝ))) ^ 2) =
                    a ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 by
                    calc
                      _ = ∑ i : Fin n, (a * L (Pi.single i (1 : ℝ))) ^ 2 := by
                            congr with i
                            rw [comp_mixCLM_inl_apply_single]
                      _ = _ := by
                            rw [Finset.mul_sum]
                            congr with i
                            ring,
                  show ∑ i : Fin n,
                    ((((L.comp (mixCLM (n := n) a b)).comp
                      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)))
                      (Pi.single i (1 : ℝ))) ^ 2) =
                    b ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 by
                    calc
                      _ = ∑ i : Fin n, (b * L (Pi.single i (1 : ℝ))) ^ 2 := by
                            congr with i
                            rw [comp_mixCLM_inr_apply_single]
                      _ = _ := by
                            rw [Finset.mul_sum]
                            congr with i
                            ring]
      _ = c ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
            rw [← hvar]
            ring
  have hsmul :
      ∑ i : Fin n, (((L.comp (smulFinCLM (n := n) c)) (Pi.single i (1 : ℝ))) ^ 2) =
        c ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
    calc
      _ = ∑ i : Fin n, (c * L (Pi.single i (1 : ℝ))) ^ 2 := by
            congr with i
            rw [comp_smulFinCLM_apply_single]
      _ = _ := by
            rw [Finset.mul_sum]
            congr with i
            ring
  let S₁ : ℝ := ∑ i : Fin n,
    ((((L.comp (mixCLM (n := n) a b)).comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2)
  let S₂ : ℝ := ∑ i : Fin n,
    ((((L.comp (mixCLM (n := n) a b)).comp
      (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2)
  let T : ℝ := ∑ i : Fin n, (((L.comp (smulFinCLM (n := n) c)) (Pi.single i (1 : ℝ))) ^ 2)
  have hS : S₁ + S₂ = c ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
    simpa [S₁, S₂] using hmix
  have hT : T = c ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2 := by
    simpa [T] using hsmul
  rw [← Complex.exp_add]
  rw [show ∑ i : Fin n,
      ((((L.comp (mixCLM (n := n) a b)).comp
        (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2) = S₁ by
      rfl]
  rw [show ∑ i : Fin n,
      ((((L.comp (mixCLM (n := n) a b)).comp
        (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) (Pi.single i (1 : ℝ))) ^ 2) = S₂ by
      rfl]
  rw [show ∑ i : Fin n, (((L.comp (smulFinCLM (n := n) c)) (Pi.single i (1 : ℝ))) ^ 2) = T by
      rfl]
  congr 1
  calc
    -(↑S₁ : ℂ) / (2 : ℂ) + -(↑S₂ : ℂ) / (2 : ℂ)
        = -(↑(S₁ + S₂) : ℂ) / (2 : ℂ) := by
            norm_num
            ring
    _ = -(↑(c ^ 2 * ∑ i : Fin n, (L (Pi.single i (1 : ℝ))) ^ 2) : ℂ) / (2 : ℂ) := by
          rw [hS]
    _ = -(↑T : ℂ) / (2 : ℂ) := by rw [hT]

theorem ouSemigroupFin_mean (f : (Fin n → ℝ) → ℝ) (t : ℝ) (ht : 0 ≤ t) (hf : IsCoreFin f) :
    ∫ x, ouSemigroupFin t f x ∂γFin n = ∫ x, f x ∂γFin n := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  have hmap : ((γFin n).prod (γFin n)).map (mixCLM (n := n) a b) = γFin n := by
    simpa [a, b] using ou_kernel_map_fin (n := n) t ht
  have hf_map_sm : AEStronglyMeasurable f (((γFin n).prod (γFin n)).map (mixCLM (n := n) a b)) := by
    simpa [hmap] using hf.stronglyMeasurable.aestronglyMeasurable
  have hf_map_int : Integrable f (((γFin n).prod (γFin n)).map (mixCLM (n := n) a b)) := by
    simpa [hmap] using hf.integrable
  have hcomp :
      ∫ p, f (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) = ∫ x, f x ∂γFin n := by
    simpa [hmap] using
      (integral_map (f := f) (Measurable.aemeasurable (by fun_prop)) hf_map_sm).symm
  have hmix_int : Integrable (f ∘ mixCLM (n := n) a b) ((γFin n).prod (γFin n)) :=
    (integrable_map_measure hf_map_sm (Measurable.aemeasurable (by fun_prop))).mp
      hf_map_int
  have hprod :
      ∫ x, ∫ y, f (mixCLM (n := n) a b (x, y)) ∂γFin n ∂γFin n =
        ∫ p, f (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) := by
    simpa using (integral_prod (f := f ∘ mixCLM (n := n) a b) hmix_int).symm
  have hiter :
      (∫ x, ouSemigroupFin t f x ∂γFin n) =
        ∫ x, ∫ y, f (mixCLM (n := n) a b (x, y)) ∂γFin n ∂γFin n := by
    unfold ouSemigroupFin
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    congr 1
  rw [hiter, hprod]
  exact hcomp

theorem ouSemigroupFin_contraction (f : (Fin n → ℝ) → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : IsCoreFin f) :
    ∫ x, (ouSemigroupFin t f x) ^ 2 ∂γFin n ≤ ∫ x, (f x) ^ 2 ∂γFin n := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  have hmap : ((γFin n).prod (γFin n)).map (mixCLM (n := n) a b) = γFin n := by
    simpa [a, b] using ou_kernel_map_fin (n := n) t ht
  obtain ⟨M, hM⟩ := hf.bound_exists
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hf_meas : Measurable f := hf.measurable
  have hf2_int : Integrable (fun x => (f x) ^ 2) (γFin n) := hf.integrable_sq
  have hf2_map_sm : AEStronglyMeasurable (fun x => (f x) ^ 2)
      (((γFin n).prod (γFin n)).map (mixCLM (n := n) a b)) := by
    simpa [hmap] using ((hf.measurable.pow_const 2).aemeasurable.aestronglyMeasurable)
  have hf2_map_int : Integrable (fun x => (f x) ^ 2)
      (((γFin n).prod (γFin n)).map (mixCLM (n := n) a b)) := by
    simpa [hmap] using hf2_int
  have hf2_mix_int : Integrable (fun p => (f (mixCLM (n := n) a b p)) ^ 2)
      ((γFin n).prod (γFin n)) :=
    (integrable_map_measure hf2_map_sm (Measurable.aemeasurable (by fun_prop))).mp hf2_map_int
  have hf_mix_int : ∀ x, Integrable (fun y => f (mixCLM (n := n) a b (x, y))) (γFin n) := by
    intro x
    have hsec_meas : Measurable (fun y : Fin n → ℝ => mixCLM (n := n) a b (x, y)) := by
      fun_prop
    refine Integrable.mono' (integrable_const M)
      ((hf_meas.comp hsec_meas).aemeasurable.aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall (fun y => hM (mixCLM (n := n) a b (x, y)))
  have h_convex : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
    Even.convexOn_pow (Nat.even_iff.mpr rfl)
  have h_cont : ContinuousOn (fun x : ℝ => x ^ 2) Set.univ := (continuous_pow 2).continuousOn
  have h_closed : IsClosed (Set.univ : Set ℝ) := isClosed_univ
  have hJensen :
      ∀ x, (∫ y, f (mixCLM (n := n) a b (x, y)) ∂γFin n) ^ 2 ≤
        ∫ y, (f (mixCLM (n := n) a b (x, y))) ^ 2 ∂γFin n := by
    intro x
    have hmem : ∀ᵐ y ∂γFin n, f (mixCLM (n := n) a b (x, y)) ∈ (Set.univ : Set ℝ) :=
      Filter.Eventually.of_forall (fun y => Set.mem_univ _)
    have hf_mix2_int : Integrable (fun y => (f (mixCLM (n := n) a b (x, y))) ^ 2) (γFin n) := by
      have hsec_meas : Measurable (fun y : Fin n → ℝ => mixCLM (n := n) a b (x, y)) := by
        fun_prop
      refine Integrable.mono' (integrable_const (M ^ 2))
        (((hf_meas.comp hsec_meas).pow_const 2).aemeasurable.aestronglyMeasurable) ?_
      refine Filter.Eventually.of_forall ?_
      intro y
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hy : |f (mixCLM (n := n) a b (x, y))| ≤ M := by
        rw [← Real.norm_eq_abs]
        exact hM (mixCLM (n := n) a b (x, y))
      have hy2 : (f (mixCLM (n := n) a b (x, y))) ^ 2 ≤ M ^ 2 := by
        have : |f (mixCLM (n := n) a b (x, y))| ^ 2 ≤ M ^ 2 := by
          nlinarith [abs_nonneg (f (mixCLM (n := n) a b (x, y)))]
        rwa [sq_abs] at this
      have hnorm : ‖M ^ 2‖ = M ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      linarith
    exact ConvexOn.map_integral_le h_convex h_cont h_closed hmem (hf_mix_int x) hf_mix2_int
  have hiter :
      (∫ x, (ouSemigroupFin t f x) ^ 2 ∂γFin n) =
        ∫ x, (∫ y, f (mixCLM (n := n) a b (x, y)) ∂γFin n) ^ 2 ∂γFin n := by
    unfold ouSemigroupFin
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    congr 1
  calc
    ∫ x, (ouSemigroupFin t f x) ^ 2 ∂γFin n
      = ∫ x, (∫ y, f (mixCLM (n := n) a b (x, y)) ∂γFin n) ^ 2 ∂γFin n := hiter
    _ ≤ ∫ x, ∫ y, (f (mixCLM (n := n) a b (x, y))) ^ 2 ∂γFin n ∂γFin n := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
          · exact hf2_mix_int.integral_prod_left
          · exact Filter.Eventually.of_forall hJensen
    _ = ∫ p, (f (mixCLM (n := n) a b p)) ^ 2 ∂((γFin n).prod (γFin n)) := by
          simpa using (integral_prod (f := fun p => (f (mixCLM (n := n) a b p)) ^ 2) hf2_mix_int).symm
    _ = ∫ x, (f x) ^ 2 ∂γFin n := by
          simpa [hmap] using
            (integral_map (f := fun x => (f x) ^ 2) (Measurable.aemeasurable (by fun_prop))
              hf2_map_sm).symm

theorem ouSemigroupFin_selfAdjoint (f g : (Fin n → ℝ) → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : IsCoreFin f) (hg : IsCoreFin g) :
    ∫ x, ouSemigroupFin t f x * g x ∂γFin n =
      ∫ x, f x * ouSemigroupFin t g x ∂γFin n := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  have hab : a ^ 2 + b ^ 2 = 1 := by
    have hnonneg : 0 ≤ 1 - exp (-2 * t) := Gaussian1D.one_sub_exp_nonneg t ht
    rw [show a = exp (-t) by rfl, show b = sqrt (1 - exp (-2 * t)) by rfl]
    rw [sq_sqrt hnonneg, sq, ← exp_add]
    ring
  have hmap : ((γFin n).prod (γFin n)).map (rotCLM (n := n) a b) =
      (γFin n).prod (γFin n) := rotCLM_map_coeff (n := n) a b hab
  obtain ⟨Mf, hMf⟩ := hf.bound_exists
  obtain ⟨Mg, hMg⟩ := hg.bound_exists
  have hMf_nn : 0 ≤ Mf := (norm_nonneg _).trans (hMf 0)
  have hMg_nn : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0)
  have hF_sm : AEStronglyMeasurable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (mixCLM (n := n) a b p) * g p.1)
      ((γFin n).prod (γFin n)) := by
    exact
      (((hf.measurable.comp (mixCLM (n := n) a b).continuous.measurable)).mul
        (hg.measurable.comp measurable_fst)).aemeasurable.aestronglyMeasurable
  have hG_sm : AEStronglyMeasurable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.1 * g (mixCLM (n := n) a b p))
      ((γFin n).prod (γFin n)) := by
    have h_meas : Measurable
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.1 * g (mixCLM (n := n) a b p)) :=
      (hf.measurable.comp measurable_fst).mul
        (hg.measurable.comp (mixCLM (n := n) a b).continuous.measurable)
    exact h_meas.aemeasurable.aestronglyMeasurable
  have hF_int : Integrable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (mixCLM (n := n) a b p) * g p.1)
      ((γFin n).prod (γFin n)) := by
    refine Integrable.mono' (integrable_const (Mf * Mg)) hF_sm ?_
    refine Filter.Eventually.of_forall ?_
    intro p
    rw [norm_mul]
    exact mul_le_mul (hMf _) (hMg _) (norm_nonneg _) hMf_nn
  have hG_int : Integrable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.1 * g (mixCLM (n := n) a b p))
      ((γFin n).prod (γFin n)) := by
    refine Integrable.mono' (integrable_const (Mf * Mg)) hG_sm ?_
    refine Filter.Eventually.of_forall ?_
    intro p
    rw [norm_mul]
    exact mul_le_mul (hMf _) (hMg _) (norm_nonneg _) hMf_nn
  have hlaw :
      HasLaw (rotCLM (n := n) a b) ((γFin n).prod (γFin n)) ((γFin n).prod (γFin n)) :=
    ⟨(Measurable.aemeasurable (by fun_prop)), hmap⟩
  have hswap :
      ∫ p, f (mixCLM (n := n) a b p) * g p.1 ∂((γFin n).prod (γFin n)) =
        ∫ p, f p.1 * g (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) := by
    calc
      ∫ p, f (mixCLM (n := n) a b p) * g p.1 ∂((γFin n).prod (γFin n))
          = ∫ p,
              (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
                f q.1 * g (mixCLM (n := n) a b q)) (rotCLM (n := n) a b p)
              ∂((γFin n).prod (γFin n)) := by
                refine integral_congr_ae ?_
                refine Filter.Eventually.of_forall ?_
                intro p
                change f (mixCLM (n := n) a b p) * g p.1 =
                  f ((rotCLM (n := n) a b p).1) *
                    g (mixCLM (n := n) a b (rotCLM (n := n) a b p))
                rw [mixCLM_rotCLM (n := n) a b hab p]
                simp [rotCLM]
      _ = ∫ p, f p.1 * g (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) := by
            exact hlaw.integral_comp hG_sm
  have hleft_prod :
      ∫ x, ouSemigroupFin t f x * g x ∂γFin n =
        ∫ p, f (mixCLM (n := n) a b p) * g p.1 ∂((γFin n).prod (γFin n)) := by
    have hiter :
        ∫ x, ouSemigroupFin t f x * g x ∂γFin n =
          ∫ x, ∫ y, f (mixCLM (n := n) a b (x, y)) * g x ∂γFin n ∂γFin n := by
      unfold ouSemigroupFin
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      have hxy :
          (fun y : Fin n → ℝ => f (ouShiftFin t x y)) =
            fun y : Fin n → ℝ => f (mixCLM (n := n) a b (x, y)) := by
        funext y
        have harg : ouShiftFin t x y = mixCLM (n := n) a b (x, y) := by
          ext i
          simp [ouShiftFin, mixCLM_apply, a, b]
        exact congrArg f harg
      calc
        (∫ y, f (ouShiftFin t x y) ∂γFin n) * g x
            = (∫ y, f (mixCLM (n := n) a b (x, y)) ∂γFin n) * g x := by
                simp [hxy]
        _ = ∫ y, f (mixCLM (n := n) a b (x, y)) * g x ∂γFin n := by
              symm
              simpa [mul_comm] using
                (integral_const_mul (r := g x)
                  (f := fun y : Fin n → ℝ => f (mixCLM (n := n) a b (x, y))))
    rw [hiter]
    simpa using
      (integral_prod
        (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          f (mixCLM (n := n) a b p) * g p.1) hF_int).symm
  have hright_prod :
      ∫ x, f x * ouSemigroupFin t g x ∂γFin n =
        ∫ p, f p.1 * g (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) := by
    have hiter :
        ∫ x, f x * ouSemigroupFin t g x ∂γFin n =
          ∫ x, ∫ y, f x * g (mixCLM (n := n) a b (x, y)) ∂γFin n ∂γFin n := by
      unfold ouSemigroupFin
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      have hxy :
          (fun y : Fin n → ℝ => g (ouShiftFin t x y)) =
            fun y : Fin n → ℝ => g (mixCLM (n := n) a b (x, y)) := by
        funext y
        have harg : ouShiftFin t x y = mixCLM (n := n) a b (x, y) := by
          ext i
          simp [ouShiftFin, mixCLM_apply, a, b]
        exact congrArg g harg
      calc
        f x * ∫ y, g (ouShiftFin t x y) ∂γFin n
            = f x * ∫ y, g (mixCLM (n := n) a b (x, y)) ∂γFin n := by
                simp [hxy]
        _ = ∫ y, f x * g (mixCLM (n := n) a b (x, y)) ∂γFin n := by
              symm
              simpa using
                (integral_const_mul (r := f x)
                  (f := fun y : Fin n → ℝ => g (mixCLM (n := n) a b (x, y))))
    rw [hiter]
    simpa using
      (integral_prod
        (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
          f p.1 * g (mixCLM (n := n) a b p)) hG_int).symm
  rw [hleft_prod, hright_prod]
  exact hswap

theorem ouSemigroupFin_compose (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ouSemigroupFin (s + t) f = ouSemigroupFin s (ouSemigroupFin t f) := by
  ext x
  obtain ⟨M, hM⟩ := hf.bound_exists
  have hf_meas : Measurable f := hf.measurable
  set ast := exp (-(s + t))
  set bst := sqrt (1 - exp (-2 * (s + t)))
  set as := exp (-s)
  set bs := sqrt (1 - exp (-2 * s))
  set at_ := exp (-t)
  set bt := sqrt (1 - exp (-2 * t))
  have hbst_nn : 0 ≤ 1 - exp (-2 * (s + t)) :=
    Gaussian1D.one_sub_exp_nonneg (s + t) (by linarith)
  have hbs_nn : 0 ≤ 1 - exp (-2 * s) := Gaussian1D.one_sub_exp_nonneg s hs
  have hbt_nn : 0 ≤ 1 - exp (-2 * t) := Gaussian1D.one_sub_exp_nonneg t ht
  have h_ast : ast = as * at_ := by
    show exp (-(s + t)) = exp (-s) * exp (-t)
    rw [show -(s + t) = -s + -t by ring, exp_add]
  set Ψ : ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ) :=
    mixCLM (n := n) (at_ * bs) bt
  have h_var_eq : (at_ * bs) ^ 2 + bt ^ 2 = bst ^ 2 := by
    show (exp (-t) * sqrt (1 - exp (-2 * s))) ^ 2 + sqrt (1 - exp (-2 * t)) ^ 2 =
        sqrt (1 - exp (-2 * (s + t))) ^ 2
    rw [mul_pow, sq_sqrt hbs_nn, sq_sqrt hbt_nn, sq_sqrt hbst_nn]
    rw [show exp (-t) ^ 2 = exp (-2 * t) by
      rw [show (-2 * t : ℝ) = -t + -t by ring, exp_add]
      ring]
    have h2 : exp (-2 * t) * exp (-2 * s) = exp (-2 * (s + t)) := by
      rw [← exp_add]
      congr 1
      ring
    linarith [h2]
  have hΨ_law :
      ((γFin n).prod (γFin n)).map Ψ = (γFin n).map (smulFinCLM (n := n) bst) := by
    simpa [Ψ] using
      (ou_kernel_map_coeff_scaled (n := n) (a := at_ * bs) (b := bt) (c := bst)
        h_var_eq (sqrt_nonneg _))
  have hΨ_int : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (ast • x + Ψ p))
      ((γFin n).prod (γFin n)) := by
    refine Integrable.mono' (integrable_const M) ?_ ?_
    · exact (hf_meas.comp ((measurable_const.add Ψ.continuous.measurable))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => hM _)
  have hRHS :
      ouSemigroupFin s (ouSemigroupFin t f) x =
        ∫ p, f (ast • x + Ψ p) ∂((γFin n).prod (γFin n)) := by
    unfold ouSemigroupFin
    have h_eq_pt : ∀ y' y : Fin n → ℝ,
        ouShiftFin t (ouShiftFin s x y') y = ast • x + Ψ (y', y) := by
      intro y' y
      ext i
      rw [h_ast]
      simp [ouShiftFin, Ψ, mixCLM_apply, Pi.smul_apply, smul_eq_mul, as, bs, at_, bt]
      ring
    simp_rw [h_eq_pt]
    simpa using
      (integral_prod (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (ast • x + Ψ p)) hΨ_int).symm
  have hcompose :
      ∫ p, f (ast • x + Ψ p) ∂((γFin n).prod (γFin n)) =
        ∫ z, f (ast • x + bst • z) ∂γFin n := by
    have h_lhs_via_law :
        ∫ p, f (ast • x + Ψ p) ∂((γFin n).prod (γFin n)) =
          ∫ w, f (ast • x + w) ∂(((γFin n).prod (γFin n)).map Ψ) := by
      have hsm : AEStronglyMeasurable (fun w : Fin n → ℝ => f (ast • x + w))
          (((γFin n).prod (γFin n)).map Ψ) := by
        exact (hf_meas.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      rw [integral_map Ψ.continuous.measurable.aemeasurable hsm]
    have h_rhs_via_law :
        ∫ z, f (ast • x + bst • z) ∂γFin n =
          ∫ w, f (ast • x + w) ∂((γFin n).map (smulFinCLM (n := n) bst)) := by
      have hsm : AEStronglyMeasurable (fun w : Fin n → ℝ => f (ast • x + w))
          ((γFin n).map (smulFinCLM (n := n) bst)) := by
        exact (hf_meas.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      have htmp :
          ∫ w, f (ast • x + w) ∂((γFin n).map (smulFinCLM (n := n) bst)) =
            ∫ z, f (ast • x + smulFinCLM (n := n) bst z) ∂γFin n := by
        rw [integral_map (smulFinCLM (n := n) bst).continuous.measurable.aemeasurable hsm]
      calc
        ∫ z, f (ast • x + bst • z) ∂γFin n
            = ∫ z, f (ast • x + smulFinCLM (n := n) bst z) ∂γFin n := by
                simp [smulFinCLM]
        _ = ∫ w, f (ast • x + w) ∂((γFin n).map (smulFinCLM (n := n) bst)) := htmp.symm
    rw [h_lhs_via_law, h_rhs_via_law, hΨ_law]
  show ouSemigroupFin (s + t) f x = ouSemigroupFin s (ouSemigroupFin t f) x
  rw [hRHS, hcompose]
  unfold ouSemigroupFin
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have harg : ouShiftFin (s + t) x y = ast • x + bst • y := by
    ext i
    simp [ouShiftFin, Pi.smul_apply, smul_eq_mul, ast, bst]
  exact congrArg f harg

theorem ouSemigroupFin_zero (f : (Fin n → ℝ) → ℝ) :
    ouSemigroupFin 0 f = f := by
  ext x
  have hconst : (fun y : Fin n → ℝ => f (ouShiftFin 0 x y)) = fun _ : Fin n → ℝ => f x := by
    funext y
    congr 1
    ext i
    simp [ouShiftFin]
  rw [ouSemigroupFin, hconst, integral_const]
  simp

end GaussianFin
