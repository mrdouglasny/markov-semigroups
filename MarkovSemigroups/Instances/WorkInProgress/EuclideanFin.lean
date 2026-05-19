/- 
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multivariate Gaussian Bakry-Emery Instance

Concrete finite-dimensional Gaussian data for the Stage N1 multivariate
Bakry-Emery construction.
-/

import MarkovSemigroups.Instances.WorkInProgress.Euclidean
import MarkovSemigroups.Instances.WorkInProgress.EuclideanEntropyDecay
import MarkovSemigroups.Instances.WorkInProgress.EuclideanStein
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory Filter Set Real ProbabilityTheory

noncomputable section

namespace GaussianFin

open scoped BigOperators ContDiff

variable {n : ℕ}

/-- The standard Gaussian product measure on `Fin n → ℝ`. -/
def γFin (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => Gaussian1D.γ)

instance instIsProbabilityMeasureγFin (n : ℕ) : IsProbabilityMeasure (γFin n) := by
  unfold γFin
  infer_instance

theorem measurePreserving_piFinSuccAbove_γFin {n : ℕ} (i : Fin (n + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i)
      (γFin (n + 1)) (Gaussian1D.γ.prod (γFin n)) := by
  simpa [γFin] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => Gaussian1D.γ) i)

theorem integral_γFin_succAbove {n : ℕ} (i : Fin (n + 1))
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Integrable f (γFin (n + 1))) :
    ∫ x, f x ∂γFin (n + 1) =
      ∫ s, ∫ y, f (i.insertNth s y) ∂γFin n ∂Gaussian1D.γ := by
  let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have he : MeasurePreserving e (γFin (n + 1)) (Gaussian1D.γ.prod (γFin n)) :=
    measurePreserving_piFinSuccAbove_γFin (n := n) i
  have hcomp : Integrable (f ∘ e.symm) (Gaussian1D.γ.prod (γFin n)) := by
    exact
      (he.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding e.symm)).2 hf
  calc
    ∫ x, f x ∂γFin (n + 1)
      = ∫ p : ℝ × (Fin n → ℝ), f (e.symm p) ∂(Gaussian1D.γ.prod (γFin n)) := by
          simpa using
            (he.integral_comp' (g := fun p : ℝ × (Fin n → ℝ) => f (e.symm p)))
    _ = ∫ s, ∫ y, f (i.insertNth s y) ∂γFin n ∂Gaussian1D.γ := by
          simpa [e] using
            (integral_prod (f := fun p : ℝ × (Fin n → ℝ) => f (e.symm p)) hcomp)

/-- The affine Mehler shift on `(Fin n → ℝ)`. -/
def ouShiftFin (t : ℝ) (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => exp (-t) * x i + sqrt (1 - exp (-2 * t)) * y i

theorem ouShiftFin_insertNth {n : ℕ} (i : Fin (n + 1)) (t s u : ℝ)
    (x y : Fin n → ℝ) :
    ouShiftFin t (i.insertNth s x) (i.insertNth u y) =
      i.insertNth (exp (-t) * s + sqrt (1 - exp (-2 * t)) * u) (ouShiftFin t x y) := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp [ouShiftFin]
  · rcases Fin.exists_succAbove_eq hji with ⟨k, rfl⟩
    simp [ouShiftFin]

/-- The multivariate Ornstein-Uhlenbeck semigroup via the Mehler formula. -/
def ouSemigroupFin (t : ℝ) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => ∫ y, f (ouShiftFin t x y) ∂γFin n

theorem ouSemigroupFin_insertNth_eq {n : ℕ} (t : ℝ) {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf_meas : Measurable f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    (i : Fin (n + 1)) (s : ℝ) (x : Fin n → ℝ) :
    ouSemigroupFin t f (i.insertNth s x) =
      ∫ u, ∫ y, f (i.insertNth (exp (-t) * s + sqrt (1 - exp (-2 * t)) * u) (ouShiftFin t x y))
        ∂γFin n ∂Gaussian1D.γ := by
  let g : (Fin (n + 1) → ℝ) → ℝ := fun z => f (ouShiftFin t (i.insertNth s x) z)
  have hcont_shift : Continuous (fun z : Fin (n + 1) → ℝ => ouShiftFin t (i.insertNth s x) z) := by
    continuity
  have hg_meas : Measurable g := hf_meas.comp hcont_shift.measurable
  have hg_int : Integrable g (γFin (n + 1)) := by
    refine Integrable.mono' (integrable_const M) hg_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun z => hM (ouShiftFin t (i.insertNth s x) z))
  unfold ouSemigroupFin
  simpa [g, ouShiftFin_insertNth] using
    (integral_γFin_succAbove (n := n) (i := i) (f := g) hg_int)

def sectionInputFin (t : ℝ) {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (i : Fin (n + 1)) (x : Fin n → ℝ) : ℝ → ℝ :=
  fun r => ∫ y, f (i.insertNth r (ouShiftFin t x y)) ∂γFin n

theorem ouSemigroupFin_section_eq_ouSemigroup
    {n : ℕ} (t : ℝ) {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf_meas : Measurable f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    (i : Fin (n + 1)) (x : Fin n → ℝ) :
    (fun s => ouSemigroupFin t f (i.insertNth s x)) =
      Gaussian1D.ouSemigroup t (sectionInputFin t f i x) := by
  funext s
  rw [ouSemigroupFin_insertNth_eq (n := n) (t := t) (hf_meas := hf_meas) (hM := hM) i s x]
  simp [Gaussian1D.ouSemigroup, sectionInputFin]

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
  ContDiff ℝ ∞ f ∧ ∃ M : ℝ,
    ∀ x, ‖f x‖ ≤ M ∧
      (∀ i : Fin n, ‖partialDeriv i f x‖ ≤ M) ∧
      ∀ i : Fin n, ‖secondPartial i f x‖ ≤ M

theorem IsCoreFin.contDiff {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ContDiff ℝ ∞ f := hf.1

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
    ContDiff ℝ ∞ (partialDeriv i f) := by
  unfold partialDeriv
  simpa using (hf.contDiff.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

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

theorem IsCoreFin.secondPartial_contDiff {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) :
    ContDiff ℝ ∞ (secondPartial i f) := by
  unfold secondPartial partialDeriv
  simpa using
    ((hf.partial_contDiff i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem IsCoreFin.secondPartial_continuous {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) : Continuous (secondPartial i f) :=
  (hf.secondPartial_contDiff i).continuous

theorem IsCoreFin.secondPartial_measurable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) : Measurable (secondPartial i f) :=
  (hf.secondPartial_continuous i).measurable

theorem IsCoreFin.secondPartial_stronglyMeasurable {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) : StronglyMeasurable (secondPartial i f) :=
  (hf.secondPartial_continuous i).stronglyMeasurable

/-- Restrict a multivariate function to the `i`-th coordinate line through `x`. -/
def coordSection (i : Fin n) (x : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) : ℝ → ℝ :=
  fun s => f (Function.update x i s)

theorem section_contDiff {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (i : Fin n) (x : Fin n → ℝ) :
    ContDiff ℝ ∞ (coordSection i x f) := by
  unfold coordSection
  exact hf.comp (contDiff_update ∞ x i)

theorem section_hasDerivAt {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (i : Fin n) (x : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (coordSection i x f)
      (partialDeriv i f (Function.update x i s)) s := by
  unfold coordSection partialDeriv
  have h_update := hasDerivAt_update x i s
  have h_f : HasFDerivAt f (fderiv ℝ f (Function.update x i s)) (Function.update x i s) :=
    ((hf.differentiable (by simp)).differentiableAt).hasFDerivAt
  simpa [partialDeriv] using h_f.comp_hasDerivAt s h_update

theorem section_deriv {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
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

theorem stein_partialDeriv_ouShiftFin {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : IsCoreFin f) (t : ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    ∫ y, y i * partialDeriv i f (ouShiftFin t x y) ∂γFin (n + 1) =
      sqrt (1 - exp (-2 * t)) * ouSemigroupFin t (secondPartial i f) x := by
  have hf_core : IsCoreFin f := hf
  obtain ⟨_, M, hM⟩ := hf
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
  let a : ℝ := exp (-t)
  let b : ℝ := sqrt (1 - exp (-2 * t))
  let x' : Fin n → ℝ := i.removeNth x
  let φ : ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun p =>
    Fin.insertNth (α := fun _ : Fin (n + 1) => ℝ) i
      (a * x i + b * p.1) (ouShiftFin t x' p.2)
  let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let G : ℝ × (Fin n → ℝ) → ℝ := fun p => secondPartial i f (φ p)
  let H : ℝ × (Fin n → ℝ) → ℝ := fun p => p.1 * partialDeriv i f (φ p)
  have hφ_meas : Measurable φ := by
    refine measurable_pi_iff.2 ?_
    intro j
    by_cases hji : j = i
    · subst hji
      simpa [φ, a, b] using
        ((measurable_const).add ((measurable_const).mul measurable_fst))
    · rcases Fin.exists_succAbove_eq hji with ⟨k, rfl⟩
      simpa [φ, x', a, b, ouShiftFin] using
        ((measurable_const).add ((measurable_const).mul ((measurable_pi_apply k).comp measurable_snd)))
  have hG_int : Integrable G (Gaussian1D.γ.prod (γFin n)) := by
    refine Integrable.mono' (integrable_const M) ?_ ?_
    · exact ((IsCoreFin.secondPartial_measurable hf_core i).comp hφ_meas).aestronglyMeasurable
    · filter_upwards with p
      exact (hM (φ p)).2.2 i
  have hH_int : Integrable H (Gaussian1D.γ.prod (γFin n)) := by
    refine Integrable.mono'
      ((((memLp_id_gaussianReal 1).integrable le_rfl).abs.comp_fst (γFin n)).const_mul M)
      ?_ ?_
    · refine ((measurable_fst.mul ?_).aestronglyMeasurable)
      exact (IsCoreFin.partial_measurable hf_core i).comp hφ_meas
    · filter_upwards with p
      have hp : ‖partialDeriv i f (φ p)‖ ≤ M := (hM (φ p)).2.1 i
      calc
        ‖H p‖
          = |p.1| * ‖partialDeriv i f (φ p)‖ := by simp [H, norm_mul, Real.norm_eq_abs]
        _ ≤ |p.1| * M := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        _ = M * |p.1| := by ring
  have hsplit :
      ∫ y, y i * partialDeriv i f (ouShiftFin t x y) ∂γFin (n + 1) =
        ∫ p, H p ∂(Gaussian1D.γ.prod (γFin n)) := by
    have he : MeasurePreserving e (γFin (n + 1)) (Gaussian1D.γ.prod (γFin n)) :=
      measurePreserving_piFinSuccAbove_γFin (n := n) i
    have hEq : (fun y : Fin (n + 1) → ℝ => y i * partialDeriv i f (ouShiftFin t x y)) = H ∘ e := by
      funext y
      have hx : i.insertNth (x i) x' = x := by
        simpa [x'] using (Fin.insertNth_self_removeNth i x)
      have hy : i.insertNth (y i) (i.removeNth y) = y := by
        simpa using (Fin.insertNth_self_removeNth i y)
      change y i * partialDeriv i f (ouShiftFin t x y) = H (y i, i.removeNth y)
      rw [← hx, ← hy, ouShiftFin_insertNth]
      simpa [a, b, H, φ]
    calc
      ∫ y, y i * partialDeriv i f (ouShiftFin t x y) ∂γFin (n + 1)
        = ∫ y, (H ∘ e) y ∂γFin (n + 1) := by rw [hEq]
      _ = ∫ p, H p ∂(Gaussian1D.γ.prod (γFin n)) := he.integral_comp' H
  have hGsplit :
      ∫ p, G p ∂(Gaussian1D.γ.prod (γFin n)) = ouSemigroupFin t (secondPartial i f) x := by
    have he : MeasurePreserving e (γFin (n + 1)) (Gaussian1D.γ.prod (γFin n)) :=
      measurePreserving_piFinSuccAbove_γFin (n := n) i
    have hEq : (fun y : Fin (n + 1) → ℝ => secondPartial i f (ouShiftFin t x y)) = G ∘ e := by
      funext y
      have hx : i.insertNth (x i) x' = x := by
        simpa [x'] using (Fin.insertNth_self_removeNth i x)
      have hy : i.insertNth (y i) (i.removeNth y) = y := by
        simpa using (Fin.insertNth_self_removeNth i y)
      change secondPartial i f (ouShiftFin t x y) = G (y i, i.removeNth y)
      rw [← hx, ← hy, ouShiftFin_insertNth]
      simpa [a, b, G, φ]
    calc
      ∫ p, G p ∂(Gaussian1D.γ.prod (γFin n))
        = ∫ y, G (e y) ∂γFin (n + 1) := by symm; exact he.integral_comp' G
      _ = ∫ y, (G ∘ e) y ∂γFin (n + 1) := by rfl
      _ = ∫ y, secondPartial i f (ouShiftFin t x y) ∂γFin (n + 1) := by rw [← hEq]
      _ = ouSemigroupFin t (secondPartial i f) x := rfl
  have hb_le_one : |b| ≤ 1 := by
    have hb_nn : 0 ≤ b := by simp [b]
    rw [abs_of_nonneg hb_nn]
    by_cases hrad : 0 ≤ 1 - exp (-2 * t)
    · have hsqrt : sqrt (1 - exp (-2 * t)) ≤ 1 := by
        refine (Real.sqrt_le_iff).2 ?_
        constructor
        · positivity
        · have hexp_nonneg : 0 ≤ exp (-2 * t) := by positivity
          linarith
      simpa [b] using hsqrt
    · have hzero : sqrt (1 - exp (-2 * t)) = 0 :=
        Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hrad)
      simpa [b, hzero]
  have hinner :
      ∀ z : Fin n → ℝ,
        ∫ u, H (u, z) ∂Gaussian1D.γ =
          b * ∫ u, secondPartial i f (i.insertNth (a * x i + b * u) (ouShiftFin t x' z))
            ∂Gaussian1D.γ := by
    intro z
    let base : Fin (n + 1) → ℝ := i.insertNth 0 (ouShiftFin t x' z)
    let g : ℝ → ℝ := fun u => coordSection i base (partialDeriv i f) (a * x i + b * u)
    have hg_C1 : ContDiff ℝ 1 g := by
      have hsec : ContDiff ℝ ∞ (coordSection i base (partialDeriv i f)) :=
        section_contDiff (IsCoreFin.partial_contDiff hf_core i) i base
      have h_aff : ContDiff ℝ 1 (fun u : ℝ => a * x i + b * u) := by
        exact contDiff_const.add (contDiff_const.mul contDiff_id)
      simpa [g] using (hsec.of_le (by simp)).comp h_aff
    have hg_bd : ∀ u, |g u| ≤ M := by
      intro u
      simp [g, coordSection]
      rw [← Real.norm_eq_abs]
      exact (hM _).2.1 i
    have hderiv_eq :
        ∀ u, deriv g u = b * secondPartial i f (Function.update base i (a * x i + b * u)) := by
      intro u
      have h_aff : HasDerivAt (fun s : ℝ => a * x i + b * s) b u := by
        simpa [a, b] using ((hasDerivAt_id u).const_mul b).const_add (a * x i)
      have h_part :
          HasDerivAt (coordSection i base (partialDeriv i f))
            (secondPartial i f (Function.update base i (a * x i + b * u))) (a * x i + b * u) :=
        section_hasDerivAt (IsCoreFin.partial_contDiff hf_core i) i base (a * x i + b * u)
      simpa [g, mul_comm] using (h_part.comp u h_aff).deriv
    have hg'_bd : ∀ u, |deriv g u| ≤ M := by
      intro u
      rw [hderiv_eq u, abs_mul]
      have hsec_bd : |secondPartial i f (Function.update base i (a * x i + b * u))| ≤ M := by
        rw [← Real.norm_eq_abs]
        exact (hM _).2.2 i
      calc
        |b| * |secondPartial i f (Function.update base i (a * x i + b * u))|
          ≤ 1 * M := mul_le_mul hb_le_one hsec_bd (abs_nonneg _) (by positivity)
        _ = M := by ring
    have hstein := Gaussian1D.stein_identity_standard hg_C1 hg_bd hg'_bd
    have hφ_update : ∀ u : ℝ,
        φ (u, z) = Function.update base i (a * x i + b * u) := by
      intro u
      ext j
      by_cases hji : j = i
      · subst hji
        simp [φ, base]
      · rcases Fin.exists_succAbove_eq hji with ⟨k, rfl⟩
        simp [φ, base, x', ouShiftFin]
    rw [show (fun u => H (u, z)) = fun u => u * g u from by
      funext u
      simp [H, g, coordSection, hφ_update u]]
    rw [hstein, show deriv g = fun u => b * secondPartial i f (Function.update base i (a * x i + b * u))
      from by funext u; exact hderiv_eq u, integral_const_mul]
    congr 2
    ext u
    rw [← hφ_update u]
  have houter :
      ∫ p, H p ∂(Gaussian1D.γ.prod (γFin n)) =
        b * ∫ p, G p ∂(Gaussian1D.γ.prod (γFin n)) := by
    calc
      ∫ p, H p ∂(Gaussian1D.γ.prod (γFin n))
        = ∫ z, ∫ u, H (u, z) ∂Gaussian1D.γ ∂γFin n := by
            rw [integral_prod_symm H hH_int]
      _ 
        = ∫ z, b * ∫ u,
            G (u, z) ∂Gaussian1D.γ ∂γFin n := by
                refine integral_congr_ae (Filter.Eventually.of_forall hinner)
      _ = b * ∫ z, ∫ u,
            G (u, z)
              ∂Gaussian1D.γ ∂γFin n := by
                rw [integral_const_mul]
      _ = b * ∫ p, G p ∂(Gaussian1D.γ.prod (γFin n)) := by
            rw [integral_prod_symm G hG_int]
  calc
    ∫ y, y i * partialDeriv i f (ouShiftFin t x y) ∂γFin (n + 1)
      = ∫ p, H p ∂(Gaussian1D.γ.prod (γFin n)) := hsplit
    _ = b * ∫ p, G p ∂(Gaussian1D.γ.prod (γFin n)) := houter
    _ = b * ouSemigroupFin t (secondPartial i f) x := by rw [hGsplit]

theorem sum_smul_single (v : Fin n → ℝ) :
    (∑ i : Fin n, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) = v := by
  ext j
  simp [Pi.single_apply]

theorem fderiv_apply_eq_sum_partial {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v : Fin n → ℝ) :
    fderiv ℝ f x v = ∑ i : Fin n, v i * partialDeriv i f x := by
  have hdiff : DifferentiableAt ℝ f x := (hf.differentiable (by simp)).differentiableAt
  calc
    fderiv ℝ f x v = (fderiv ℝ f x) (∑ i : Fin n, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
      rw [sum_smul_single]
    _ = ∑ i : Fin n, (fderiv ℝ f x) (v i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
      rw [map_sum]
    _ = ∑ i : Fin n, v i * partialDeriv i f x := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [ContinuousLinearMap.map_smul]
      simp [partialDeriv, smul_eq_mul]

theorem IsCoreFin.exists_lipschitzWith {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ∃ C : NNReal, LipschitzWith C f := by
  obtain ⟨hf_smooth, M, hM⟩ := hf
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
  refine ⟨⟨n * M, by positivity⟩, ?_⟩
  refine lipschitzWith_of_nnnorm_fderiv_le (hf_smooth.differentiable (by simp)) ?_
  intro x
  have hbound : ‖fderiv ℝ f x‖ ≤ n * M := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
    intro v
    have hcoord : ∀ i : Fin n, ‖v i‖ ≤ ‖v‖ := by
      intro i
      exact norm_le_pi_norm v i
    have hvsum : ∑ i : Fin n, ‖v i‖ ≤ n * ‖v‖ := by
      calc
        ∑ i : Fin n, ‖v i‖ ≤ ∑ i : Fin n, ‖v‖ := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact hcoord i
        _ = n * ‖v‖ := by simp [nsmul_eq_mul]
    calc
      ‖fderiv ℝ f x v‖ = ‖∑ i : Fin n, v i * partialDeriv i f x‖ := by
        rw [fderiv_apply_eq_sum_partial hf_smooth]
      _ ≤ ∑ i : Fin n, ‖v i * partialDeriv i f x‖ := by
            simpa using (norm_sum_le Finset.univ (fun i : Fin n => v i * partialDeriv i f x))
      _ = ∑ i : Fin n, ‖v i‖ * ‖partialDeriv i f x‖ := by
            congr with i
            rw [norm_mul]
      _ ≤ ∑ i : Fin n, ‖v i‖ * M := by
            refine Finset.sum_le_sum ?_
            intro i hi
            gcongr
            exact (hM x).2.1 i
      _ = (∑ i : Fin n, ‖v i‖) * M := by rw [Finset.sum_mul]
      _ ≤ (n * ‖v‖) * M := by
            exact mul_le_mul_of_nonneg_right hvsum hM_nn
      _ = (n * M) * ‖v‖ := by ring
  exact_mod_cast hbound

theorem hasLineDerivAt_ouSemigroupFin
    (t : ℝ) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (x v : Fin n → ℝ) :
    HasLineDerivAt ℝ (ouSemigroupFin t f)
      (exp (-t) * ∫ y, ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t x y) ∂γFin n) x v := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  set F : ℝ → (Fin n → ℝ) → ℝ := fun s y => f (ouShiftFin t (x + s • v) y)
  set F' : ℝ → (Fin n → ℝ) → ℝ := fun s y =>
    a * ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t (x + s • v) y)
  have hs : Set.Ioo (-1 : ℝ) 1 ∈ nhds (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) zero_lt_one
  obtain ⟨hf_smooth, M, hM⟩ := hf
  have hf_core : IsCoreFin f := ⟨hf_smooth, M, hM⟩
  have hF_meas : ∀ s, AEStronglyMeasurable (F s) (γFin n) := by
    intro s
    have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t (x + s • v) y) := by
      continuity
    exact ((hf_smooth.continuous.comp hcont_shift).measurable.aestronglyMeasurable)
  have hF_int : Integrable (F 0) (γFin n) := by
    refine Integrable.mono' (integrable_const M) (hF_meas 0) ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    simpa [F, a, b] using (hM (ouShiftFin t x y)).1
  have hF'_meas : AEStronglyMeasurable (F' 0) (γFin n) := by
    have hmeas_term : ∀ i : Fin n,
        Measurable (fun y : Fin n → ℝ => v i * partialDeriv i f (ouShiftFin t x y)) := by
      intro i
      have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
        continuity
      exact measurable_const.mul (((hf_core.partial_continuous i).comp hcont_shift).measurable)
    have hmeas_sum : Measurable (fun y : Fin n → ℝ =>
        ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t x y)) :=
      Finset.measurable_sum Finset.univ (fun i _ => hmeas_term i)
    simpa [F', a] using (measurable_const.mul hmeas_sum).aestronglyMeasurable
  have h_bound_int : Integrable (fun _ : Fin n → ℝ => |a| * (n * M * ‖v‖)) (γFin n) :=
    integrable_const _
  have h_bound :
      ∀ᵐ y ∂γFin n, ∀ s ∈ Set.Ioo (-1 : ℝ) 1,
        ‖F' s y‖ ≤ |a| * (n * M * ‖v‖) := by
    refine Filter.Eventually.of_forall ?_
    intro y s hs_mem
    have hvsum : ∑ i : Fin n, ‖v i‖ ≤ n * ‖v‖ := by
      calc
        ∑ i : Fin n, ‖v i‖ ≤ ∑ i : Fin n, ‖v‖ := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact norm_le_pi_norm v i
        _ = n * ‖v‖ := by simp [nsmul_eq_mul]
    have hsum :
        ‖∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t (x + s • v) y)‖ ≤ n * M * ‖v‖ := by
      calc
        ‖∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t (x + s • v) y)‖
            ≤ ∑ i : Fin n, ‖v i * partialDeriv i f (ouShiftFin t (x + s • v) y)‖ := by
                simpa using
                  (norm_sum_le Finset.univ
                    (fun i : Fin n => v i * partialDeriv i f (ouShiftFin t (x + s • v) y)))
        _ = ∑ i : Fin n, ‖v i‖ * ‖partialDeriv i f (ouShiftFin t (x + s • v) y)‖ := by
              congr with i
              rw [norm_mul]
        _ ≤ ∑ i : Fin n, ‖v i‖ * M := by
              refine Finset.sum_le_sum ?_
              intro i hi
              gcongr
              exact (hM (ouShiftFin t (x + s • v) y)).2.1 i
        _ = (∑ i : Fin n, ‖v i‖) * M := by rw [Finset.sum_mul]
        _ ≤ (n * ‖v‖) * M := by
              exact mul_le_mul_of_nonneg_right hvsum ((norm_nonneg _).trans (hM 0).1)
        _ = n * M * ‖v‖ := by ring
    show ‖a * ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t (x + s • v) y)‖ ≤
        |a| * (n * M * ‖v‖)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hsum (abs_nonneg a)
  have h_diff :
      ∀ᵐ y ∂γFin n, ∀ s ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt (F · y) (F' s y) s := by
    refine Filter.Eventually.of_forall ?_
    intro y s hs_mem
    have h_inner :
        HasDerivAt (fun u : ℝ => ouShiftFin t (x + u • v) y) (a • v) s := by
      set z : Fin n → ℝ := ouShiftFin t x y
      have h_eq :
          (fun u : ℝ => ouShiftFin t (x + u • v) y) = fun u => z + u • (a • v) := by
        funext u
        ext j
        simp [ouShiftFin, z, a, Pi.smul_apply, smul_eq_mul]
        ring
      have hraw : HasDerivAt (fun u : ℝ => z + u • (a • v)) (a • v) s := by
        simpa using (((hasDerivAt_id s).smul_const (a • v)).const_add z)
      simpa [h_eq] using hraw
    have h_f :
        HasFDerivAt f (fderiv ℝ f (ouShiftFin t (x + s • v) y))
          (ouShiftFin t (x + s • v) y) :=
      ((hf_smooth.differentiable (by simp)).differentiableAt).hasFDerivAt
    have h_comp := h_f.comp_hasDerivAt s h_inner
    have htarget :
        (fderiv ℝ f (ouShiftFin t (x + s • v) y)) (a • v) =
          a * ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t (x + s • v) y) := by
      rw [fderiv_apply_eq_sum_partial hf_smooth (ouShiftFin t (x + s • v) y) (a • v)]
      simp [a, Finset.mul_sum, smul_eq_mul]
      ring
    simpa [F, F', htarget] using h_comp
  obtain ⟨_, h_deriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
      (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas h_bound h_bound_int h_diff
  have h_lhs : (fun s => ∫ y, F s y ∂γFin n) = fun s => ouSemigroupFin t f (x + s • v) := rfl
  have h_rhs :
      ∫ y, F' 0 y ∂γFin n =
        exp (-t) * ∫ y, ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t x y) ∂γFin n := by
    have hF0 :
        (fun y => F' 0 y) =
          (fun y => a * ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t x y)) := by
      funext y
      simp [F', a]
    rw [hF0, integral_const_mul]
  simpa [HasLineDerivAt, h_lhs, h_rhs]
    using h_deriv

theorem ouSemigroupFin_exists_lipschitzWith
    (t : ℝ) (ht : 0 ≤ t) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ∃ C : NNReal, LipschitzWith C (ouSemigroupFin t f) := by
  obtain ⟨C, hC⟩ := hf.exists_lipschitzWith
  obtain ⟨hf_smooth, M, hM⟩ := hf
  have hf_core : IsCoreFin f := ⟨hf_smooth, M, hM⟩
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
  have hf_cont : Continuous f := hf_core.continuous
  refine ⟨C, LipschitzWith.of_dist_le_mul ?_⟩
  intro x x'
  have hsec_int : ∀ x₀ : Fin n → ℝ, Integrable (fun y => f (ouShiftFin t x₀ y)) (γFin n) := by
    intro x₀
    refine Integrable.mono' (integrable_const M) ?_ ?_
    · have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x₀ y) := by
        continuity
      exact ((hf_cont.comp hcont_shift).measurable.aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun y => (hM (ouShiftFin t x₀ y)).1)
  have hdiff_int :
      Integrable (fun y => f (ouShiftFin t x y) - f (ouShiftFin t x' y)) (γFin n) := by
    refine Integrable.mono' (integrable_const (2 * M)) ?_ ?_
    · have hcontx : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by continuity
      have hcontx' : Continuous (fun y : Fin n → ℝ => ouShiftFin t x' y) := by continuity
      exact (((hf_cont.comp hcontx).sub (hf_cont.comp hcontx')).measurable.aestronglyMeasurable)
    · refine Filter.Eventually.of_forall ?_
      intro y
      calc
        ‖f (ouShiftFin t x y) - f (ouShiftFin t x' y)‖
            ≤ ‖f (ouShiftFin t x y)‖ + ‖f (ouShiftFin t x' y)‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hM (ouShiftFin t x y)).1 (hM (ouShiftFin t x' y)).1
        _ = 2 * M := by ring
  have hpoint :
      ∀ y : Fin n → ℝ,
        ‖f (ouShiftFin t x y) - f (ouShiftFin t x' y)‖ ≤ (C : ℝ) * ‖x - x'‖ := by
    intro y
    set a := exp (-t)
    have ha_le_one : |a| ≤ 1 := by
      rw [abs_of_nonneg (exp_pos (-t)).le]
      exact Real.exp_le_one_iff.mpr (by linarith)
    have hshift : ouShiftFin t x y - ouShiftFin t x' y = a • (x - x') := by
      ext i
      simp [ouShiftFin, a, Pi.smul_apply, smul_eq_mul]
      ring
    have hmul : |a| * ‖x - x'‖ ≤ ‖x - x'‖ := by
      have hxnn : 0 ≤ ‖x - x'‖ := norm_nonneg _
      nlinarith
    calc
      ‖f (ouShiftFin t x y) - f (ouShiftFin t x' y)‖
          ≤ (C : ℝ) * ‖ouShiftFin t x y - ouShiftFin t x' y‖ := hC.norm_sub_le _ _
      _ = (C : ℝ) * ‖a • (x - x')‖ := by rw [hshift]
      _ = (C : ℝ) * (|a| * ‖x - x'‖) := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ (C : ℝ) * ‖x - x'‖ := by
            gcongr
  have hsub :
      ouSemigroupFin t f x - ouSemigroupFin t f x' =
        ∫ y, f (ouShiftFin t x y) - f (ouShiftFin t x' y) ∂γFin n := by
    unfold ouSemigroupFin
    rw [integral_sub (hsec_int x) (hsec_int x')]
  calc
    dist (ouSemigroupFin t f x) (ouSemigroupFin t f x')
        = ‖∫ y, f (ouShiftFin t x y) - f (ouShiftFin t x' y) ∂γFin n‖ := by
            rw [dist_eq_norm, hsub]
    _ ≤ ∫ y, ‖f (ouShiftFin t x y) - f (ouShiftFin t x' y)‖ ∂γFin n := norm_integral_le_integral_norm _
    _ ≤ ∫ _y, (C : ℝ) * ‖x - x'‖ ∂γFin n := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
          · exact integrable_const _
          · exact Filter.Eventually.of_forall hpoint
    _ = (C : ℝ) * dist x x' := by
          rw [integral_const, dist_eq_norm]
          simp

theorem hasFDerivAt_ouSemigroupFin
    (t : ℝ) (ht : 0 ≤ t) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (x : Fin n → ℝ) :
    HasFDerivAt (ouSemigroupFin t f)
      (∑ i : Fin n,
        (exp (-t) * ouSemigroupFin t (partialDeriv i f) x) •
          (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
  obtain ⟨C, hC⟩ := ouSemigroupFin_exists_lipschitzWith (n := n) t ht hf
  have hf_core : IsCoreFin f := hf
  let L : (Fin n → ℝ) →L[ℝ] ℝ :=
    ∑ i : Fin n, (exp (-t) * ouSemigroupFin t (partialDeriv i f) x) •
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)
  refine hC.hasFDerivAt_of_hasLineDerivAt_of_closure (s := Set.univ) ?_ ?_
  · simpa using (subset_univ (sphere (0 : Fin n → ℝ) 1))
  · intro v hv
    have hint_term : ∀ i : Fin n,
        Integrable (fun y : Fin n → ℝ => v i * partialDeriv i f (ouShiftFin t x y)) (γFin n) := by
      intro i
      obtain ⟨_, M, hM⟩ := hf
      have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
        continuity
      refine Integrable.mono' (integrable_const (‖v i‖ * M))
        ((measurable_const.mul ((hf_core.partial_continuous i).comp hcont_shift).measurable).aestronglyMeasurable) ?_
      refine Filter.Eventually.of_forall ?_
      intro y
      rw [norm_mul]
      gcongr
      exact (hM (ouShiftFin t x y)).2.1 i
    have hline := hasLineDerivAt_ouSemigroupFin (n := n) t hf x v
    convert hline using 1
    calc
      L v = ∑ i : Fin n, (exp (-t) * ouSemigroupFin t (partialDeriv i f) x) * v i := by
        simp [L, mul_comm]
      _ = exp (-t) * ∑ i : Fin n, v i * ouSemigroupFin t (partialDeriv i f) x := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
      _ = exp (-t) *
            ∑ i : Fin n, v i * ∫ y, partialDeriv i f (ouShiftFin t x y) ∂γFin n := by
              simp [ouSemigroupFin]
      _ = exp (-t) *
            ∑ i : Fin n, ∫ y, v i * partialDeriv i f (ouShiftFin t x y) ∂γFin n := by
              congr 2 with i
              rw [← integral_const_mul]
      _ = exp (-t) *
            ∫ y, ∑ i : Fin n, v i * partialDeriv i f (ouShiftFin t x y) ∂γFin n := by
              rw [integral_finset_sum Finset.univ (fun i _ => hint_term i)]

theorem fderiv_ouSemigroupFin_eq
    (t : ℝ) (ht : 0 ≤ t) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    fderiv ℝ (ouSemigroupFin t f) =
      fun x =>
        ∑ i : Fin n,
          (exp (-t) * ouSemigroupFin t (partialDeriv i f) x) •
            (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) := by
  funext x
  exact (hasFDerivAt_ouSemigroupFin (n := n) t ht hf x).fderiv

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

theorem partialDeriv_ouSemigroupFin_eq
    (t : ℝ) (ht : 0 ≤ t) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (i : Fin n) :
    partialDeriv i (ouSemigroupFin t f) =
      fun x => exp (-t) * ouSemigroupFin t (partialDeriv i f) x := by
  funext x
  rw [partialDeriv, (hasFDerivAt_ouSemigroupFin (n := n) t ht hf x).fderiv]
  have hsum :
      (∑ j : Fin n,
        ((exp (-t) * ouSemigroupFin t (partialDeriv j f) x) •
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) (Pi.single i (1 : ℝ))) =
      exp (-t) * ouSemigroupFin t (partialDeriv i f) x := by
    rw [Finset.sum_eq_single i]
    · simp [ContinuousLinearMap.proj_apply]
    · intro j _ hji
      simp [ContinuousLinearMap.proj_apply, Pi.single_apply, hji]
    · simp [ContinuousLinearMap.proj_apply]
  simpa using hsum

theorem section_deriv_ouSemigroupFin_eq {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (t : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    deriv (fun s => ouSemigroupFin t f (Function.update x i s)) =
      fun s => exp (-t) * ouSemigroupFin t (partialDeriv i f) (Function.update x i s) := by
  have hf_core : IsCoreFin f := hf
  have hf_cont : ContDiff ℝ ∞ f := hf.contDiff
  obtain ⟨_, M, hM⟩ := hf
  funext s
  exact (hasDerivAt_coordSection_ouSemigroupFin_C1 (t := t)
    (hf_C1 := hf_cont.of_le (by simp))
    (i := i)
    (hM0 := fun z => (hM z).1)
    (hM1 := fun z => (hM z).2.1 i)
    (x := x) (s₀ := s)).deriv

theorem section_secondDeriv_ouSemigroupFin_eq {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f)
    (t : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    deriv (deriv (fun s => ouSemigroupFin t f (Function.update x i s))) =
      fun s => exp (-2 * t) * ouSemigroupFin t (secondPartial i f) (Function.update x i s) := by
  have hf_core : IsCoreFin f := hf
  have hf_partial : ContDiff ℝ ∞ (partialDeriv i f) := hf.partial_contDiff i
  obtain ⟨_, M, hM⟩ := hf
  funext s
  have h :=
    hasDerivAt_coordSection_ouSemigroupFin_C1 (t := t)
      (hf_C1 := hf_partial.of_le (by simp))
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
  have hsection : ContDiff ℝ ∞ (coordSection i x f) := by
    exact section_contDiff hf_smooth i x
  refine ⟨hsection, ⟨M, fun s => ?_⟩⟩
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

theorem integrable_abs_eval_γFin (i : Fin n) :
    Integrable (fun x : Fin n → ℝ => |x i|) (γFin n) := by
  have heval : MeasurePreserving (Function.eval i) (γFin n) Gaussian1D.γ := by
    simpa [γFin] using
      (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => Gaussian1D.γ) i)
  simpa [Function.comp, Function.eval] using
    heval.integrable_comp_of_integrable (((memLp_id_gaussianReal 1).integrable le_rfl).abs)

theorem integrable_sum_abs_γFin :
    Integrable (fun x : Fin n → ℝ => ∑ i : Fin n, |x i|) (γFin n) := by
  simpa using
    (integrable_finset_sum (s := Finset.univ)
      (f := fun i (x : Fin n → ℝ) => |x i|)
      (fun i _ => integrable_abs_eval_γFin (n := n) i))

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
    have hf_core : IsCoreFin f := ⟨hf_smooth, Mf, hfM⟩
    have hg_core : IsCoreFin g := ⟨hg_smooth, Mg, hgM⟩
    have hpartialf_smooth : ContDiff ℝ ∞ (partialDeriv i f) := hf_core.partial_contDiff i
    have hpartialg_smooth : ContDiff ℝ ∞ (partialDeriv i g) := hg_core.partial_contDiff i
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
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
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
    have hf_core : IsCoreFin f := ⟨hf_smooth, Mf, hfM⟩
    have hg_core : IsCoreFin g := ⟨hg_smooth, Mg, hgM⟩
    have hpartialf_smooth : ContDiff ℝ ∞ (partialDeriv i f) := hf_core.partial_contDiff i
    have hpartialg_smooth : ContDiff ℝ ∞ (partialDeriv i g) := hg_core.partial_contDiff i
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
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
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

theorem stronglyMeasurable_ouSemigroupFin (t : ℝ) {g : (Fin n → ℝ) → ℝ}
    (hg_meas : Measurable g) :
    StronglyMeasurable (ouSemigroupFin t g) := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  have hmix_sm : StronglyMeasurable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => g (mixCLM (n := n) a b p)) :=
    (hg_meas.comp (mixCLM (n := n) a b).continuous.measurable).stronglyMeasurable
  have hEq :
      (fun x => ouSemigroupFin t g x) =
        fun x => ∫ y, g (mixCLM (n := n) a b (x, y)) ∂γFin n := by
    funext x
    have hxy :
        (fun y : Fin n → ℝ => g (ouShiftFin t x y)) =
          fun y : Fin n → ℝ => g (mixCLM (n := n) a b (x, y)) := by
      funext y
      have harg : ouShiftFin t x y = mixCLM (n := n) a b (x, y) := by
        ext i
        simp [ouShiftFin, mixCLM_apply, a, b]
      exact congrArg g harg
    simp [ouSemigroupFin, hxy]
  simpa [hEq] using hmix_sm.integral_prod_right' (ν := γFin n)

theorem integrable_of_bound {g : (Fin n → ℝ) → ℝ} {M : ℝ}
    (hg_meas : Measurable g) (hM : ∀ x, ‖g x‖ ≤ M) :
    Integrable g (γFin n) := by
  refine Integrable.mono' (integrable_const M) hg_meas.aemeasurable.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall hM

theorem norm_ouSemigroupFin_le_of_bound (t : ℝ) {g : (Fin n → ℝ) → ℝ}
    (hg_meas : Measurable g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (x : Fin n → ℝ) :
    ‖ouSemigroupFin t g x‖ ≤ M := by
  have hsec_int : Integrable (fun y : Fin n → ℝ => g (ouShiftFin t x y)) (γFin n) := by
    have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
      continuity
    refine integrable_of_bound (M := M)
      ((hg_meas.comp hcont_shift.measurable)) ?_
    intro y
    exact hM (ouShiftFin t x y)
  calc
    ‖ouSemigroupFin t g x‖ = ‖∫ y, g (ouShiftFin t x y) ∂γFin n‖ := rfl
    _ ≤ ∫ y, ‖g (ouShiftFin t x y)‖ ∂γFin n := norm_integral_le_integral_norm _
    _ ≤ ∫ _y : Fin n → ℝ, M ∂γFin n := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
          · exact integrable_const M
          · exact Filter.Eventually.of_forall (fun y => hM (ouShiftFin t x y))
    _ = M := by simp

theorem continuous_ouSemigroupFin_of_bound (t : ℝ) {g : (Fin n → ℝ) → ℝ}
    (hg_cont : Continuous g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) :
    Continuous (ouSemigroupFin t g) := by
  rw [continuous_iff_continuousAt]
  intro x
  show Tendsto (fun x' => ∫ y, g (ouShiftFin t x' y) ∂γFin n) (nhds x)
    (nhds (∫ y, g (ouShiftFin t x y) ∂γFin n))
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun _ => M) ?_ ?_ (integrable_const M) ?_
  · filter_upwards with x'
    have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x' y) := by
      continuity
    exact (hg_cont.comp hshift).aestronglyMeasurable
  · filter_upwards with x'
    filter_upwards with y
    exact hM (ouShiftFin t x' y)
  · filter_upwards with y
    have h_arg : Tendsto (fun x' : Fin n → ℝ => ouShiftFin t x' y) (nhds x)
        (nhds (ouShiftFin t x y)) := by
      have hcont : Continuous (fun x' : Fin n → ℝ => ouShiftFin t x' y) := by
        continuity
      exact hcont.tendsto x
    exact (hg_cont.tendsto _).comp h_arg

theorem ouSemigroupFin_preserves_bound (t : ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) :
    ∃ M : ℝ, ∀ x, ‖ouSemigroupFin t f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  exact ⟨M, fun x => norm_ouSemigroupFin_le_of_bound (n := n) t hf.measurable hM x⟩

theorem partialDeriv_ouSemigroupFin_preserves_bound (t : ℝ) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) :
    ∃ M : ℝ, ∀ x, ‖partialDeriv i (ouSemigroupFin t f) x‖ ≤ M := by
  have hf_core : IsCoreFin f := hf
  obtain ⟨_, M, hM⟩ := hf
  refine ⟨M, ?_⟩
  intro x
  rw [partialDeriv_ouSemigroupFin_eq (n := n) t ht hf_core i]
  calc
    ‖exp (-t) * ouSemigroupFin t (partialDeriv i f) x‖
      = exp (-t) * ‖ouSemigroupFin t (partialDeriv i f) x‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
    _ ≤ exp (-t) * M := by
          gcongr
          exact norm_ouSemigroupFin_le_of_bound (n := n) t (hf_core.partial_measurable i)
            (fun y => (hM y).2.1 i) x
    _ ≤ M := by
          have hexp_le : exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
          nlinarith

theorem continuous_partialDeriv_ouSemigroupFin (t : ℝ) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) :
    Continuous (partialDeriv i (ouSemigroupFin t f)) := by
  have hf_core : IsCoreFin f := hf
  obtain ⟨_, M, hM⟩ := hf
  have hEq := partialDeriv_ouSemigroupFin_eq (n := n) t ht hf_core i
  rw [hEq]
  exact continuous_const.mul
    (continuous_ouSemigroupFin_of_bound (n := n) t (hf_core.partial_continuous i)
      (fun x => (hM x).2.1 i))

theorem contDiffOne_ouSemigroupFin
    (t : ℝ) (ht : 0 ≤ t) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ContDiff ℝ 1 (ouSemigroupFin t f) := by
  have hf_core : IsCoreFin f := hf
  obtain ⟨_, M, hM⟩ := hf
  rw [contDiff_one_iff_fderiv]
  refine ⟨?_, ?_⟩
  · intro x
    exact (hasFDerivAt_ouSemigroupFin (n := n) t ht hf_core x).differentiableAt
  · rw [show Continuous (fderiv ℝ (ouSemigroupFin t f)) ↔
        ContDiff ℝ 0 (fderiv ℝ (ouSemigroupFin t f)) by
          simpa using (contDiff_zero : ContDiff ℝ 0 (fderiv ℝ (ouSemigroupFin t f)) ↔
            Continuous (fderiv ℝ (ouSemigroupFin t f)))]
    rw [contDiff_clm_apply_iff
      (𝕜 := ℝ) (D := Fin n → ℝ) (E := Fin n → ℝ) (F := ℝ)
      (f := fderiv ℝ (ouSemigroupFin t f))]
    intro y
    refine contDiff_zero.2 ?_
    have hEq :
        (fun x => fderiv ℝ (ouSemigroupFin t f) x y) =
          fun x => ∑ i : Fin n, exp (-t) * ouSemigroupFin t (partialDeriv i f) x * y i := by
      funext x
      rw [fderiv_ouSemigroupFin_eq (n := n) t ht hf_core]
      simp [ContinuousLinearMap.proj_apply]
    rw [hEq]
    refine continuous_finset_sum _ ?_
    intro i hi
    exact ((continuous_const.mul
      (continuous_ouSemigroupFin_of_bound (n := n) t (hf_core.partial_continuous i)
        (fun x => (hM x).2.1 i))).mul continuous_const)

theorem section_secondDeriv_ouSemigroupFin_preserves_bound (t : ℝ) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) (i : Fin n) (x : Fin n → ℝ) :
    ∃ M : ℝ, ∀ s, ‖deriv (deriv (fun r => ouSemigroupFin t f (Function.update x i r))) s‖ ≤ M := by
  have hf_core : IsCoreFin f := hf
  obtain ⟨_, M, hM⟩ := hf
  refine ⟨M, ?_⟩
  intro s
  rw [section_secondDeriv_ouSemigroupFin_eq (n := n) hf_core t i x]
  calc
    ‖exp (-2 * t) * ouSemigroupFin t (secondPartial i f) (Function.update x i s)‖
      = exp (-2 * t) * ‖ouSemigroupFin t (secondPartial i f) (Function.update x i s)‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
    _ ≤ exp (-2 * t) * M := by
          gcongr
          exact norm_ouSemigroupFin_le_of_bound (n := n) t
            (hf_core.secondPartial_measurable i)
            (fun y => (hM y).2.2 i) (Function.update x i s)
    _ ≤ M := by
          have hexp_le : exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
          nlinarith

theorem ouSemigroupFin_preserves_core_bounds (t : ℝ) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    ∃ M : ℝ,
      (∀ x, ‖ouSemigroupFin t f x‖ ≤ M) ∧
      (∀ i x, ‖partialDeriv i (ouSemigroupFin t f) x‖ ≤ M) ∧
      ∀ i x s, ‖deriv (deriv (fun r => ouSemigroupFin t f (Function.update x i r))) s‖ ≤ M := by
  have hf_core : IsCoreFin f := hf
  obtain ⟨_, M, hM⟩ := hf
  refine ⟨M, ?_, ?_, ?_⟩
  · intro x
    exact norm_ouSemigroupFin_le_of_bound (n := n) t hf_core.measurable (fun y => (hM y).1) x
  · intro i x
    rw [partialDeriv_ouSemigroupFin_eq (n := n) t ht hf_core i]
    calc
      ‖exp (-t) * ouSemigroupFin t (partialDeriv i f) x‖
        = exp (-t) * ‖ouSemigroupFin t (partialDeriv i f) x‖ := by
            rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
      _ ≤ exp (-t) * M := by
            gcongr
            exact norm_ouSemigroupFin_le_of_bound (n := n) t (hf_core.partial_measurable i)
              (fun y => (hM y).2.1 i) x
      _ ≤ M := by
            have hexp_le : exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
            have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
            nlinarith
  · intro i x s
    rw [section_secondDeriv_ouSemigroupFin_eq (n := n) hf_core t i x]
    calc
      ‖exp (-2 * t) * ouSemigroupFin t (secondPartial i f) (Function.update x i s)‖
        = exp (-2 * t) *
            ‖ouSemigroupFin t (secondPartial i f) (Function.update x i s)‖ := by
              rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
      _ ≤ exp (-2 * t) * M := by
            gcongr
            exact norm_ouSemigroupFin_le_of_bound (n := n) t
              (hf_core.secondPartial_measurable i) (fun y => (hM y).2.2 i) (Function.update x i s)
      _ ≤ M := by
            have hexp_le : exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
            have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
            nlinarith

theorem sq_ouSemigroupFin_le_ouSemigroupFin_sq (t : ℝ) {g : (Fin n → ℝ) → ℝ}
    (hg_meas : Measurable g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (x : Fin n → ℝ) :
    (ouSemigroupFin t g x) ^ 2 ≤ ouSemigroupFin t (fun y => g y ^ 2) x := by
  have h_shift_meas : Measurable (fun y : Fin n → ℝ => ouShiftFin t x y) := by
    have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
      continuity
    exact hcont_shift.measurable
  have h_inner_int :
      Integrable (fun y : Fin n → ℝ => g (ouShiftFin t x y)) (γFin n) := by
    refine integrable_of_bound (M := M) (hg_meas.comp h_shift_meas) ?_
    intro y
    exact hM (ouShiftFin t x y)
  have h_inner_sq_int :
      Integrable (fun y : Fin n → ℝ => g (ouShiftFin t x y) ^ 2) (γFin n) := by
    refine integrable_of_bound (M := M ^ 2) ((hg_meas.comp h_shift_meas).pow_const 2) ?_
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : |g (ouShiftFin t x y)| ≤ M := by
      rw [← Real.norm_eq_abs]
      exact hM (ouShiftFin t x y)
    have h2 : (g (ouShiftFin t x y)) ^ 2 ≤ M ^ 2 := by
      have : |g (ouShiftFin t x y)| ^ 2 ≤ M ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      rwa [sq_abs] at this
    exact h2
  have h_conv : ConvexOn ℝ Set.univ (fun s : ℝ => s ^ 2) :=
    Even.convexOn_pow (Nat.even_iff.mpr rfl)
  have h_cont : ContinuousOn (fun s : ℝ => s ^ 2) Set.univ := (continuous_pow 2).continuousOn
  have h_closed : IsClosed (Set.univ : Set ℝ) := isClosed_univ
  have h_aem :
      ∀ᵐ y ∂γFin n, g (ouShiftFin t x y) ∈ (Set.univ : Set ℝ) :=
    Filter.Eventually.of_forall (fun _ => Set.mem_univ _)
  simpa [ouSemigroupFin] using
    ConvexOn.map_integral_le h_conv h_cont h_closed h_aem h_inner_int h_inner_sq_int

theorem ouSemigroupFin_integral_eq_of_bound (t : ℝ) (ht : 0 ≤ t)
    {g : (Fin n → ℝ) → ℝ} (hg_meas : Measurable g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) :
    ∫ x, ouSemigroupFin t g x ∂γFin n = ∫ x, g x ∂γFin n := by
  set a := exp (-t)
  set b := sqrt (1 - exp (-2 * t))
  have hmap : ((γFin n).prod (γFin n)).map (mixCLM (n := n) a b) = γFin n := by
    simpa [a, b] using ou_kernel_map_fin (n := n) t ht
  have hg_int : Integrable g (γFin n) := integrable_of_bound hg_meas hM
  have hg_map_sm : AEStronglyMeasurable g
      (((γFin n).prod (γFin n)).map (mixCLM (n := n) a b)) := by
    simpa [hmap] using hg_meas.aemeasurable.aestronglyMeasurable
  have hg_map_int : Integrable g (((γFin n).prod (γFin n)).map (mixCLM (n := n) a b)) := by
    simpa [hmap] using hg_int
  have hcomp :
      ∫ p, g (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) = ∫ x, g x ∂γFin n := by
    simpa [hmap] using
      (integral_map (f := g) (Measurable.aemeasurable (by fun_prop)) hg_map_sm).symm
  have hmix_int : Integrable (g ∘ mixCLM (n := n) a b) ((γFin n).prod (γFin n)) :=
    (integrable_map_measure hg_map_sm (Measurable.aemeasurable (by fun_prop))).mp hg_map_int
  have hprod :
      ∫ x, ∫ y, g (mixCLM (n := n) a b (x, y)) ∂γFin n ∂γFin n =
        ∫ p, g (mixCLM (n := n) a b p) ∂((γFin n).prod (γFin n)) := by
    simpa using (integral_prod (f := g ∘ mixCLM (n := n) a b) hmix_int).symm
  have hiter :
      (∫ x, ouSemigroupFin t g x ∂γFin n) =
        ∫ x, ∫ y, g (mixCLM (n := n) a b (x, y)) ∂γFin n ∂γFin n := by
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
    simp [hxy]
  rw [hiter, hprod]
  exact hcomp

theorem ouSemigroupFin_gradient_decay (f : (Fin n → ℝ) → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf : IsCoreFin f) :
    ∫ x, ouGammaFin (ouSemigroupFin t f) (ouSemigroupFin t f) x ∂γFin n ≤
      exp (-2 * t) * ∫ x, ouGammaFin f f x ∂γFin n := by
  have hf_core : IsCoreFin f := hf
  obtain ⟨_, M, hM⟩ := hf
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
  have hΓ_meas : Measurable (ouGammaFin f f) := by
    unfold ouGammaFin
    refine Finset.measurable_sum _ ?_
    intro i hi
    exact (hf_core.partial_measurable i).mul (hf_core.partial_measurable i)
  have hΓ_bound : ∀ x, ‖ouGammaFin f f x‖ ≤ n * M ^ 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (ouGammaFin_nonneg (f := f) x)]
    unfold ouGammaFin
    calc
      ∑ i : Fin n, partialDeriv i f x * partialDeriv i f x
          ≤ ∑ i : Fin n, M ^ 2 := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have h1 : |partialDeriv i f x| ≤ M := by
                rw [← Real.norm_eq_abs]
                exact (hM x).2.1 i
              have h2 : (partialDeriv i f x) ^ 2 ≤ M ^ 2 := by
                have : |partialDeriv i f x| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
                rwa [sq_abs] at this
              simpa [pow_two] using h2
      _ = n * M ^ 2 := by simp [nsmul_eq_mul]
  have hpt :
      ∀ x, ouGammaFin (ouSemigroupFin t f) (ouSemigroupFin t f) x ≤
        exp (-2 * t) * ouSemigroupFin t (ouGammaFin f f) x := by
    intro x
    have h_terms :
        ∀ i : Fin n,
          partialDeriv i (ouSemigroupFin t f) x * partialDeriv i (ouSemigroupFin t f) x ≤
            exp (-2 * t) *
              ouSemigroupFin t (fun y => partialDeriv i f y * partialDeriv i f y) x := by
      intro i
      have hj :=
        sq_ouSemigroupFin_le_ouSemigroupFin_sq (n := n) t
          (g := partialDeriv i f) (hg_meas := hf_core.partial_measurable i)
          (hM := fun y => (hM y).2.1 i) x
      rw [partialDeriv_ouSemigroupFin_eq (n := n) t ht hf_core i]
      calc
        (exp (-t) * ouSemigroupFin t (partialDeriv i f) x) *
            (exp (-t) * ouSemigroupFin t (partialDeriv i f) x)
          = exp (-2 * t) * (ouSemigroupFin t (partialDeriv i f) x) ^ 2 := by
              rw [show exp (-2 * t) = exp (-t) * exp (-t) by
                rw [show (-2 * t : ℝ) = -t + -t by ring, exp_add]]
              ring
        _ ≤ exp (-2 * t) * ouSemigroupFin t (fun y => partialDeriv i f y ^ 2) x := by
              exact mul_le_mul_of_nonneg_left hj (exp_nonneg _)
        _ = exp (-2 * t) *
              ouSemigroupFin t (fun y => partialDeriv i f y * partialDeriv i f y) x := by
              congr 2
              ext y
              ring
    have h_sum_int :
        ∀ i : Fin n,
          Integrable
            (fun y : Fin n → ℝ =>
              partialDeriv i f (ouShiftFin t x y) * partialDeriv i f (ouShiftFin t x y)) (γFin n) := by
      intro i
      have hcont_shift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
        continuity
      refine integrable_of_bound (M := M ^ 2)
        (((hf_core.partial_measurable i).comp hcont_shift.measurable).mul
          ((hf_core.partial_measurable i).comp hcont_shift.measurable)) ?_
      intro y
      rw [norm_mul]
      have hi : ‖partialDeriv i f (ouShiftFin t x y)‖ ≤ M := (hM (ouShiftFin t x y)).2.1 i
      have hsq : ‖partialDeriv i f (ouShiftFin t x y)‖ * ‖partialDeriv i f (ouShiftFin t x y)‖
          ≤ M * M := mul_le_mul hi hi (norm_nonneg _) hM_nn
      simpa [sq] using hsq
    unfold ouGammaFin
    calc
      ∑ i : Fin n, partialDeriv i (ouSemigroupFin t f) x * partialDeriv i (ouSemigroupFin t f) x
        ≤ ∑ i : Fin n,
            exp (-2 * t) * ouSemigroupFin t (fun y => partialDeriv i f y * partialDeriv i f y) x := by
              exact Finset.sum_le_sum (fun i _ => h_terms i)
      _ = exp (-2 * t) *
            ∑ i : Fin n, ouSemigroupFin t (fun y => partialDeriv i f y * partialDeriv i f y) x := by
              rw [Finset.mul_sum]
      _ = exp (-2 * t) * ouSemigroupFin t (ouGammaFin f f) x := by
            congr 1
            calc
              ∑ i : Fin n, ouSemigroupFin t (fun y => partialDeriv i f y * partialDeriv i f y) x
                  = ∑ i : Fin n,
                      ∫ y, partialDeriv i f (ouShiftFin t x y) * partialDeriv i f (ouShiftFin t x y)
                        ∂γFin n := by
                          simp [ouSemigroupFin]
              _ = ∫ y,
                    ∑ i : Fin n,
                      partialDeriv i f (ouShiftFin t x y) * partialDeriv i f (ouShiftFin t x y)
                    ∂γFin n := by
                        rw [integral_finset_sum Finset.univ (fun i _ => h_sum_int i)]
              _ = ouSemigroupFin t (ouGammaFin f f) x := by
                    simp [ouSemigroupFin, ouGammaFin]
  have hupper_int :
      Integrable (fun x => exp (-2 * t) * ouSemigroupFin t (ouGammaFin f f) x) (γFin n) := by
    refine integrable_of_bound (M := exp (-2 * t) * (n * M ^ 2))
      ((stronglyMeasurable_ouSemigroupFin (n := n) t hΓ_meas).measurable.const_mul _) ?_
    intro x
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (norm_ouSemigroupFin_le_of_bound (n := n) t hΓ_meas hΓ_bound x) (exp_nonneg _)
  have h_inv :=
    ouSemigroupFin_integral_eq_of_bound (n := n) t ht hΓ_meas hΓ_bound
  calc
    ∫ x, ouGammaFin (ouSemigroupFin t f) (ouSemigroupFin t f) x ∂γFin n
      ≤ ∫ x, exp (-2 * t) * ouSemigroupFin t (ouGammaFin f f) x ∂γFin n := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun x => ouGammaFin_nonneg (f := ouSemigroupFin t f) x)
          · exact hupper_int
          · exact Filter.Eventually.of_forall hpt
    _ = exp (-2 * t) * ∫ x, ouGammaFin f f x ∂γFin n := by
          rw [integral_const_mul, h_inv]

theorem ouSemigroupFin_ergodic (f : (Fin n → ℝ) → ℝ) (hf : IsCoreFin f) :
    Tendsto
      (fun t => ∫ x, (ouSemigroupFin t f x) ^ 2 ∂γFin n - (∫ x, f x ∂γFin n) ^ 2)
      atTop (nhds 0) := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
  have hf_cont : Continuous f := hf.continuous
  have hf_meas : Measurable f := hf.measurable
  set Ef : ℝ := ∫ y, f y ∂γFin n with hEf_def
  have h_exp_neg_atTop : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have h_exp_neg2_atTop : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (nhds 0) := by
    have h_neg2t : Tendsto (fun t : ℝ => -2 * t) atTop atBot := by
      refine Filter.tendsto_atBot.mpr ?_
      intro B
      rw [Filter.eventually_atTop]
      refine ⟨max 1 ((1 - B) / 2), ?_⟩
      intro t ht
      have h1 : (1 - B) / 2 ≤ t := (le_max_right _ _).trans ht
      linarith
    exact Real.tendsto_exp_atBot.comp h_neg2t
  have h_b_atTop : Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t))) atTop (nhds 1) := by
    have h_inner : Tendsto (fun t : ℝ => 1 - Real.exp (-2 * t)) atTop (nhds 1) := by
      simpa using Filter.Tendsto.const_sub 1 h_exp_neg2_atTop
    simpa using h_inner.sqrt
  have h_ptwise : ∀ x, Tendsto (fun t => ouSemigroupFin t f x) atTop (nhds Ef) := by
    intro x
    show Tendsto
      (fun t => ∫ y, f (ouShiftFin t x y) ∂γFin n)
      atTop (nhds (∫ y, f y ∂γFin n))
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M) ?_ ?_ (integrable_const M) ?_
    · filter_upwards with t
      have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
        continuity
      exact (hf_meas.comp hshift.measurable).aestronglyMeasurable
    · filter_upwards with t
      filter_upwards with y
      exact hM _
    · filter_upwards with y
      have h_arg : Tendsto (fun t : ℝ => ouShiftFin t x y) atTop (nhds y) := by
        have h1 : Tendsto (fun t : ℝ => Real.exp (-t) • x) atTop (nhds 0) := by
          simpa [Pi.zero_apply] using h_exp_neg_atTop.smul_const x
        have h2 : Tendsto
            (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t)) • y) atTop (nhds y) := by
          simpa using h_b_atTop.smul_const y
        have := h1.add h2
        have h_eq :
            (fun t : ℝ => ouShiftFin t x y) =
              fun t : ℝ => Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2 * t)) • y := by
          funext t
          ext i
          simp [ouShiftFin, Pi.add_apply, Pi.smul_apply]
        simpa [h_eq, one_smul] using this
      exact (hf_cont.tendsto y).comp h_arg
  have h_bound : ∀ x t, |ouSemigroupFin t f x| ≤ M := by
    intro x t
    exact norm_ouSemigroupFin_le_of_bound (n := n) t hf_meas hM x
  have h_outer :
      Tendsto (fun t => ∫ x, (ouSemigroupFin t f x) ^ 2 ∂γFin n) atTop (nhds (Ef ^ 2)) := by
    have h_target : Ef ^ 2 = ∫ _x, Ef ^ 2 ∂γFin n := by simp
    rw [h_target]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M ^ 2) ?_ ?_ (integrable_const _) ?_
    · filter_upwards with t
      exact ((stronglyMeasurable_ouSemigroupFin (n := n) t hf_meas).pow 2).aestronglyMeasurable
    · filter_upwards with t
      filter_upwards with x
      have habs : |ouSemigroupFin t f x| ≤ M := h_bound x t
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have : |ouSemigroupFin t f x| ^ 2 ≤ M ^ 2 := by
        nlinarith [abs_nonneg (ouSemigroupFin t f x)]
      rwa [sq_abs] at this
    · filter_upwards with x
      exact (h_ptwise x).pow 2
  have := h_outer.sub_const (Ef ^ 2)
  simpa [hEf_def] using this

theorem ouSemigroupFin_entropy_sq_ergodic (f : (Fin n → ℝ) → ℝ) (hf : IsCoreFin f) :
    Tendsto
      (fun t => DirichletSpace.entropy (ds := dirichletSpaceFin (n := n))
        (ouSemigroupFin t (fun x => f x * f x))) atTop (nhds 0) := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
  have hf_cont : Continuous f := hf.continuous
  have hf_meas : Measurable f := hf.measurable
  set g : (Fin n → ℝ) → ℝ := fun x => f x * f x with hg_def
  have hg_cont : Continuous g := hf_cont.mul hf_cont
  have hg_meas : Measurable g := hg_cont.measurable
  have hg_nn : ∀ x, 0 ≤ g x := fun x => mul_self_nonneg _
  have hg_bdd : ∀ x, g x ≤ M ^ 2 := by
    intro x
    have h1 : |f x| ≤ M := by
      rw [← Real.norm_eq_abs]
      exact hM x
    have h2 : (f x) ^ 2 ≤ M ^ 2 := by
      have : |f x| ^ 2 ≤ M ^ 2 := by
        nlinarith [abs_nonneg (f x)]
      rwa [sq_abs] at this
    show f x * f x ≤ M ^ 2
    have : f x * f x = (f x) ^ 2 := by ring
    linarith
  set Eg : ℝ := ∫ y, g y ∂γFin n with hEg_def
  have h_exp_neg_atTop : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have h_exp_neg2_atTop : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (nhds 0) := by
    have h_neg2t : Tendsto (fun t : ℝ => -2 * t) atTop atBot := by
      refine Filter.tendsto_atBot.mpr ?_
      intro B
      rw [Filter.eventually_atTop]
      refine ⟨max 1 ((1 - B) / 2), ?_⟩
      intro t ht
      have h1 : (1 - B) / 2 ≤ t := (le_max_right _ _).trans ht
      linarith
    exact Real.tendsto_exp_atBot.comp h_neg2t
  have h_b_atTop : Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t))) atTop (nhds 1) := by
    have h_inner : Tendsto (fun t : ℝ => 1 - Real.exp (-2 * t)) atTop (nhds 1) := by
      simpa using Filter.Tendsto.const_sub 1 h_exp_neg2_atTop
    simpa using h_inner.sqrt
  have h_ptwise : ∀ x, Tendsto (fun t => ouSemigroupFin t g x) atTop (nhds Eg) := by
    intro x
    show Tendsto
      (fun t => ∫ y, g (ouShiftFin t x y) ∂γFin n)
      atTop (nhds (∫ y, g y ∂γFin n))
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => M ^ 2) ?_ ?_ (integrable_const _) ?_
    · filter_upwards with t
      have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
        continuity
      exact (hg_meas.comp hshift.measurable).aestronglyMeasurable
    · filter_upwards with t
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn _)]
      exact hg_bdd _
    · filter_upwards with y
      have h_arg : Tendsto (fun t : ℝ => ouShiftFin t x y) atTop (nhds y) := by
        have h1 : Tendsto (fun t : ℝ => Real.exp (-t) • x) atTop (nhds 0) := by
          simpa [Pi.zero_apply] using h_exp_neg_atTop.smul_const x
        have h2 : Tendsto
            (fun t : ℝ => Real.sqrt (1 - Real.exp (-2 * t)) • y) atTop (nhds y) := by
          simpa using h_b_atTop.smul_const y
        have := h1.add h2
        have h_eq :
            (fun t : ℝ => ouShiftFin t x y) =
              fun t : ℝ => Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2 * t)) • y := by
          funext t
          ext i
          simp [ouShiftFin, Pi.add_apply, Pi.smul_apply]
        simpa [h_eq, one_smul] using this
      exact (hg_cont.tendsto y).comp h_arg
  have h_Ptg_bdd : ∀ x t, 0 ≤ ouSemigroupFin t g x ∧ ouSemigroupFin t g x ≤ M ^ 2 := by
    intro x t
    have hint : Integrable (fun y => g (ouShiftFin t x y)) (γFin n) := by
      refine Integrable.mono' (integrable_const (M ^ 2)) ?_ ?_
      · have hshift : Continuous (fun y : Fin n → ℝ => ouShiftFin t x y) := by
          continuity
        exact (hg_meas.comp hshift.measurable).aestronglyMeasurable
      · filter_upwards with y
        rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn _)]
        exact hg_bdd _
    refine ⟨?_, ?_⟩
    · exact integral_nonneg (fun y => hg_nn _)
    · calc
        ∫ y, g (ouShiftFin t x y) ∂γFin n
            ≤ ∫ _y : Fin n → ℝ, M ^ 2 ∂γFin n := by
                exact integral_mono hint (integrable_const _) (fun y => hg_bdd _)
        _ = M ^ 2 := by simp
  have hM2_nn : (0 : ℝ) ≤ M ^ 2 := sq_nonneg M
  obtain ⟨B, hB⟩ : ∃ B, ∀ s ∈ Set.Icc (0 : ℝ) (M ^ 2), |s * Real.log s| ≤ B := by
    have h_compact : IsCompact (Set.Icc (0 : ℝ) (M ^ 2)) := isCompact_Icc
    have h_cont_abs : Continuous (fun s => |s * Real.log s|) :=
      Real.continuous_mul_log.abs
    have h_im_compact : IsCompact ((fun s => |s * Real.log s|) '' Set.Icc 0 (M ^ 2)) :=
      h_compact.image h_cont_abs
    obtain ⟨B, hB⟩ := h_im_compact.bddAbove
    refine ⟨B, fun s hs => ?_⟩
    exact hB ⟨s, hs, rfl⟩
  have h_outer_log :
      Tendsto (fun t => ∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n)
        atTop (nhds (Eg * Real.log Eg)) := by
    have h_target : Eg * Real.log Eg = ∫ _x, Eg * Real.log Eg ∂γFin n := by simp
    rw [h_target]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => B) ?_ ?_ (integrable_const _) ?_
    · filter_upwards with t
      have hPtg_sm : MeasureTheory.StronglyMeasurable (ouSemigroupFin t g) :=
        stronglyMeasurable_ouSemigroupFin (n := n) t hg_meas
      have h_log_meas : Measurable (fun x => Real.log (ouSemigroupFin t g x)) :=
        Real.measurable_log.comp hPtg_sm.measurable
      exact (hPtg_sm.measurable.mul h_log_meas).aestronglyMeasurable
    · filter_upwards with t
      filter_upwards with x
      rw [Real.norm_eq_abs]
      exact hB (ouSemigroupFin t g x) ⟨(h_Ptg_bdd x t).1, (h_Ptg_bdd x t).2⟩
    · filter_upwards with x
      have h_cont_pt : ContinuousAt (fun s => s * Real.log s) Eg :=
        Real.continuous_mul_log.continuousAt
      exact h_cont_pt.tendsto.comp (h_ptwise x)
  have h_mean : ∀ t, 0 ≤ t → ∫ x, ouSemigroupFin t g x ∂γFin n = ∫ x, g x ∂γFin n := by
    intro t ht
    refine ouSemigroupFin_integral_eq_of_bound (n := n) (M := M ^ 2) t ht hg_meas ?_
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn x)]
    exact hg_bdd x
  have h_entropy_eq : ∀ t, 0 ≤ t →
      DirichletSpace.entropy (ds := dirichletSpaceFin (n := n)) (ouSemigroupFin t g) =
        (∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n) -
          Eg * Real.log Eg := by
    intro t ht
    show
      (∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n) -
        (∫ x, ouSemigroupFin t g x ∂γFin n) * Real.log (∫ x, ouSemigroupFin t g x ∂γFin n) =
      (∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n) -
        Eg * Real.log Eg
    rw [h_mean t ht]
  have h_diff : Tendsto
      (fun t =>
        (∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n) -
          Eg * Real.log Eg) atTop (nhds 0) := by
    simpa using h_outer_log.sub_const (Eg * Real.log Eg)
  have h_eq_eventually :
      (fun t => DirichletSpace.entropy (ds := dirichletSpaceFin (n := n))
        (ouSemigroupFin t (fun x => f x * f x))) =ᶠ[atTop]
      (fun t =>
        (∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n) -
          Eg * Real.log Eg) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    simpa [g, hg_def] using h_entropy_eq t ht
  exact Tendsto.congr' h_eq_eventually.symm h_diff

/-! `ouSemigroupFin_l2_sq_hasDerivWithinAt` and the derived
`ouSemigroupFin_l2_decay_bound` are proved in the later module
`EuclideanFinBE.lean`, which can import the `L²` generator-limit
infrastructure without creating an import cycle. -/

/-! ### N1.5 textbook axiom: `C^∞` core preservation under the multivariate OU semigroup

After the `IsCoreFin` harmonization from `ContDiff ℝ ⊤` to `ContDiff ℝ ∞`,
the remaining nontrivial part of semigroup-core preservation is the
`C^∞` smoothing statement. The boundedness half is already proved by
`ouSemigroupFin_preserves_core_bounds`. What remains is the standard
kernel-smoothing fact that Mehler convolution preserves `C^∞`. -/

/-- **Multivariate OU smoothing preserves the `IsCoreFin` test algebra.**

For `t ≥ 0`, if `f` is `IsCoreFin`, then `P_t f` is again `IsCoreFin`.

Post-harmonization this means `C^∞` regularity plus the same uniform
bounds on the function, coordinate first partials, and coordinate
sectionwise second derivatives. The bounds portion is already proved in
`ouSemigroupFin_preserves_core_bounds`; the remaining load-bearing input
is the `C^∞` smoothing of the explicit Mehler kernel in the spatial
variable.

**Reference:** BGL §2.7 (OU kernel smoothing), applied coordinatewise to
the finite product Gaussian setting.

**Vetting:** gemini-3.1-pro-preview, 2026-05-13, verdict
**Flagged** pre-harmonization and **Standard / Likely correct**
post-harmonization to `ContDiff ℝ ∞`. The vet specifically confirmed
that no mixed-derivative bounds are needed for this `IsCoreFin`
predicate: the pure second partials commute with the semigroup up to the
expected `exp (-2t)` factor, so only the `C^∞` smoothing remains to be
discharged.

**Discharge plan:** rewrite `P_t f` against the explicit shifted
Gaussian density `ρ_t (x, z)`, then apply `ContDiff.integral` to push
spatial derivatives onto the kernel rather than onto `f`. This avoids
the multi-index Hermite formalization burden and matches the recommended
kernel-based proof route from the vet. -/
axiom ouSemigroupFin_preserves_IsCore {n : ℕ}
    (t : ℝ) (ht : 0 ≤ t) {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    IsCoreFin (ouSemigroupFin t f)

/-! ### N1.c: multivariate entropy decay for `f²` (BGL Thm. 5.5.2)

The 1D entropy-decay theorem is proved in `EuclideanEntropyDecay.lean`,
where the general per-coordinate building block
`Gaussian1D.boltzmannEntropy_ouSemigroup_decay_le` (FTC assembly of the
Fisher-info decay A1 and de Bruijn A2) is also extracted.

The multivariate bound is obtained by the **telescoping route** (vetted
gemini-3.1-pro-preview 2026-05-13, route confirmed by deep-think
2026-05-19): the macroscopic `(∫·)log(∫·)` terms cancel **once** for the
full operator because `ouSemigroupFin` preserves the Gaussian mean
(`ouSemigroupFin_integral_eq_of_bound`), so the centered `entropy`
difference equals the Boltzmann (`∫ h log h`) difference. The Boltzmann
difference telescopes over the per-coordinate factors with no further
macroscopic terms; each per-coordinate step is the integrated 1D bound,
and the per-coordinate Fisher informations stay controlled by
`4 · ouEnergyFin f f` via orthogonal Fisher monotonicity.

The infrastructure below is staged; the full assembly is in progress. -/

/-- The single-coordinate Ornstein–Uhlenbeck operator: the 1D OU
semigroup acting on coordinate `i` only, freezing the other
coordinates. Equals `Gaussian1D.ouSemigroup t (coordSection i x f)`
evaluated at `x i`. -/
def ouCoord (i : Fin n) (t : ℝ) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => ∫ s, f (Function.update x i
    (Real.exp (-t) * x i + Real.sqrt (1 - Real.exp (-2 * t)) * s)) ∂Gaussian1D.γ

/-- `ouCoord` is the 1D OU semigroup of the coordinate section. -/
theorem ouCoord_eq_ouSemigroup_coordSection (i : Fin n) (t : ℝ)
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    ouCoord i t f x = Gaussian1D.ouSemigroup t (coordSection i x f) (x i) := by
  unfold ouCoord Gaussian1D.ouSemigroup coordSection
  rfl

/-- Bridge: updating coordinate `i` of `i.insertNth a y` to `b` gives
`i.insertNth b y`. Connects `ouCoord` (defined via `Function.update`)
to the `insertNth`-based Fubini lemma `integral_γFin_succAbove`. -/
theorem update_insertNth_same {n : ℕ} (i : Fin (n + 1)) (y : Fin n → ℝ)
    (a b : ℝ) :
    Function.update (Fin.insertNth (α := fun _ => ℝ) i a y) i b
      = Fin.insertNth (α := fun _ => ℝ) i b y := by
  funext j
  rcases eq_or_ne j i with h | h
  · subst h; simp
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
    rw [Function.update_of_ne (Fin.succAbove_ne i k)]
    simp

/-- `ouCoord` in `insertNth` coordinates: the single-coordinate OU on
coordinate `i`, evaluated at `i.insertNth s y`, is the 1D OU semigroup
applied to the 1D slice `r ↦ g (i.insertNth r y)`, at the point `s`. -/
theorem ouCoord_insertNth_eq {n : ℕ} (i : Fin (n + 1)) (t : ℝ)
    (g : (Fin (n + 1) → ℝ) → ℝ) (s : ℝ) (y : Fin n → ℝ) :
    ouCoord i t g (Fin.insertNth (α := fun _ => ℝ) i s y) =
      Gaussian1D.ouSemigroup t
        (fun r => g (Fin.insertNth (α := fun _ => ℝ) i r y)) s := by
  unfold ouCoord Gaussian1D.ouSemigroup
  have hi : (Fin.insertNth (α := fun _ => ℝ) i s y) i = s := by simp
  rw [hi]
  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro u
  simp only [update_insertNth_same]

/-- The multivariate Boltzmann entropy `∫ h log h dγ_n` (no
`(∫h)log(∫h)` centering — the centered form is `DirichletSpace.entropy`
under `dirichletSpaceFin`). -/
def boltzmannEntropyFin (h : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, h x * Real.log (h x) ∂γFin n

/-- Per-coordinate Fisher information `∫ (∂_i h)² / h dγ_n`. -/
def fisherInfoFinCoord (i : Fin n) (h : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ x, (partialDeriv i h x) ^ 2 / h x ∂γFin n

/-- The 1D slice of `g` along coordinate `i` (other coordinates `y`)
equals the coordinate section based at `i.insertNth 0 y`. -/
theorem slice_eq_coordSection {n : ℕ} (i : Fin (n + 1))
    (g : (Fin (n + 1) → ℝ) → ℝ) (y : Fin n → ℝ) :
    (fun r => g (Fin.insertNth (α := fun _ => ℝ) i r y)) =
      coordSection i (Fin.insertNth (α := fun _ => ℝ) i 0 y) g := by
  funext r
  unfold coordSection
  rw [update_insertNth_same i y 0 r]

/-- **Swapped Fubini split for `γFin (n+1)`.** For a bounded measurable
`h`, the integral splits as the outer integral over the `n` remaining
coordinates of the inner 1D integral over coordinate `i`. The dominating
constant makes the product integrand integrable, so the order of
`integral_γFin_succAbove` can be swapped via `integral_integral_swap`. -/
theorem integral_γFin_succAbove_swap {n : ℕ} (i : Fin (n + 1))
    {h : (Fin (n + 1) → ℝ) → ℝ} (hh_meas : Measurable h) {C : ℝ}
    (hh_bd : ∀ z, ‖h z‖ ≤ C) :
    ∫ x, h x ∂γFin (n + 1) =
      ∫ y, ∫ s, h (Fin.insertNth (α := fun _ => ℝ) i s y)
        ∂Gaussian1D.γ ∂γFin n := by
  have hh_int : Integrable h (γFin (n + 1)) := integrable_of_bound hh_meas hh_bd
  rw [integral_γFin_succAbove (n := n) (i := i) hh_int]
  -- Joint integrability of `(s, y) ↦ h (i.insertNth s y)` on `γ × γFin n`.
  set F : ℝ → (Fin n → ℝ) → ℝ :=
    fun s y => h (Fin.insertNth (α := fun _ => ℝ) i s y) with hF
  have hF_meas : Measurable (Function.uncurry F) := by
    have hcont : Continuous (fun p : ℝ × (Fin n → ℝ) =>
        Fin.insertNth (α := fun _ => ℝ) i p.1 p.2) :=
      Continuous.finInsertNth i continuous_fst continuous_snd
    have : Measurable (fun p : ℝ × (Fin n → ℝ) =>
        h (Fin.insertNth (α := fun _ => ℝ) i p.1 p.2)) :=
      hh_meas.comp hcont.measurable
    simpa [Function.uncurry, hF] using this
  have hF_int : Integrable (Function.uncurry F)
      (Gaussian1D.γ.prod (γFin n)) := by
    refine Integrable.mono' (integrable_const C)
      hF_meas.aestronglyMeasurable ?_
    filter_upwards with p
    simpa [Function.uncurry, hF] using hh_bd _
  exact MeasureTheory.integral_integral_swap hF_int

/-- **Per-coordinate Boltzmann-entropy step bound.**

For a `C^∞` function `g` with `ε ≤ g ≤ M` and coordinate-`i` partial
derivative bounded by `M`, and `t ≥ 0`,
`BE(g) - BE(ouCoord i t g) ≤ (1 - e^{-2t})/2 · I_i(g)`.

This is the 1D bound `Gaussian1D.boltzmannEntropy_ouSemigroup_decay_le`
applied to each coordinate-`i` slice and integrated over the remaining
coordinates via `integral_γFin_succAbove`. The sectionwise hypotheses
transfer through `coordSection`/`section_deriv`; the Fubini
integrability of the dominating slices follows from the uniform bounds.

**Strategy:** rewrite `BE` via `integral_γFin_succAbove i`; identify the
inner 1D integral as the 1D Boltzmann entropy of the slice `G_y` and
`ouCoord` as `Gaussian1D.ouSemigroup` of `G_y` (`ouCoord_insertNth_eq`);
apply the 1D lemma slicewise and `integral_mono` over `γ_n`; finally
identify `∫ I(G_y) dγ_n = I_i(g)` via `section_deriv`. -/
theorem boltzmannEntropyFin_ouCoord_step_le {n : ℕ} (i : Fin (n + 1))
    (g : (Fin (n + 1) → ℝ) → ℝ) (hg : ContDiff ℝ ∞ g) {ε M : ℝ}
    (hε : 0 < ε) (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hg'_bd : ∀ x, |partialDeriv i g x| ≤ M) (t : ℝ) (ht : 0 ≤ t) :
    boltzmannEntropyFin g - boltzmannEntropyFin (ouCoord i t g) ≤
      (1 - Real.exp (-2 * t)) / 2 * fisherInfoFinCoord i g := by
  classical
  have hε_nn : (0 : ℝ) ≤ ε := hε.le
  have hεM : ε ≤ M := le_trans (hg_lo (fun _ => 0)) (hg_hi (fun _ => 0))
  have hM_pos : 0 < M := lt_of_lt_of_le hε hεM
  -- The coordinate-`i` slice and its packaged 1D facts.
  set G : (Fin n → ℝ) → ℝ → ℝ :=
    fun y r => g (Fin.insertNth (α := fun _ => ℝ) i r y) with hG
  have hG_eq : ∀ y, G y = coordSection i (Fin.insertNth (α := fun _ => ℝ) i 0 y) g :=
    fun y => slice_eq_coordSection i g y
  have hG_C1 : ∀ y, ContDiff ℝ 1 (G y) := by
    intro y
    rw [hG_eq y]
    exact (section_contDiff hg i _).of_le (by simp)
  have hG_lo : ∀ y r, ε ≤ G y r := fun y r => hg_lo _
  have hG_hi : ∀ y r, G y r ≤ M := fun y r => hg_hi _
  have hG_deriv : ∀ y, deriv (G y) =
      fun r => partialDeriv i g (Fin.insertNth (α := fun _ => ℝ) i r y) := by
    intro y
    rw [hG_eq y, section_deriv hg i _]
    funext r
    rw [update_insertNth_same i y 0 r]
  have hG'_bd : ∀ y r, |deriv (G y) r| ≤ M := by
    intro y r
    rw [hG_deriv y]
    exact hg'_bd _
  -- 1D entropy-decay bound applied to each slice.
  have h1D : ∀ y, Gaussian1D.boltzmannEntropy (G y) -
      Gaussian1D.boltzmannEntropy (Gaussian1D.ouSemigroup t (G y)) ≤
      (1 - Real.exp (-2 * t)) / 2 * Gaussian1D.fisherInfo (G y) := fun y =>
    Gaussian1D.boltzmannEntropy_ouSemigroup_decay_le (G y) (hG_C1 y) hε
      (hG_lo y) (hG_hi y) (hG'_bd y) t ht
  have hg_meas : Measurable g := hg.continuous.measurable
  -- Uniform `|s log s|` bound on `[0, M]` (covers the slice ranges).
  obtain ⟨B, hB_nn, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧
      ∀ s ∈ Set.Icc (0 : ℝ) M, |s * Real.log s| ≤ B := by
    have h_compact : IsCompact (Set.Icc (0 : ℝ) M) := isCompact_Icc
    have h_cont_abs : Continuous (fun s => |s * Real.log s|) :=
      Real.continuous_mul_log.abs
    obtain ⟨B, hB⟩ := (h_compact.image h_cont_abs).bddAbove
    exact ⟨max B 0, le_max_right _ _, fun s hs =>
      (hB ⟨s, hs, rfl⟩).trans (le_max_left _ _)⟩
  -- (1) `boltzmannEntropyFin g = ∫_y boltzmannEntropy (G y) dγ_n`.
  have hBE_g : boltzmannEntropyFin g =
      ∫ y, Gaussian1D.boltzmannEntropy (G y) ∂γFin n := by
    unfold boltzmannEntropyFin Gaussian1D.boltzmannEntropy
    rw [integral_γFin_succAbove_swap (n := n) (i := i)
      (h := fun x => g x * Real.log (g x))
      (hg_meas.mul (Real.measurable_log.comp hg_meas)) (C := B)
      (fun z => by
        rw [Real.norm_eq_abs]
        exact hB _ ⟨le_trans hε_nn (hg_lo z), hg_hi z⟩)]
  -- The 1D slice OU is bounded by `M` (1D OU of a function ≤ M).
  have hPG_bd : ∀ y s, ε ≤ Gaussian1D.ouSemigroup t (G y) s ∧
      Gaussian1D.ouSemigroup t (G y) s ≤ M := by
    intro y s
    have hGy_int : Integrable
        (fun u => G y (Real.exp (-t) * s +
          Real.sqrt (1 - Real.exp (-2 * t)) * u)) Gaussian1D.γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (((hG_C1 y).continuous).measurable.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with u
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨le_trans (by linarith [hε_nn]) (le_of_lt (lt_of_lt_of_le hε (hG_lo y _))),
          (hG_hi y _)⟩
    constructor
    · show ε ≤ ∫ u, G y (Real.exp (-t) * s +
        Real.sqrt (1 - Real.exp (-2 * t)) * u) ∂Gaussian1D.γ
      calc ε = ∫ _u, ε ∂Gaussian1D.γ := by simp
        _ ≤ _ := integral_mono (integrable_const ε) hGy_int (fun u => hG_lo y _)
    · show ∫ u, G y (Real.exp (-t) * s +
        Real.sqrt (1 - Real.exp (-2 * t)) * u) ∂Gaussian1D.γ ≤ M
      calc ∫ u, _ ∂Gaussian1D.γ
          ≤ ∫ _u, M ∂Gaussian1D.γ :=
            integral_mono hGy_int (integrable_const M) (fun u => hG_hi y _)
        _ = M := by simp
  -- (2) `boltzmannEntropyFin (ouCoord i t g) = ∫_y BE(P_t (G y)) dγ_n`.
  have h_ouCoord_meas : Measurable (ouCoord i t g) := by
    have hupd : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
        Function.update p.1 i (Real.exp (-t) * p.1 i +
          Real.sqrt (1 - Real.exp (-2 * t)) * p.2)) := by
      have hval : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
          Real.exp (-t) * p.1 i +
            Real.sqrt (1 - Real.exp (-2 * t)) * p.2) :=
        (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).add
          (measurable_const.mul measurable_snd)
      exact measurable_update'.comp (measurable_fst.prodMk hval)
    have hjoint : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
        g (Function.update p.1 i (Real.exp (-t) * p.1 i +
          Real.sqrt (1 - Real.exp (-2 * t)) * p.2))) := hg_meas.comp hupd
    exact (hjoint.stronglyMeasurable.integral_prod_right').measurable
  have hBE_ouCoord : boltzmannEntropyFin (ouCoord i t g) =
      ∫ y, Gaussian1D.boltzmannEntropy
        (Gaussian1D.ouSemigroup t (G y)) ∂γFin n := by
    unfold boltzmannEntropyFin Gaussian1D.boltzmannEntropy
    rw [integral_γFin_succAbove_swap (n := n) (i := i)
      (h := fun x => ouCoord i t g x * Real.log (ouCoord i t g x))
      (h_ouCoord_meas.mul (Real.measurable_log.comp h_ouCoord_meas)) (C := B)
      (fun z => by
        rw [Real.norm_eq_abs]
        -- `ouCoord` is itself a 1D OU of a slice, so bounded in `[ε, M]`.
        have hval : ouCoord i t g z =
            Gaussian1D.ouSemigroup t
              (fun r => g (Fin.insertNth (α := fun _ => ℝ) i r
                (Fin.removeNth i z))) (z i) := by
          have hz : z = Fin.insertNth (α := fun _ => ℝ) i (z i)
              (Fin.removeNth i z) := (Fin.insertNth_self_removeNth i z).symm
          conv_lhs => rw [hz]
          rw [ouCoord_insertNth_eq i t g (z i) (Fin.removeNth i z)]
        simp only []
        rw [hval]
        have hb := hPG_bd (Fin.removeNth i z) (z i)
        rw [hG] at hb
        exact hB _ ⟨le_trans hε_nn hb.1, hb.2⟩)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    simp only [hG, ouCoord_insertNth_eq i t g s y]
  sorry

/-- **Macroscopic-term cancellation.** For an `IsCoreFin` test function
`f`, the centered entropy difference of `g = f²` and `P_t g` equals
their Boltzmann-entropy difference, because the multivariate OU
semigroup preserves the Gaussian mean
(`ouSemigroupFin_integral_eq_of_bound`), so the two `(∫·)log(∫·)`
terms are identical and cancel in the difference.

This is the only place the macroscopic terms enter, and it requires no
derivatives — pure mean preservation plus linearity. -/
theorem entropy_sub_eq_boltzmann_sub {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (t : ℝ) (ht : 0 ≤ t) (hf : IsCoreFin f) :
    DirichletSpace.entropy (ds := dirichletSpaceFin (n := n)) (fun x => f x * f x) -
        DirichletSpace.entropy (ds := dirichletSpaceFin (n := n))
          (ouSemigroupFin t (fun x => f x * f x)) =
      boltzmannEntropyFin (fun x => f x * f x) -
        boltzmannEntropyFin (ouSemigroupFin t (fun x => f x * f x)) := by
  obtain ⟨M, hM⟩ := hf.bound_exists
  have hM_nn : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
  set g : (Fin n → ℝ) → ℝ := fun x => f x * f x with hg_def
  have hg_meas : Measurable g := (hf.measurable.mul hf.measurable)
  have hg_bd : ∀ x, ‖g x‖ ≤ M ^ 2 := by
    intro x
    have hfx : |f x| ≤ M := by rw [← Real.norm_eq_abs]; exact hM x
    have hgx : g x = f x * f x := rfl
    have hnn : 0 ≤ g x := by rw [hgx]; exact mul_self_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, hgx]
    nlinarith [abs_nonneg (f x), sq_abs (f x)]
  -- Mean preservation: ∫ P_t g dγ = ∫ g dγ.
  have h_mean : ∫ x, ouSemigroupFin t g x ∂γFin n = ∫ x, g x ∂γFin n :=
    ouSemigroupFin_integral_eq_of_bound (n := n) (M := M ^ 2) t ht hg_meas hg_bd
  -- Unfold the centered entropy and cancel the equal macroscopic terms.
  unfold DirichletSpace.entropy boltzmannEntropyFin
  show
    ((∫ x, g x * Real.log (g x) ∂γFin n) -
        (∫ x, g x ∂γFin n) * Real.log (∫ x, g x ∂γFin n)) -
      ((∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n) -
        (∫ x, ouSemigroupFin t g x ∂γFin n) *
          Real.log (∫ x, ouSemigroupFin t g x ∂γFin n)) =
    (∫ x, g x * Real.log (g x) ∂γFin n) -
      (∫ x, ouSemigroupFin t g x * Real.log (ouSemigroupFin t g x) ∂γFin n)
  rw [h_mean]
  ring

/-- **Integrated multivariate entropy decay for `f²` (BGL Thm. 5.5.2,
n-dim Gaussian case).**

For every `IsCoreFin` test function `f` and every `t ≥ 0`,
`Ent(f²) - Ent(P_t(f²)) ≤ (1 - e^{-2t}) * 2 * E_n(f,f)`.

This is the finite-dimensional Gaussian tensor lift of the proved 1D
theorem `Gaussian1D.ouSemigroup_entropy_sq_decay_bound_proved`, obtained
via the telescoping route documented above.

**Reference:** Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov
Diffusion Operators*, Springer 2014, §5.5, Theorem 5.5.2. -/
theorem ouSemigroupFin_entropy_sq_decay_bound {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (t : ℝ) (ht : 0 ≤ t) (hf : IsCoreFin f) :
    DirichletSpace.entropy (ds := dirichletSpaceFin (n := n)) (fun x => f x * f x) -
      DirichletSpace.entropy (ds := dirichletSpaceFin (n := n))
        (ouSemigroupFin t (fun x => f x * f x)) ≤
      (1 - Real.exp (-2 * 1 * t)) * (2 / 1) * ouEnergyFin f f := by
  -- Step 1 (proved): reduce the centered entropy difference to the
  -- Boltzmann difference via macroscopic-term cancellation.
  rw [entropy_sub_eq_boltzmann_sub f t ht hf]
  -- Remaining: the Boltzmann telescoping bound.
  -- `boltzmannEntropyFin (f²) - boltzmannEntropyFin (P_t f²)`
  --   ≤ 2 (1 - e^{-2t}) · ouEnergyFin f f.
  -- Telescope over per-coordinate `ouCoord` factors of `ouSemigroupFin`,
  -- bound each step by the 1D `boltzmannEntropy_ouSemigroup_decay_le`,
  -- and control the per-coordinate Fisher informations by
  -- `4 · ouEnergyFin f f` via orthogonal Fisher monotonicity.
  sorry

end GaussianFin
