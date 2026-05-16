/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ouGeneratorFin` as an `L²(γFin n)` element (G2/G4 base)

Shared prerequisite for the `GeneratorCompat` discharge
(`plans/gross-discharge.md`, G2/G4): the named OU generator
`ouGeneratorFin f = Δf − x·∇f` (from `EuclideanGenerator`) is
square-integrable against the standard multivariate Gaussian for core
`f`, hence defines an element of `Lp ℝ 2 (γFin n)`.

Split out so the strong-`L²` limit (`EuclideanGeneratorLimit`) and the
γ-IBP / assembly (`EuclideanGeneratorCompat`) can be developed in
parallel against a common base.
-/

import MarkovSemigroups.Instances.WorkInProgress.EuclideanFinLp
import MarkovSemigroups.Instances.WorkInProgress.EuclideanGenerator

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace GaussianFin

variable {n : ℕ}

/-- `ouGeneratorFin f = Δf − x·∇f ∈ L²(γFin n)` for core `f`.

Strategy: `IsCoreFin` gives `f` `ContDiff ℝ ∞` with uniformly bounded
first/second partials, so `∑ᵢ ∂ᵢ²f` is bounded and `∑ᵢ xᵢ ∂ᵢf` has at
most linear growth in `x`; both are square-integrable against the
standard Gaussian `γFin n` (bounded part via `memLp_two_of_bound`;
linear-growth part via Gaussian polynomial moments). -/
theorem memLp_ouGeneratorFin {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    MemLp (ouGeneratorFin f) 2 (γFin n) := by
  obtain ⟨hcd, M, hM⟩ := hf
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) ((hM (fun _ => 0)).1)
  have hcoreF : IsCoreFin f := ⟨hcd, M, hM⟩
  -- Each Gaussian coordinate is in `L²`.
  have hcoord : ∀ i : Fin n, MemLp (fun x : Fin n → ℝ => x i) 2 (γFin n) := by
    intro i
    have heval : MeasurePreserving (Function.eval i) (γFin n) Gaussian1D.γ := by
      simpa [γFin] using
        (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => Gaussian1D.γ) i)
    have hid : MemLp (id : ℝ → ℝ) (2 : ℝ≥0∞) Gaussian1D.γ := by
      have h := memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (2 : ℝ≥0)
      have hcoe : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := by norm_num
      simpa [Gaussian1D.γ, hcoe] using h
    have hcomp := hid.comp_measurePreserving heval
    simpa [Function.comp] using hcomp
  -- Diffusion part `∑ᵢ ∂ᵢ²f` (function-valued Finset sum): bounded ⇒ `L²`.
  have hA : MemLp (∑ i : Fin n, secondPartial i f) 2 (γFin n) := by
    have hsm : StronglyMeasurable (∑ i : Fin n, secondPartial i f) :=
      Finset.stronglyMeasurable_sum _ (fun i _ =>
        (hcoreF.secondPartial_continuous i).stronglyMeasurable)
    refine (memLp_const ((n : ℝ) * M)).mono hsm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_))
    have hnM : (0 : ℝ) ≤ (n : ℝ) * M := by positivity
    have hb : |∑ i : Fin n, secondPartial i f x| ≤ (n : ℝ) * M := by
      calc |∑ i : Fin n, secondPartial i f x|
          ≤ ∑ i : Fin n, |secondPartial i f x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, M := Finset.sum_le_sum
            (fun i _ => by simpa [Real.norm_eq_abs] using (hM x).2.2 i)
        _ = (n : ℝ) * M := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [Finset.sum_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg hnM]
    exact hb
  -- Drift part `∑ᵢ xᵢ ∂ᵢf`: each term is (Gaussian coordinate)·(bounded) ∈ `L²`.
  have hB : MemLp
      (∑ i : Fin n, fun x : Fin n → ℝ => x i * partialDeriv i f x) 2 (γFin n) := by
    refine memLp_finset_sum' _ (fun i _ => ?_)
    have hsm : AEStronglyMeasurable
        (fun x : Fin n → ℝ => x i * partialDeriv i f x) (γFin n) :=
      (((measurable_pi_apply i).stronglyMeasurable).mul
        (hcoreF.partial_continuous i).stronglyMeasurable).aestronglyMeasurable
    refine ((hcoord i).const_mul M).mono hsm
      (Filter.Eventually.of_forall (fun x => ?_))
    have hpm : ‖partialDeriv i f x‖ ≤ M := (hM x).2.1 i
    calc ‖x i * partialDeriv i f x‖
        = ‖x i‖ * ‖partialDeriv i f x‖ := by rw [norm_mul]
      _ ≤ ‖x i‖ * M :=
          mul_le_mul_of_nonneg_left hpm (norm_nonneg _)
      _ = ‖M * x i‖ := by
          rw [norm_mul, Real.norm_eq_abs M, abs_of_nonneg hM0, mul_comm]
  have hougen : ouGeneratorFin f =
      (∑ i : Fin n, secondPartial i f)
        - (∑ i : Fin n, fun x : Fin n → ℝ => x i * partialDeriv i f x) := by
    funext x
    simp [ouGeneratorFin_apply, Finset.sum_apply, Pi.sub_apply]
  rw [hougen]
  exact hA.sub hB

/-- The `L²(γFin n)` element represented by `ouGeneratorFin f`
(`= Δf − x·∇f`), for core `f`. -/
def ouGeneratorFinLp {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    Lp ℝ 2 (γFin n) :=
  (memLp_ouGeneratorFin hf).toLp (ouGeneratorFin f)

end GaussianFin

end
