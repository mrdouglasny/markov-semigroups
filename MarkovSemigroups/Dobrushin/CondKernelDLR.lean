/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# CondKernel DLR Inheritance

## Overview

For a Gibbs measure μ on `SpinConfig I S`, the condKernel fiber measure
(from disintegrating μ via `piEquivPiSubtypeProd (· ∈ N_f)`) satisfies
DLR at sites z ∉ N_f, for a.e. N_f-marginal value b.

## Main result

- `condKernel_ae_bound`: for a.e. b, the conditional expectation of g
  on the condKernel fiber differs from E[g] by at most
  `2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x`.

## Strategy

1. Define the fiber measure `mu_b := (ρ.condKernel b).map (fun ω => e.symm (b, ω))`.
2. Show `mu_b` is a probability measure for a.e. b (from IsMarkovKernel).
3. Prove `mu_b` satisfies DLR at z ∉ N_f for a.e. b (sorry: requires
   pushing the Gibbs DLR equation through the disintegration).
4. Apply coupling + Neumann iteration on `mu_b` vs μ.
5. Rewrite in condKernel terms → the a.e. bound.

## Sorry inventory

- `fiberMeasure_dlr_ae`: the condKernel fiber measure satisfies DLR at
  sites z ∉ N_f, for a.e. b. This is the core measure-theoretic fact,
  following from pushing the Gibbs DLR through the disintegration identity
  `ρ = ρ.fst ⊗ₘ ρ.condKernel` and the fact that DLR at z ∉ N_f involves
  only complement-coordinate conditioning.

## References

- Georgii (1988), §8 (DLR equations and conditioning)
- Dobrushin (1968), uniqueness via influence matrix
-/

import MarkovSemigroups.Dobrushin.CovarianceBoundMultisite
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Metrizable.CompletelyMetrizable

open MeasureTheory ProbabilityTheory CovarianceBoundMultisite Topology Filter Set
  TopologicalSpace

noncomputable section

namespace CondKernelDLR

variable {I : Type*} [DecidableEq I] [Fintype I]
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]
    [Inhabited S]

/-! ## Setup: the product decomposition -/

/-- The product decomposition of `SpinConfig I S` via the N_f partition. -/
private abbrev prodEquiv (N_f : Finset I) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => S) (fun i => i ∈ N_f)

/-- Standard Borel Space instance for compact spin spaces. -/
private instance standardBorel_S : StandardBorelSpace S := by
  haveI : MetrizableSpace S := inferInstance
  letI := metrizableSpaceMetric S; exact inferInstance

/-! ## Fiber measure construction -/

/-- The fiber measure at b, lifted back to SpinConfig I S.
For a.e. b, this is a probability measure representing the conditional
distribution of μ given that the N_f-coordinates equal b. -/
def fiberMeasure (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (N_f : Finset I) (b : {i // i ∈ N_f} → S) : Measure (SpinConfig I S) :=
  let e := prodEquiv N_f
  let ρ := μ.map e
  haveI : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  (ρ.condKernel b).map (fun ω => e.symm (b, ω))

set_option linter.unusedSectionVars false in
/-- The map `ω ↦ e.symm (b, ω)` is measurable. -/
private lemma measurable_fiberLift (N_f : Finset I) (b : {i // i ∈ N_f} → S) :
    Measurable (fun ω : {i // i ∉ N_f} → S => (prodEquiv N_f).symm (b, ω)) :=
  (prodEquiv N_f).symm.measurable.comp (Measurable.prodMk measurable_const measurable_id)

/-- The fiber measure is a probability measure for every b. -/
lemma fiberMeasure_isProbabilityMeasure
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (N_f : Finset I)
    (b : {i // i ∈ N_f} → S) :
    IsProbabilityMeasure (fiberMeasure μ N_f b) := by
  simp only [fiberMeasure]
  have he : IsProbabilityMeasure (μ.map (prodEquiv N_f)) :=
    Measure.isProbabilityMeasure_map (prodEquiv N_f).measurable.aemeasurable
  have : IsMarkovKernel (μ.map (prodEquiv N_f)).condKernel := inferInstance
  have : IsProbabilityMeasure ((μ.map (prodEquiv N_f)).condKernel b) :=
    IsMarkovKernel.isProbabilityMeasure b
  exact Measure.isProbabilityMeasure_map (measurable_fiberLift N_f b).aemeasurable

/-- The integral of g against `fiberMeasure` equals the condKernel integral.
This is definitional, but useful as a rewrite lemma. -/
lemma integral_fiberMeasure_eq
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (N_f : Finset I)
    (b : {i // i ∈ N_f} → S)
    (g : SpinConfig I S → ℝ) (hg_meas : Measurable g) :
    ∫ σ, g σ ∂fiberMeasure μ N_f b =
    ∫ ω, g ((prodEquiv N_f).symm (b, ω)) ∂(μ.map (prodEquiv N_f)).condKernel b := by
  unfold fiberMeasure
  rw [integral_map (measurable_fiberLift N_f b).aemeasurable
    hg_meas.aestronglyMeasurable]

/-! ## Core sorry: DLR for the fiber measure

The fiber measure `mu_b = fiberMeasure μ N_f b` satisfies DLR at every
z ∉ N_f, for a.e. b. This is the key measure-theoretic step.

Proof sketch (not formalized):
1. μ satisfies DLR: for all measurable A and all z,
   `μ(A) = ∫ γ.condDist{z} σ A dμ(σ)`.
2. Apply the disintegration ρ = ρ.fst ⊗ₘ ρ.condKernel to both sides.
3. By `integral_condKernel`, both sides decompose as
   `∫_b ∫_ω ... d(condKernel b) d(fst)`.
4. For a.e. b, the inner integrals must agree (by uniqueness of
   conditional expectations). Since the DLR identity holds for all
   measurable A, we get: for a.e. b and all A,
   `mu_b(A) = ∫ γ.condDist{z} σ A d(mu_b)(σ)`.
5. The "for all A" upgrade uses `CountablyGenerated` (Standard Borel). -/

/-- **DLR for the fiber measure at z ∉ N_f.**

For a.e. b, the fiber measure satisfies the DLR equation at {z} for
every z ∉ N_f and every measurable set A.

**Proof (sketch).**
Fix z ∉ N_f and a measurable set A. The DLR equation for μ says:
  `(μ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ`

Transport both sides through `e` using `Measure.integral_condKernel`:
  LHS = `∫_b (fiberMeasure b A).toReal d(ρ.fst)`
  RHS = `∫_b [∫ σ, (γ.condDist {z} σ A).toReal d(fiberMeasure b)] d(ρ.fst)`

Since both outer integrals agree and the integrands are measurable,
by uniqueness of conditional expectations (for each fixed A and z):
  for a.e. b: `(fiberMeasure b A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal d(fiberMeasure b)`

The "for all A" upgrade uses `CountablyGenerated` (from `StandardBorelSpace`)
to get a countable pi-system generating the sigma-algebra, then takes a
countable intersection of full-measure sets.

The "for all z ∉ N_f" upgrade is trivial since I is finite (Fintype). -/
lemma fiberMeasure_dlr_ae
    (γ : GibbsSpec I S)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (N_f : Finset I) :
    let e := prodEquiv N_f
    let ρ := μ.map e
    ∀ᵐ b ∂ρ.fst,
      ∀ z, z ∉ N_f →
        ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
          (fiberMeasure μ N_f b A).toReal =
            ∫ σ, (γ.condDist {z} σ A).toReal ∂fiberMeasure μ N_f b := by
  sorry

/-- Bounded measurable functions are integrable against probability measures. -/
private lemma integrable_of_bounded_measurable
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (g : α → ℝ) (hg_meas : Measurable g)
    (Bg : ℝ) (hBg : ∀ σ, |g σ| ≤ Bg) :
    Integrable g μ :=
  Integrable.of_bound hg_meas.aestronglyMeasurable Bg
    (ae_of_all μ (fun x => (Real.norm_eq_abs (g x)).symm ▸ hBg x))

/-! ## The main theorem: condKernel a.e. bound -/

set_option maxHeartbeats 1200000 in
/-- **CondKernel a.e. bound.**

For a Gibbs measure μ and an N_g-local observable g bounded by Bg,
for a.e. N_f-marginal value b:
  `|∫ ω, g(e.symm(b,ω)) d(condKernel b) - ∫ g dμ| ≤
    2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x`

This is the key hypothesis needed for
`covariance_bound_gibbs_multisite_general_nocount` and the
`CondKernelAEBound` type used in the LGT `MassGap3D.lean`. -/
theorem condKernel_ae_bound
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (g : SpinConfig I S → ℝ) (hg_meas : Measurable g)
    (Bg : ℝ) (hBg_nn : 0 ≤ Bg) (hBg : ∀ σ, |g σ| ≤ Bg)
    (N_f N_g : Finset I)
    (hg_local : ∀ σ τ : SpinConfig I S,
      (∀ w ∈ N_g, σ w = τ w) → g σ = g τ)
    (hg_int : Integrable g μ)
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    let e := prodEquiv N_f
    let ρ := μ.map e
    ∀ᵐ b ∂ρ.fst,
      |(∫ ω, g (e.symm (b, ω)) ∂ρ.condKernel b) - ∫ σ, g σ ∂μ| ≤
        2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by
  intro e ρ
  -- Step 1: Get the a.e. DLR property for fiber measures
  have h_dlr := fiberMeasure_dlr_ae γ μ hμ N_f
  -- Step 2: For each b where DLR holds, bound via coupling
  -- Use filter_upwards with h_dlr
  filter_upwards [h_dlr] with b hb_dlr
  -- Rewrite LHS using integral_fiberMeasure_eq
  rw [← integral_fiberMeasure_eq μ N_f b g hg_meas]
  -- Now bound |∫ g d(fiberMeasure) - ∫ g dμ|
  set mu_b := fiberMeasure μ N_f b
  haveI : IsProbabilityMeasure mu_b := fiberMeasure_isProbabilityMeasure μ N_f b
  -- Set up the coupling argument
  set T : Set I := {z | z ∉ N_f}
  -- DLR for mu_b at z ∉ N_f
  have hdlr₁ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (mu_b A).toReal =
        ∫ σ, (γ.condDist {z} σ A).toReal ∂mu_b := by
    intro z hzT A hA
    exact hb_dlr z hzT A hA
  -- DLR for μ at z ∉ N_f (from Gibbs property)
  have hdlr₂ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (μ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ := by
    intro z _ A hA; exact hμ.dlr {z} A hA
  -- Get the coupling
  obtain ⟨P, hP_coup, hP_ineq⟩ :=
    dobrushin_iterated_coupling_exists_compact γ mu_b μ T
      hdlr₁ hdlr₂ hfinsupp h_dep_F
  haveI := hP_coup.isProb
  -- Disagreement probabilities
  set δ : I → ℝ :=
    fun w => (P {p : SpinConfig I S × SpinConfig I S | p.1 w ≠ p.2 w}).toReal
  have hδ_nn : ∀ w, 0 ≤ δ w := fun _ => ENNReal.toReal_nonneg
  have hδ_le_one : ∀ w, δ w ≤ 1 := by
    intro w
    calc (P {p : SpinConfig I S × SpinConfig I S | p.1 w ≠ p.2 w}).toReal
        ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) (prob_le_one)
      _ = 1 := by simp
  have hcontract : ∀ z, z ∉ N_f → δ z ≤ ∑' w, influenceCoeff γ z w * δ w :=
    fun z hzN => hP_ineq z hzN
  -- Neumann iteration
  have hδ_le_neu : ∀ y, δ y ≤ ∑ x ∈ N_f, neumannSeriesCoeff γ y x := fun y =>
    abstract_neumann_iteration_finset γ hD N_f δ hδ_nn hδ_le_one hcontract y
  have h_sum_le : ∑ y ∈ N_g, δ y ≤
      ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x :=
    Finset.sum_le_sum (fun y _ => hδ_le_neu y)
  haveI : MeasurableEq S := inferInstance
  -- Integrability of g on mu_b and μ
  have hg_mu_b_int : Integrable g mu_b :=
    integrable_of_bounded_measurable mu_b g hg_meas Bg hBg
  -- Coupling-based integral bound
  have h_int_bound :
      |∫ σ, g σ ∂mu_b - ∫ σ, g σ ∂μ| ≤ 2 * Bg * ∑ y ∈ N_g, δ y :=
    local_integral_sub_le_coupling_Ng mu_b μ P hP_coup
      g hg_meas Bg hBg_nn hBg
      hg_mu_b_int hg_int N_g hg_local
  calc |∫ σ, g σ ∂mu_b - ∫ σ, g σ ∂μ|
      ≤ 2 * Bg * ∑ y ∈ N_g, δ y := h_int_bound
    _ ≤ 2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x :=
        mul_le_mul_of_nonneg_left h_sum_le (by positivity)

end CondKernelDLR
