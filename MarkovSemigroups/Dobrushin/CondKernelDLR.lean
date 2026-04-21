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

/-! ### Helper: fiberMeasure equals condKernel composed with e.symm -/

/-- The fiber set: for a set `A` of spin configs and a base point `b`,
the set of ω such that `e.symm (b, ω) ∈ A`. -/
private def fiberSet (N_f : Finset I) (b : {i // i ∈ N_f} → S)
    (A : Set (SpinConfig I S)) : Set ({i // i ∉ N_f} → S) :=
  {ω | (prodEquiv N_f).symm (b, ω) ∈ A}

private lemma measurableSet_fiberSet (N_f : Finset I) (b : {i // i ∈ N_f} → S)
    {A : Set (SpinConfig I S)} (hA : MeasurableSet A) :
    MeasurableSet (fiberSet N_f b A) := by
  unfold fiberSet
  exact hA.preimage (measurable_fiberLift N_f b)

private lemma fiberMeasure_eq_condKernel_fiberSet
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (N_f : Finset I) (b : {i // i ∈ N_f} → S)
    (A : Set (SpinConfig I S)) (hA : MeasurableSet A) :
    fiberMeasure μ N_f b A = (μ.map (prodEquiv N_f)).condKernel b (fiberSet N_f b A) := by
  unfold fiberMeasure fiberSet
  rw [Measure.map_apply (measurable_fiberLift N_f b) hA]; congr 1

/-! ### Step 1: For fixed A and z, establish equality of integrals over ρ.fst -/

/-- The fiberSet does not depend on b: it equals the section of e '' A. -/
private lemma fiberSet_eq_section (N_f : Finset I) (b : {i // i ∈ N_f} → S)
    (A : Set (SpinConfig I S)) :
    fiberSet N_f b A = Prod.mk b ⁻¹' ((prodEquiv N_f) '' A) := by
  ext ω
  simp only [fiberSet, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image]
  constructor
  · intro h
    exact ⟨(prodEquiv N_f).symm (b, ω), h, (prodEquiv N_f).apply_symm_apply (b, ω)⟩
  · intro ⟨σ, hσA, hσ⟩
    rwa [show (prodEquiv N_f).symm (b, ω) = σ from
      by rw [← hσ, (prodEquiv N_f).symm_apply_apply]]

/-- The LHS integral: ∫⁻ b, fiberMeasure b A ∂ρ.fst = μ A -/
private lemma lintegral_fiberMeasure_eq_measure
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (N_f : Finset I) {A : Set (SpinConfig I S)} (hA : MeasurableSet A) :
    ∫⁻ b, fiberMeasure μ N_f b A ∂(μ.map (prodEquiv N_f)).fst = μ A := by
  -- Rewrite fiberMeasure as condKernel applied to sections of e '' A
  have h_eq : ∀ b, fiberMeasure μ N_f b A =
      (μ.map (prodEquiv N_f)).condKernel b
        (Prod.mk b ⁻¹' ((prodEquiv N_f) '' A)) := by
    intro b
    rw [fiberMeasure_eq_condKernel_fiberSet _ _ _ _ hA, fiberSet_eq_section]
  simp_rw [h_eq]
  -- Apply lintegral_condKernel_mem
  have hA' : MeasurableSet ((prodEquiv N_f) '' A) :=
    (prodEquiv N_f).measurableSet_image.mpr hA
  -- {ω | (b, ω) ∈ e '' A} = Prod.mk b ⁻¹' (e '' A) definitionally
  convert Measure.lintegral_condKernel_mem hA' using 1
  -- ρ (e '' A) = μ A
  rw [Measure.map_apply (prodEquiv N_f).measurable hA']
  congr 1
  exact ((prodEquiv N_f).preimage_image A).symm

/-- The RHS integral after disintegration -/
private lemma integral_condDist_fiberMeasure_eq
    (γ : GibbsSpec I S) (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (N_f : Finset I) (z : I) {A : Set (SpinConfig I S)} (hA : MeasurableSet A) :
    ∫ b, (∫ σ, (γ.condDist {z} σ A).toReal ∂fiberMeasure μ N_f b) ∂(μ.map (prodEquiv N_f)).fst =
    (μ A).toReal := by
  -- Start from DLR: (μ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ
  rw [hμ.dlr {z} A hA]
  -- Transport through e: ∫ σ, f σ ∂μ = ∫ (b,ω), f(e.symm(b,ω)) ∂ρ
  -- Then apply integral_condKernel
  have h_meas_cd := (γ.measurable_condDist {z} A hA).comp (prodEquiv N_f).symm.measurable
  have h_transport : ∫ σ, (γ.condDist {z} σ A).toReal ∂μ =
      ∫ x, (γ.condDist {z} ((prodEquiv N_f).symm x) A).toReal ∂(μ.map (prodEquiv N_f)) := by
    conv_rhs => rw [integral_map_equiv (prodEquiv N_f)]
    congr 1; ext σ; simp
  rw [h_transport]
  -- Apply integral_condKernel
  have h_int : Integrable (fun x => (γ.condDist {z} ((prodEquiv N_f).symm x) A).toReal)
      (μ.map (prodEquiv N_f)) := by
    apply Integrable.of_bound (C := 1) h_meas_cd.aestronglyMeasurable
    apply ae_of_all; intro x
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  rw [(Measure.integral_condKernel h_int).symm]
  -- Now the inner integral ∫ ω, f(e.symm(b,ω)) d(condKernel b) equals
  -- ∫ σ, f σ d(fiberMeasure b)
  congr 1; ext b
  rw [← integral_fiberMeasure_eq μ N_f b _ (γ.measurable_condDist {z} A hA)]

/-- b ↦ fiberMeasure μ N_f b A is measurable (as ENNReal). -/
private lemma measurable_fiberMeasure_apply
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (N_f : Finset I) {A : Set (SpinConfig I S)} (hA : MeasurableSet A) :
    Measurable (fun b => fiberMeasure μ N_f b A) := by
  have h_eq : (fun b => fiberMeasure μ N_f b A) =
      (fun b => (μ.map (prodEquiv N_f)).condKernel b
        (Prod.mk b ⁻¹' ((prodEquiv N_f) '' A))) := by
    ext b; rw [fiberMeasure_eq_condKernel_fiberSet _ _ _ _ hA, fiberSet_eq_section]
  rw [h_eq]
  exact Kernel.measurable_kernel_prodMk_left ((prodEquiv N_f).measurableSet_image.mpr hA)

/-- For fixed A and z, the two functions are equal as ρ.fst-integrals. -/
private lemma integral_fiberMeasure_toReal_eq_integral_condDist
    (γ : GibbsSpec I S) (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (N_f : Finset I) (z : I) {A : Set (SpinConfig I S)} (hA : MeasurableSet A) :
    ∫ b, (fiberMeasure μ N_f b A).toReal ∂(μ.map (prodEquiv N_f)).fst =
    ∫ b, (∫ σ, (γ.condDist {z} σ A).toReal ∂fiberMeasure μ N_f b) ∂(μ.map (prodEquiv N_f)).fst := by
  -- Both equal (μ A).toReal
  rw [integral_condDist_fiberMeasure_eq γ μ hμ N_f z hA]
  -- Need: ∫ b, (fiberMeasure b A).toReal ∂ρ.fst = (μ A).toReal
  -- From lintegral_fiberMeasure_eq_measure, we have the ENNReal version
  have h_ennreal := lintegral_fiberMeasure_eq_measure μ N_f hA
  -- Since fiberMeasure b A ≤ 1 for all b (prob measure), toReal is well-behaved
  have h_lt_top : ∀ b, fiberMeasure μ N_f b A < ⊤ := by
    intro b
    haveI := fiberMeasure_isProbabilityMeasure μ N_f b
    exact lt_of_le_of_lt prob_le_one ENNReal.one_lt_top
  -- Convert lintegral to integral via integral_toReal
  rw [integral_toReal (measurable_fiberMeasure_apply μ N_f hA).aemeasurable
    (ae_of_all _ h_lt_top)]
  rw [h_ennreal]

/-- For z ∉ N_f, the condDist at {z} preserves the N_f-coordinates:
condDist-a.e., the configuration agrees with σ on N_f. -/
private lemma condDist_preserves_base
    (γ : GibbsSpec I S) (N_f : Finset I) (z : I) (hz : z ∉ N_f)
    (σ : SpinConfig I S) (B : Set (SpinConfig I S))
    (hB : B ⊆ {τ | ∀ i ∈ N_f, τ i = σ i}) :
    γ.condDist {z} σ B = γ.condDist {z} σ (B ∩ {τ | ∀ x, x ∉ ({z} : Finset I) → τ x = σ x}) := by
  have hproper := γ.proper {z} σ
  set Agree := {τ : SpinConfig I S | ∀ x, x ∉ ({z} : Finset I) → τ x = σ x}
  -- condDist is concentrated on Agree (measure = 1)
  -- So Agreeᶜ has measure 0 (outer measure argument)
  have h_compl_zero : γ.condDist {z} σ (Agreeᶜ) = 0 := by
    rw [show Agree = {τ | ∀ x, x ∉ ({z} : Finset I) → τ x = σ x} from rfl] at hproper
    haveI := γ.isProb {z} σ
    -- μ(univ) ≤ μ(Agree) + μ(Agreeᶜ), and μ(univ) = 1 = μ(Agree)
    have h1 := measure_univ_le_add_compl
      (μ := γ.condDist {z} σ)
      {τ | ∀ x, x ∉ ({z} : Finset I) → τ x = σ x}
    rw [hproper, measure_univ] at h1
    -- 1 ≤ 1 + μ(Agreeᶜ), which is trivially true
    -- We need the other direction: μ(Agreeᶜ) ≤ μ(univ) - μ(Agree)
    -- Use: μ(Agree) + μ(Agreeᶜ) ≤ μ(univ) from subadditivity? No...
    -- Actually: μ(Agreeᶜ) ≤ μ(univ) = 1, and μ(Agree) = 1
    -- Use: Agree ∪ Agreeᶜ = univ, so μ(Agree ∪ Agreeᶜ) = μ(univ) = 1
    -- And μ(Agree ∪ Agreeᶜ) ≤ μ(Agree) + μ(Agreeᶜ) = 1 + μ(Agreeᶜ)
    -- So 1 ≤ 1 + μ(Agreeᶜ), giving μ(Agreeᶜ) ≥ 0 (trivial)
    -- For the upper bound: μ(Agreeᶜ) ≤ μ(Set.univ) = 1
    -- But we still can't prove = 0!
    -- The KEY: μ(Agree) ≤ μ(univ), so 1 ≤ 1, OK.
    -- Actually we need: μ is a probability measure so μ(S) + μ(Sᶜ) = 1 for
    -- MEASURABLE S. But Agree may not be measurable.
    -- For outer measures: μ(univ) ≤ μ(S) + μ(Sᶜ) always.
    -- With μ(S) = 1 and μ(univ) = 1: 1 ≤ 1 + μ(Sᶜ), which gives nothing.
    -- We need μ(S) + μ(Sᶜ) ≥ μ(univ), which is measure_univ_le_add_compl.
    -- And μ(Sᶜ) ≤ μ(univ) - μ(S) when μ(S) ≤ μ(univ)... for outer measures?
    -- Actually: for any outer measure, μ(Sᶜ) ≤ μ(univ) always.
    -- And we have μ(S) = 1 = μ(univ). So we need:
    -- μ(Sᶜ) = 0 from μ(S) = μ(univ) and μ being an actual measure.
    -- For measures (not just outer measures), if S is measurable:
    -- μ(univ) = μ(S) + μ(Sᶜ), so μ(Sᶜ) = 0.
    -- But S (= Agree) may not be measurable!
    -- However, μ(S) = 1 ≥ μ(univ) = 1, and μ is monotone...
    -- μ(Sᶜ) ≤ μ(univ \ S). For outer measures, μ(univ) ≤ μ(S) + μ(univ \ S).
    -- So 1 ≤ 1 + μ(Sᶜ). This gives nothing new.
    -- BUT: for a probability measure, μ(Sᶜ) + μ(S) ≥ 1 (subadditivity of univ cover).
    -- And μ(S) ≤ 1 (prob measure). With μ(S) = 1: μ(Sᶜ) ≥ 0 (trivial).
    -- We also have μ(Sᶜ) ≤ 1 - μ(S) only if S is measurable.
    -- For a measure (not just outer), if μ(S) = μ(univ), does it follow μ(Sᶜ) = 0?
    -- Yes! Because μ(univ) ≤ μ(S) + μ(Sᶜ) (outer measure) and
    -- μ(S) ≤ μ(univ) (monotonicity), so μ(S) = μ(univ).
    -- And μ(Sᶜ) ≤ μ(univ) - μ(S) (for any outer measure? No, this fails.)
    -- Actually for Measures: we DO have μ(Sᶜ) ≤ μ(univ) = 1.
    -- And measure_univ_le_add_compl gives 1 ≤ 1 + μ(Sᶜ), i.e., 0 ≤ μ(Sᶜ).
    -- We can't get μ(Sᶜ) = 0 without measurability of S!
    -- SOLUTION: Agree IS measurable since I is Fintype and S has BorelSpace.
    -- With [Fintype I] and [MeasurableSpace S], SpinConfig I S = I → S has
    -- the product sigma-algebra. Agree = {τ | ∀ x ∉ {z}, τ x = σ x} is measurable
    -- because it's a finite intersection of preimages.
    have hAgree_meas : MeasurableSet Agree := by
      change MeasurableSet {τ : SpinConfig I S | ∀ x, x ∉ ({z} : Finset I) → τ x = σ x}
      -- Use Finset.univ.measurableSet_biInter since I is Fintype
      have : {τ : SpinConfig I S | ∀ x, x ∉ ({z} : Finset I) → τ x = σ x} =
          ⋂ x ∈ ({z} : Finset I)ᶜ, {τ : SpinConfig I S | τ x = σ x} := by
        ext τ; simp [Finset.mem_compl]
      rw [this]
      refine Finset.measurableSet_biInter _ (fun x _ => ?_)
      change MeasurableSet ((fun (τ : SpinConfig I S) => τ x) ⁻¹' {σ x})
      exact (measurable_pi_apply x) (measurableSet_singleton (σ x))
    rw [measure_compl hAgree_meas (measure_ne_top _ _), hproper]
    simp
  -- B ⊆ B ∩ Agree ∪ Agreeᶜ, so μ B ≤ μ(B ∩ Agree) + μ(Agreeᶜ) = μ(B ∩ Agree)
  apply le_antisymm
  · calc γ.condDist {z} σ B
        ≤ γ.condDist {z} σ (B ∩ Agree) + γ.condDist {z} σ (Agreeᶜ) := by
          calc γ.condDist {z} σ B
              ≤ γ.condDist {z} σ ((B ∩ Agree) ∪ Agreeᶜ) := by
                apply measure_mono; intro τ hτ
                by_cases hτAgree : τ ∈ Agree
                · exact Or.inl ⟨hτ, hτAgree⟩
                · exact Or.inr hτAgree
            _ ≤ γ.condDist {z} σ (B ∩ Agree) + γ.condDist {z} σ (Agreeᶜ) :=
                measure_union_le _ _
      _ = γ.condDist {z} σ (B ∩ Agree) := by rw [h_compl_zero, add_zero]
  · exact measure_mono Set.inter_subset_left


/-! ### Step A: For fixed z and A, a.e. equality via set-integral uniqueness -/

/-- The agree set is measurable. -/
private lemma measurableSet_agree (L : Finset I) (s : SpinConfig I S) :
    MeasurableSet {t : SpinConfig I S | forall x, x ∉ L -> t x = s x} := by
  have : {t : SpinConfig I S | forall x, x ∉ L -> t x = s x} =
      ⋂ x ∈ Lᶜ, {t : SpinConfig I S | t x = s x} := by
    ext t; simp [Finset.mem_compl]
  rw [this]
  exact Finset.measurableSet_biInter _ (fun x _ => by
    change MeasurableSet ((fun (t : SpinConfig I S) => t x) ⁻¹' {s x})
    exact (measurable_pi_apply x) (measurableSet_singleton (s x)))

/-- Complement of agree set has measure zero under condDist. -/
private lemma condDist_agree_compl_zero (g : GibbsSpec I S) (L : Finset I)
    (s : SpinConfig I S) :
    g.condDist L s {t | forall x, x ∉ L -> t x = s x}ᶜ = 0 := by
  haveI := g.isProb L s
  rw [measure_compl (measurableSet_agree L s) (measure_ne_top _ _), g.proper L s]; simp

set_option maxHeartbeats 6400000 in
private lemma fiberMeasure_dlr_ae_fixed
    (g : GibbsSpec I S)
    (m : Measure (SpinConfig I S)) [IsProbabilityMeasure m]
    (hm : IsGibbsMeasure g m)
    (N_f : Finset I) (z : I) (hz : z ∉ N_f)
    {A : Set (SpinConfig I S)} (hA : MeasurableSet A) :
    let r := m.map (prodEquiv N_f)
    ∀ᵐ b ∂r.fst,
      (fiberMeasure m N_f b A).toReal =
        ∫ s, (g.condDist {z} s A).toReal ∂fiberMeasure m N_f b := by
  intro r
  -- Both functions are bounded, measurable, and their set-integrals agree.
  -- We use ae_eq_of_forall_setIntegral_eq_of_sigmaFinite.
  haveI : IsProbabilityMeasure r :=
    Measure.isProbabilityMeasure_map (prodEquiv N_f).measurable.aemeasurable
  haveI : IsFiniteMeasure r.fst := Measure.fst.instIsFiniteMeasure
  -- Both sides integrate to (m A).toReal
  have h_total := integral_fiberMeasure_toReal_eq_integral_condDist g m hm N_f z hA
  -- For set-integral equality, we use the DLR on restricted sets + properness
  -- The key argument: condDist {z} preserves N_f-coordinates (z ∉ N_f),
  -- so restricting to a base set T commutes with condDist averaging.
  -- This is the core measure-theoretic step.
  -- Both sides are bounded by 1, measurable, and have equal total integrals.
  -- Moreover, they have equal set-integrals (by DLR on restricted sets).
  sorry

/-! ### Steps B + C: upgrade to all A and all z -/

set_option maxHeartbeats 3200000 in
lemma fiberMeasure_dlr_ae
    (g : GibbsSpec I S)
    (m : Measure (SpinConfig I S)) [IsProbabilityMeasure m]
    (hm : IsGibbsMeasure g m)
    (N_f : Finset I) :
    let e := prodEquiv N_f
    let r := m.map e
    ∀ᵐ b ∂r.fst,
      ∀ z, z ∉ N_f →
        ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
          (fiberMeasure m N_f b A).toReal =
            ∫ s, (g.condDist {z} s A).toReal ∂fiberMeasure m N_f b := by
  intro e r
  -- Step C: Finite intersection over z ∉ N_f
  have h_finite_z : ({z : I | z ∉ N_f}).Countable :=
    (Set.Finite.subset (Set.toFinite _) (fun _ h => h)).countable
  suffices h_all_z : ∀ z, z ∉ N_f →
      ∀ᵐ b ∂r.fst, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
        (fiberMeasure m N_f b A).toReal =
          ∫ s, (g.condDist {z} s A).toReal ∂fiberMeasure m N_f b by
    have := (ae_ball_iff h_finite_z).mpr (fun z hz => h_all_z z hz)
    filter_upwards [this] with b hb z hz A hA; exact hb z hz A hA
  intro z hz
  -- Step B: For fixed z, upgrade from "a.e. for each A" to "a.e. for all A"
  -- using ae_induction_on_inter (pi-lambda for a.e. properties).
  haveI : StandardBorelSpace (SpinConfig I S) := inferInstance
  set f := embeddingReal (SpinConfig I S)
  have hf := measurableEmbedding_embeddingReal (SpinConfig I S)
  set Iic_rat := ⋃ a : ℚ, ({Set.Iic (a : ℝ)} : Set (Set ℝ))
  set gen := (Set.preimage f) '' Iic_rat
  have h_gen_eq : MeasurableSpace.generateFrom gen =
      (inferInstance : MeasurableSpace (SpinConfig I S)) := by
    show MeasurableSpace.generateFrom ((Set.preimage f) '' Iic_rat) = _
    rw [← MeasurableSpace.comap_generateFrom]
    change (MeasurableSpace.generateFrom Iic_rat).comap f = _
    rw [← Real.borel_eq_generateFrom_Iic_rat, ← BorelSpace.measurable_eq (α := ℝ), hf.comap_eq]
  have h_pi : IsPiSystem gen := Real.isPiSystem_Iic_rat.comap f
  apply MeasurableSpace.ae_induction_on_inter h_gen_eq.symm h_pi
  · -- C(b, empty)
    apply ae_of_all; intro b; simp [measure_empty]
  · -- C(b, generators): for a.e. b, C holds on all generators
    have h_gen_count : gen.Countable := by
      apply Set.Countable.image
      exact Set.countable_iUnion (fun _ => Set.countable_singleton _)
    rw [ae_ball_iff h_gen_count]
    intro t ht
    obtain ⟨s, hs, rfl⟩ := ht
    rw [Set.mem_iUnion] at hs; obtain ⟨q, hq⟩ := hs
    rw [Set.mem_singleton_iff] at hq; subst hq
    exact fiberMeasure_dlr_ae_fixed g m hm N_f z hz (hf.measurable measurableSet_Iic)
  · -- Complement closure
    apply ae_of_all; intro b A hA hCA
    haveI := fiberMeasure_isProbabilityMeasure m N_f b
    have hLHS : (fiberMeasure m N_f b Aᶜ).toReal = 1 - (fiberMeasure m N_f b A).toReal := by
      rw [prob_compl_eq_one_sub hA, ENNReal.toReal_sub_of_le prob_le_one (by simp)]; simp
    have hRHS : ∫ s, (g.condDist {z} s Aᶜ).toReal ∂fiberMeasure m N_f b =
        1 - ∫ s, (g.condDist {z} s A).toReal ∂fiberMeasure m N_f b := by
      have h_cd_compl : ∀ s, (g.condDist {z} s Aᶜ).toReal = 1 - (g.condDist {z} s A).toReal := by
        intro s; haveI := g.isProb {z} s
        rw [prob_compl_eq_one_sub hA, ENNReal.toReal_sub_of_le prob_le_one (by simp)]; simp
      simp_rw [h_cd_compl]
      rw [integral_sub (integrable_const 1)
        (Integrable.of_bound (g.measurable_condDist {z} A hA).aestronglyMeasurable 1
          (ae_of_all _ (fun s => by
            rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
            exact ENNReal.toReal_le_of_le_ofReal zero_le_one
              (by rw [ENNReal.ofReal_one]; exact prob_le_one))))]
      simp [measure_univ]
    rw [hLHS, hRHS, hCA]
  · -- Countable disjoint union closure
    apply ae_of_all; intro b As hdisj hAs_meas hAs_C
    haveI := fiberMeasure_isProbabilityMeasure m N_f b
    have hLHS : (fiberMeasure m N_f b (⋃ n, As n)).toReal =
        ∑' n, (fiberMeasure m N_f b (As n)).toReal := by
      rw [measure_iUnion hdisj hAs_meas]
      exact ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _)
    have hRHS : ∫ s, (g.condDist {z} s (⋃ n, As n)).toReal ∂fiberMeasure m N_f b =
        ∑' n, ∫ s, (g.condDist {z} s (As n)).toReal ∂fiberMeasure m N_f b := by
      have h_cd_union : ∀ s, (g.condDist {z} s (⋃ n, As n)).toReal =
          ∑' n, (g.condDist {z} s (As n)).toReal := by
        intro s; rw [measure_iUnion hdisj hAs_meas]
        exact ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _)
      simp_rw [h_cd_union]
      rw [integral_tsum
        (fun n => (g.measurable_condDist {z} (As n) (hAs_meas n)).aestronglyMeasurable)
        (by
          -- Each enorm term is ≤ 1, and terms sum via disjointness to ≤ 1.
          -- ‖condDist(As n).toReal‖ₑ ≤ condDist(As n) ≤ 1, and
          -- ∫ condDist(As n) d(fiber b) has tsum ≤ 1.
          sorry)]
    rw [hLHS, hRHS]; exact tsum_congr hAs_C

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
