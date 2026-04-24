/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Prokhorov Coupling for Compact Spin Spaces

Proves `dobrushin_coupling_axiom_compact` as a theorem, eliminating
the last custom axiom in the mass gap proof.

## Strategy

1. **Coupling set is compact**: The set of couplings of (μ₁, μ₂) is a
   closed subset of the compact space ProbabilityMeasure(Ω × Ω).
2. **Total disagreement is lsc**: By Portmanteau, ν ↦ ν(U).toReal is
   lsc for open U. Disagreement sets are open (T2 space).
3. **Minimum exists**: Compact + lsc → minimum attained.
4. **Minimizer contracts**: Same argument as the Fintype case.

## References

- Prokhorov (1956), compactness of probability measures
- Dobrushin (1968), Lemma 2
- Georgii (1988), Proposition 8.7
-/

import MarkovSemigroups.Coupling.DobrushinCoupling
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Probability.Kernel.Composition.Prod

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MeasureTheory MeasureTheory.Measure Topology Filter ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

variable {I S : Type*} [DecidableEq I] [Fintype I]
  [TopologicalSpace S] [CompactSpace S] [T2Space S] [SecondCountableTopology S]
  [MeasurableSpace S] [BorelSpace S]

-- Ω = SpinConfig I S = I → S
local notation "Ω" => SpinConfig I S

/-! ## Part I: Topological infrastructure -/

/-- The disagreement set {p | p.1 z ≠ p.2 z} is open (complement of a closed
diagonal-like set in a T2 space). -/
theorem isOpen_disagreement (z : I) :
    IsOpen {p : Ω × Ω | p.1 z ≠ p.2 z} := by
  -- Complement of a closed set
  have : {p : Ω × Ω | p.1 z ≠ p.2 z} = {p : Ω × Ω | p.1 z = p.2 z}ᶜ := by
    ext p; simp
  rw [this]
  exact (isClosed_eq
    ((continuous_apply z).comp continuous_fst)
    ((continuous_apply z).comp continuous_snd)).isOpen_compl

/-- The disagreement set is measurable. -/
theorem measurableSet_disagreement (z : I) :
    MeasurableSet {p : Ω × Ω | p.1 z ≠ p.2 z} :=
  (isOpen_disagreement z).measurableSet

/-! ## Part II: Lower semicontinuity of measure on open sets -/

/-- For an open set U in a compact metrizable space, the function
ν ↦ ν(U) is lower semicontinuous on ProbabilityMeasure. -/
theorem lsc_measure_open {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [T2Space X] [SecondCountableTopology X]
    (U : Set X) (hU : IsOpen U) (hU_meas : MeasurableSet U) :
    LowerSemicontinuous
      (fun ν : ProbabilityMeasure X => (ν : Measure X) U) := by
  -- CompactSpace + T2Space => RegularSpace => PseudoMetrizableSpace => HasOuterApproxClosed
  haveI : RegularSpace X := inferInstance
  haveI : TopologicalSpace.PseudoMetrizableSpace X := inferInstance
  haveI : HasOuterApproxClosed X := inferInstance
  rw [lowerSemicontinuous_iff_le_liminf]
  intro μ
  exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto tendsto_id hU

/-! ## Part III: Coupling set compactness -/

/-- The set of couplings of μ₁ and μ₂ as ProbabilityMeasures. -/
def CouplingSet (μ₁ μ₂ : Measure Ω) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    Set (ProbabilityMeasure (Ω × Ω)) :=
  {ν | (ν : Measure (Ω × Ω)).map Prod.fst = μ₁ ∧
       (ν : Measure (Ω × Ω)).map Prod.snd = μ₂}

/-- The coupling set is nonempty (product measure is a coupling). -/
theorem CouplingSet_nonempty (μ₁ μ₂ : Measure Ω)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    (CouplingSet μ₁ μ₂).Nonempty := by
  refine ⟨⟨μ₁.prod μ₂, inferInstance⟩, ?_, ?_⟩
  · simp [Measure.map_fst_prod, measure_univ]
  · simp [Measure.map_snd_prod, measure_univ]

/-- The coupling set is closed. -/
theorem CouplingSet_isClosed (μ₁ μ₂ : Measure Ω)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    IsClosed (CouplingSet μ₁ μ₂) := by
  -- CouplingSet is the intersection of two preimages of singletons
  -- under continuous maps in a T2 space
  let pm₁ : ProbabilityMeasure Ω := ⟨μ₁, inferInstance⟩
  let pm₂ : ProbabilityMeasure Ω := ⟨μ₂, inferInstance⟩
  -- The marginal maps as ProbabilityMeasure-valued functions
  let fst_map : ProbabilityMeasure (Ω × Ω) → ProbabilityMeasure Ω :=
    fun ν => ν.map measurable_fst.aemeasurable
  let snd_map : ProbabilityMeasure (Ω × Ω) → ProbabilityMeasure Ω :=
    fun ν => ν.map measurable_snd.aemeasurable
  -- Show CouplingSet = preimage intersection
  suffices h : CouplingSet μ₁ μ₂ = fst_map ⁻¹' {pm₁} ∩ snd_map ⁻¹' {pm₂} by
    rw [h]
    exact (isClosed_singleton.preimage (ProbabilityMeasure.continuous_map continuous_fst)).inter
      (isClosed_singleton.preimage (ProbabilityMeasure.continuous_map continuous_snd))
  ext ν
  simp only [CouplingSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Subtype.ext h1, Subtype.ext h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨congr_arg Subtype.val h1, congr_arg Subtype.val h2⟩

/-- The coupling set is compact. -/
theorem CouplingSet_isCompact (μ₁ μ₂ : Measure Ω)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    IsCompact (CouplingSet μ₁ μ₂) :=
  (CouplingSet_isClosed μ₁ μ₂).isCompact

/-! ## Part IV: Total disagreement and minimizer -/

/-- Total disagreement function. -/
def totalDisagreement (ν : ProbabilityMeasure (Ω × Ω)) : ℝ :=
  ∑ z : I, ((ν : Measure (Ω × Ω)) {p | p.1 z ≠ p.2 z}).toReal

/-- Total disagreement is lower semicontinuous. -/
theorem totalDisagreement_lsc :
    LowerSemicontinuous (totalDisagreement (I := I) (S := S)) := by
  -- totalDisagreement is a finite sum; sum of lsc is lsc
  apply lowerSemicontinuous_sum
  intro z _
  -- Each summand is ν ↦ ((ν : Measure) U_z).toReal where U_z = {p | p.1 z ≠ p.2 z}
  -- Strategy: show it equals truncateToReal 1 ∘ (ν ↦ (ν : Measure) U_z)
  -- and truncateToReal 1 is continuous + monotone, (ν ↦ (ν : Measure) U_z) is lsc
  have hU := isOpen_disagreement (I := I) (S := S) z
  suffices h : LowerSemicontinuous
      (fun ν : ProbabilityMeasure (Ω × Ω) =>
        ENNReal.truncateToReal 1 ((ν : Measure (Ω × Ω)) {p | p.1 z ≠ p.2 z})) by
    have heq : (fun ν : ProbabilityMeasure (Ω × Ω) =>
        ((ν : Measure (Ω × Ω)) {p | p.1 z ≠ p.2 z}).toReal) =
      (fun ν : ProbabilityMeasure (Ω × Ω) =>
        ENNReal.truncateToReal 1 ((ν : Measure (Ω × Ω)) {p | p.1 z ≠ p.2 z})) := by
      ext ν
      rw [ENNReal.truncateToReal_eq_toReal ENNReal.one_ne_top]
      exact (measure_mono (Set.subset_univ _)).trans (le_of_eq (measure_univ))
    rw [heq]
    exact h
  exact (ENNReal.continuous_truncateToReal ENNReal.one_ne_top).comp_lowerSemicontinuous
    (lsc_measure_open _ hU hU.measurableSet) (ENNReal.monotone_truncateToReal ENNReal.one_ne_top)

/-- There exists a coupling minimizing total disagreement. -/
theorem exists_min_disagreement_coupling (μ₁ μ₂ : Measure Ω)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    ∃ ν ∈ CouplingSet μ₁ μ₂,
      ∀ ν' ∈ CouplingSet μ₁ μ₂,
        totalDisagreement ν ≤ totalDisagreement ν' := by
  have hlsc : LowerSemicontinuousOn totalDisagreement (CouplingSet μ₁ μ₂) :=
    totalDisagreement_lsc.lowerSemicontinuousOn (CouplingSet μ₁ μ₂)
  obtain ⟨ν, hν_mem, hν_min⟩ := hlsc.exists_isMinOn
    (CouplingSet_nonempty μ₁ μ₂) (CouplingSet_isCompact μ₁ μ₂)
  exact ⟨ν, hν_mem, hν_min⟩

/-! ## Part V: Single-site coupling improvement

The key lemma: given any coupling P and a site z where DLR holds,
there exists an improved coupling Q that:
(a) preserves disagreement at all other sites w ≠ z
(b) satisfies the Dobrushin contraction at z
(c) remains a coupling of μ₁ and μ₂

Proof idea: disintegrate P along the non-z coordinates, replace the
z-fiber coupling with the canonical maximal coupling of the Gibbs
conditional distributions, and reassemble. The contraction follows
from the TV-distance bound of the maximal coupling and the influence
coefficient definition.

This is the Borel-space generalization of `updateCoupling_contraction_at_z`
+ `updateCoupling_isCoupling` + `updateCoupling_disagree_preserve`. -/

/-- Canonical maximal coupling for Borel spaces (no Countable requirement).

Same formula as `canonicalMaximalCoupling` but works for compact metrizable S.
The coupling puts mass on the diagonal where μ and ν overlap, and
independently on the residuals where they don't. -/
def canonicalMaximalCoupling_compact
    {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Measure (X × X) :=
  let overlap := μ ⊓ ν
  let residμ := μ - overlap
  let residν := ν - overlap
  let c := residμ Set.univ
  overlap.map (fun a => (a, a)) + c⁻¹ • (residμ.prod residν)

/-- Helper: `c⁻¹ • (c • m) = m` when c is finite. -/
private lemma inv_smul_smul_measure' {X : Type*} [MeasurableSpace X]
    {c : ENNReal} (hc_ne_top : c ≠ ⊤)
    (m : Measure X) (hm : c = 0 → m = 0) :
    c⁻¹ • (c • m) = m := by
  by_cases hc0 : c = 0
  · rw [hm hc0, hc0]; simp
  · rw [smul_smul, ENNReal.inv_mul_cancel hc0 hc_ne_top, one_smul]

/-- The residual measures have equal total mass (no Countable needed). -/
private theorem residual_mass_eq' {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (μ - μ ⊓ ν) Set.univ = (ν - μ ⊓ ν) Set.univ := by
  rw [Measure.sub_apply MeasurableSet.univ inf_le_left,
      Measure.sub_apply MeasurableSet.univ inf_le_right]
  simp [measure_univ]

/-- The first marginal of the compact canonical coupling equals μ. -/
theorem canonicalMaximalCoupling_compact_fst
    {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (canonicalMaximalCoupling_compact μ ν).map Prod.fst = μ := by
  unfold canonicalMaximalCoupling_compact
  rw [Measure.map_add _ _ measurable_fst]
  have hd : ((μ ⊓ ν).map (fun a => (a, a))).map Prod.fst = μ ⊓ ν := by
    rw [Measure.map_map measurable_fst measurable_diag]; convert Measure.map_id using 2
  rw [hd, Measure.map_smul]
  have hp : ((μ - μ ⊓ ν).prod (ν - μ ⊓ ν)).map Prod.fst =
      (ν - μ ⊓ ν) Set.univ • (μ - μ ⊓ ν) := Measure.map_fst_prod
  rw [hp, ← residual_mass_eq' μ ν,
      inv_smul_smul_measure' (measure_ne_top (μ - μ ⊓ ν) Set.univ) (μ - μ ⊓ ν)
        (fun h => Measure.measure_univ_eq_zero.mp h)]
  haveI : IsFiniteMeasure (μ ⊓ ν) := measureInf_isFiniteMeasure μ ν
  show μ ⊓ ν + (μ - μ ⊓ ν) = μ
  ext1 A hA
  simp only [Measure.add_apply]
  rw [Measure.sub_apply hA inf_le_left, add_comm]
  exact tsub_add_cancel_of_le (Measure.le_iff.mp inf_le_left A hA)

/-- The second marginal of the compact canonical coupling equals ν. -/
theorem canonicalMaximalCoupling_compact_snd
    {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (canonicalMaximalCoupling_compact μ ν).map Prod.snd = ν := by
  unfold canonicalMaximalCoupling_compact
  rw [Measure.map_add _ _ measurable_snd]
  have hd : ((μ ⊓ ν).map (fun a => (a, a))).map Prod.snd = μ ⊓ ν := by
    rw [Measure.map_map measurable_snd measurable_diag]; convert Measure.map_id using 2
  rw [hd, Measure.map_smul]
  have hp : ((μ - μ ⊓ ν).prod (ν - μ ⊓ ν)).map Prod.snd =
      (μ - μ ⊓ ν) Set.univ • (ν - μ ⊓ ν) := Measure.map_snd_prod
  rw [hp, inv_smul_smul_measure' (measure_ne_top (μ - μ ⊓ ν) Set.univ) (ν - μ ⊓ ν)
      (fun h => Measure.measure_univ_eq_zero.mp (residual_mass_eq' μ ν ▸ h))]
  haveI : IsFiniteMeasure (μ ⊓ ν) := measureInf_isFiniteMeasure μ ν
  show μ ⊓ ν + (ν - μ ⊓ ν) = ν
  ext1 A hA
  simp only [Measure.add_apply]
  rw [Measure.sub_apply hA inf_le_right, add_comm]
  exact tsub_add_cancel_of_le (Measure.le_iff.mp inf_le_right A hA)

/-- For finite measures with `μ = λ.withDensity f` and `ν = λ.withDensity g`,
the lattice infimum satisfies `μ ⊓ ν = λ.withDensity (min f g)`.

The ≥ direction: `min f g ≤ f` and `min f g ≤ g` a.e., so `withDensity (min f g) ≤ μ, ν`.
The ≤ direction: take `t = {y | f y ≤ g y}` in `inf_apply`; on `t ∩ C` the density is `f = min`,
on `tᶜ ∩ C` the density is `g = min`, giving equality with `∫ min(f,g) dλ`. -/
private theorem inf_eq_withDensity_min {Y : Type*} [MeasurableSpace Y]
    (lam : Measure Y) [IsFiniteMeasure lam]
    {f_d g_d : Y → ℝ≥0∞} (hf_m : Measurable f_d) (hg_m : Measurable g_d) :
    (lam.withDensity f_d) ⊓ (lam.withDensity g_d) =
      lam.withDensity (fun y => min (f_d y) (g_d y)) := by
  apply le_antisymm
  · -- (≤) μ ⊓ ν ≤ withDensity(min f g): use inf_apply with t = {y | f y ≤ g y}
    rw [Measure.le_iff]
    intro C hC
    rw [Measure.inf_apply hC]
    apply csInf_le
    · exact ⟨0, fun m ⟨_, hm⟩ => hm ▸ zero_le _⟩
    refine ⟨{y | f_d y ≤ g_d y}, ?_⟩
    have ht_meas : MeasurableSet {y | f_d y ≤ g_d y} := measurableSet_le hf_m hg_m
    -- Show the value at the witness equals the withDensity value
    rw [withDensity_apply _ (ht_meas.inter hC),
        withDensity_apply _ (ht_meas.compl.inter hC),
        withDensity_apply _ hC]
    -- Need: ∫ f on {f≤g}∩C + ∫ g on {f≤g}ᶜ∩C = ∫ min(f,g) on C
    -- On {f≤g}, f = min(f,g); on {f≤g}ᶜ, g = min(f,g)
    have h1 : ∫⁻ y in {y | f_d y ≤ g_d y} ∩ C, f_d y ∂lam =
        ∫⁻ y in {y | f_d y ≤ g_d y} ∩ C, min (f_d y) (g_d y) ∂lam :=
      setLIntegral_congr_fun (ht_meas.inter hC) (fun y hy => by
        exact (min_eq_left (hy.1 : f_d y ≤ g_d y)).symm)
    have h2 : ∫⁻ y in {y | f_d y ≤ g_d y}ᶜ ∩ C, g_d y ∂lam =
        ∫⁻ y in {y | f_d y ≤ g_d y}ᶜ ∩ C, min (f_d y) (g_d y) ∂lam :=
      setLIntegral_congr_fun (ht_meas.compl.inter hC) (fun y hy => by
        have : ¬ f_d y ≤ g_d y := hy.1
        exact (min_eq_right (le_of_lt (not_le.mp this))).symm)
    rw [h1, h2]
    -- Now: ∫ min on {f≤g}∩C + ∫ min on {f≤g}ᶜ∩C = ∫ min on C
    rw [← Measure.restrict_restrict ht_meas, ← Measure.restrict_restrict ht_meas.compl,
        lintegral_add_compl _ ht_meas]
  · -- (≥) withDensity(min f g) ≤ μ ⊓ ν: min ≤ f and min ≤ g
    exact le_inf
      (withDensity_mono (ae_of_all _ (fun y => min_le_left _ _)))
      (withDensity_mono (ae_of_all _ (fun y => min_le_right _ _)))

/-- The measure infimum `(f x ⊓ g x)(C)` is measurable in x.

We express `(μ ⊓ ν)(C)` via Radon-Nikodym derivatives:
`(μ ⊓ ν)(C) = ∫⁻ y in C, min(dμ/d(μ+ν), dν/d(μ+ν)) d(μ+ν)`.
Joint measurability of kernel Radon-Nikodym derivatives (from Mathlib's
`Kernel.measurable_rnDeriv`) then gives measurability
of the parametric integral via `Measurable.setLIntegral_kernel_prod_right`. -/
private theorem measurable_inf_apply {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    {f g : X → Measure Y} [hfp : ∀ x, IsProbabilityMeasure (f x)]
    [hgp : ∀ x, IsProbabilityMeasure (g x)]
    (hf : Measurable f) (hg : Measurable g)
    (C : Set Y) (hC : MeasurableSet C) :
    Measurable (fun x => (f x ⊓ g x) C) := by
  -- Build kernels from the measurable functions
  let κ_f : Kernel X Y := ⟨f, hf⟩
  let κ_g : Kernel X Y := ⟨g, hg⟩
  let κ_sum : Kernel X Y := κ_f + κ_g
  -- Kernel finiteness: probability measures have uniform bound 1
  haveI : IsFiniteKernel κ_f :=
    ⟨⟨1, ENNReal.one_lt_top, fun a => by simp [κ_f, measure_univ]⟩⟩
  haveI : IsFiniteKernel κ_g :=
    ⟨⟨1, ENNReal.one_lt_top, fun a => by simp [κ_g, measure_univ]⟩⟩
  -- Reduce to showing the function equals a measurable integral expression
  suffices hinf : ∀ x, (f x ⊓ g x) C =
      ∫⁻ y in C, min (Kernel.rnDeriv κ_f κ_sum x y)
        (Kernel.rnDeriv κ_g κ_sum x y) ∂κ_sum x by
    simp_rw [hinf]
    exact @Measurable.setLIntegral_kernel_prod_right X Y _ _ κ_sum _
      (fun x y => min (Kernel.rnDeriv κ_f κ_sum x y) (Kernel.rnDeriv κ_g κ_sum x y))
      ((Kernel.measurable_rnDeriv κ_f κ_sum).min (Kernel.measurable_rnDeriv κ_g κ_sum))
      C hC
  -- Prove the pointwise identity using kernel Lebesgue decomposition
  intro x
  have hf_ac : f x ≪ κ_sum x := absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hg_ac : g x ≪ κ_sum x := absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  -- Kernel Lebesgue decomposition: κ = withDensity η (rnDeriv κ η) + singularPart
  -- Since f(x) ≪ κ_sum(x), singular part is 0, so f(x) = (κ_sum x).withDensity(rnDeriv ...)
  -- Kernel Lebesgue decomposition gives f(x) = (κ_sum x).withDensity(rnDeriv κ_f κ_sum x)
  have hf_eq : f x = (κ_sum x).withDensity (Kernel.rnDeriv κ_f κ_sum x) := by
    have h := Kernel.rnDeriv_add_singularPart κ_f κ_sum
    have hsp := (Kernel.singularPart_eq_zero_iff_absolutelyContinuous κ_f κ_sum x).mpr hf_ac
    -- h : Kernel.withDensity κ_sum (rnDeriv κ_f κ_sum) + singularPart κ_f κ_sum = κ_f
    have h_eval := congr_fun (congr_arg DFunLike.coe h) x
    -- h_eval at x: (withDensity κ_sum (rnDeriv κ_f κ_sum)) x + (singularPart κ_f κ_sum) x = κ_f x
    simp only [Kernel.coe_add, Pi.add_apply, hsp, add_zero] at h_eval
    -- h_eval: (Kernel.withDensity κ_sum (rnDeriv κ_f κ_sum)) x = κ_f x = f x
    show κ_f x = _
    rw [← h_eval, Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv κ_f κ_sum)]
  have hg_eq : g x = (κ_sum x).withDensity (Kernel.rnDeriv κ_g κ_sum x) := by
    have h := Kernel.rnDeriv_add_singularPart κ_g κ_sum
    have hsp := (Kernel.singularPart_eq_zero_iff_absolutelyContinuous κ_g κ_sum x).mpr hg_ac
    have h_eval := congr_fun (congr_arg DFunLike.coe h) x
    simp only [Kernel.coe_add, Pi.add_apply, hsp, add_zero] at h_eval
    show κ_g x = _
    rw [← h_eval, Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv κ_g κ_sum)]
  rw [hf_eq, hg_eq, inf_eq_withDensity_min (κ_sum x)
    (Kernel.measurable_rnDeriv_right κ_f κ_sum x)
    (Kernel.measurable_rnDeriv_right κ_g κ_sum x),
    withDensity_apply _ hC]

/-- The canonical coupling is Giry-measurable in both arguments.

Uses `Measure.measurable_of_measurable_coe`: for each measurable A in Y × Y,
  cmc(f x, g x)(A) = (f x ⊓ g x)(diag⁻¹' A) + c(x)⁻¹ * (resid_f(x).prod resid_g(x))(A)
The overlap term is measurable via `measurable_inf_apply`.
The product term is measurable by building kernels for the residuals and using
`Kernel.prod_apply` + `Kernel.measurable_coe`. -/
theorem canonicalMaximalCoupling_compact_measurable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    {f g : X → Measure Y}
    [∀ x, IsProbabilityMeasure (f x)] [∀ x, IsProbabilityMeasure (g x)]
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => canonicalMaximalCoupling_compact (f x) (g x)) := by
  -- Step 0: Establish measurability of the inf as a function into Measure Y
  have h_inf_meas : Measurable (fun x => f x ⊓ g x) := by
    apply Measure.measurable_of_measurable_coe
    intro C hC
    exact measurable_inf_apply hf hg C hC
  -- Step 1: Establish measurability of residuals as functions into Measure Y
  have h_resid_f_meas : Measurable (fun x => f x - f x ⊓ g x) := by
    apply Measure.measurable_of_measurable_coe
    intro C hC
    have : ∀ x, (f x - f x ⊓ g x) C = f x C - (f x ⊓ g x) C := by
      intro x
      haveI : IsFiniteMeasure (f x ⊓ g x) := measureInf_isFiniteMeasure (f x) (g x)
      exact Measure.sub_apply hC inf_le_left
    simp_rw [this]
    exact ((Measure.measurable_coe hC).comp hf).sub (measurable_inf_apply hf hg C hC)
  have h_resid_g_meas : Measurable (fun x => g x - f x ⊓ g x) := by
    apply Measure.measurable_of_measurable_coe
    intro C hC
    have : ∀ x, (g x - f x ⊓ g x) C = g x C - (f x ⊓ g x) C := by
      intro x
      haveI : IsFiniteMeasure (f x ⊓ g x) := measureInf_isFiniteMeasure (f x) (g x)
      exact Measure.sub_apply hC inf_le_right
    simp_rw [this]
    exact ((Measure.measurable_coe hC).comp hg).sub (measurable_inf_apply hf hg C hC)
  -- Step 2: Build kernels from the measurable functions
  let κ_rf : Kernel X Y := ⟨fun x => f x - f x ⊓ g x, h_resid_f_meas⟩
  let κ_rg : Kernel X Y := ⟨fun x => g x - f x ⊓ g x, h_resid_g_meas⟩
  -- Finite kernel instances (each residual ≤ original probability measure, so mass ≤ 1)
  have : IsFiniteKernel κ_rf :=
    ⟨⟨1, ENNReal.one_lt_top, fun a => by
      simp only [κ_rf, Kernel.coe_mk]
      exact (Measure.le_iff'.mp Measure.sub_le Set.univ).trans (by simp [measure_univ])⟩⟩
  have : IsFiniteKernel κ_rg :=
    ⟨⟨1, ENNReal.one_lt_top, fun a => by
      simp only [κ_rg, Kernel.coe_mk]
      exact (Measure.le_iff'.mp Measure.sub_le Set.univ).trans (by simp [measure_univ])⟩⟩
  -- Step 3: Reduce to pointwise set evaluation
  apply Measure.measurable_of_measurable_coe
  intro A hA
  show Measurable (fun x => canonicalMaximalCoupling_compact (f x) (g x) A)
  -- Unfold: overlap.map(diag) + c⁻¹ • (resid_f.prod resid_g)
  simp only [canonicalMaximalCoupling_compact, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  -- Step 4: Measurability of c(x)⁻¹ where c(x) = (f x - f x ⊓ g x)(univ)
  have hc_meas : Measurable (fun x => ((f x - f x ⊓ g x) Set.univ)⁻¹) := by
    apply Measurable.inv
    have hc_eq : ∀ x, (f x - f x ⊓ g x) Set.univ = 1 - (f x ⊓ g x) Set.univ := by
      intro x
      haveI : IsFiniteMeasure (f x ⊓ g x) := measureInf_isFiniteMeasure (f x) (g x)
      rw [Measure.sub_apply MeasurableSet.univ inf_le_left, measure_univ]
    simp_rw [hc_eq]
    exact measurable_const.sub (measurable_inf_apply hf hg _ MeasurableSet.univ)
  apply Measurable.add
  · -- Piece 1: x ↦ (f x ⊓ g x).map(diag) A = (f x ⊓ g x)(diag⁻¹' A)
    simp_rw [Measure.map_apply measurable_diag hA]
    exact measurable_inf_apply hf hg _ (measurable_diag hA)
  · -- Piece 2: x ↦ c(x)⁻¹ * ((f x - f x ⊓ g x).prod (g x - f x ⊓ g x)) A
    apply Measurable.mul hc_meas
    -- Use kernel product: (Kernel.prod κ_rf κ_rg) x = (κ_rf x).prod (κ_rg x)
    let κ_prod := Kernel.prod κ_rf κ_rg
    have h_eq : ∀ x, ((f x - f x ⊓ g x).prod (g x - f x ⊓ g x)) A =
        κ_prod x A := by
      intro x
      show _ = (Kernel.prod κ_rf κ_rg) x A
      rw [Kernel.prod_apply κ_rf κ_rg x]; rfl
    simp_rw [h_eq]
    exact κ_prod.measurable_coe hA

/-- The canonical maximal coupling's disagreement measure is at most the
residual mass c = (μ - μ ⊓ ν)(univ). -/
private theorem canonicalMaximalCoupling_compact_ne_le_residual
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [BorelSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (canonicalMaximalCoupling_compact μ ν) {p | p.1 ≠ p.2} ≤ (μ - μ ⊓ ν) Set.univ := by
  unfold canonicalMaximalCoupling_compact
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  -- Piece 1: overlap.map(diag)({≠}) = 0
  have hdiag_ne : ((μ ⊓ ν).map (fun a => (a, a))) {p : X × X | p.1 ≠ p.2} = 0 := by
    -- {p | p.1 ≠ p.2} is measurable (complement of closed diagonal in T2 Borel space)
    have hne_meas : MeasurableSet {p : X × X | p.1 ≠ p.2} := by
      have : {p : X × X | p.1 ≠ p.2} = (Set.diagonal X)ᶜ := by
        ext ⟨a, b⟩; simp [Set.diagonal]
      rw [this]
      exact isClosed_diagonal.measurableSet.compl
    rw [Measure.map_apply measurable_diag hne_meas]
    -- Preimage of {≠} under diag is ∅
    have : (fun a : X => (a, a)) ⁻¹' {p : X × X | p.1 ≠ p.2} = ∅ := by
      ext x; simp
    rw [this, measure_empty]
  rw [hdiag_ne, zero_add]
  -- Piece 2: c⁻¹ * (resid_μ.prod resid_ν)({≠}) ≤ c⁻¹ * (resid_μ.prod resid_ν)(univ) = c
  calc ((μ - μ ⊓ ν) Set.univ)⁻¹ * ((μ - μ ⊓ ν).prod (ν - μ ⊓ ν)) {p | p.1 ≠ p.2}
      ≤ ((μ - μ ⊓ ν) Set.univ)⁻¹ * ((μ - μ ⊓ ν).prod (ν - μ ⊓ ν)) Set.univ :=
        by exact mul_le_mul_of_nonneg_left (measure_mono (Set.subset_univ _)) (zero_le _)
    _ = ((μ - μ ⊓ ν) Set.univ)⁻¹ * ((μ - μ ⊓ ν) Set.univ * (ν - μ ⊓ ν) Set.univ) := by
        congr 1
        rw [show (Set.univ : Set (X × X)) = Set.univ ×ˢ Set.univ from (Set.univ_prod_univ).symm,
            Measure.prod_prod]
    _ = ((μ - μ ⊓ ν) Set.univ)⁻¹ * ((μ - μ ⊓ ν) Set.univ * (μ - μ ⊓ ν) Set.univ) := by
        rw [residual_mass_eq' μ ν]
    _ = (μ - μ ⊓ ν) Set.univ := by
        by_cases hc : (μ - μ ⊓ ν) Set.univ = 0
        · simp [hc]
        · rw [← mul_assoc, ENNReal.inv_mul_cancel hc (measure_ne_top _ _), one_mul]

/-- The residual mass (μ - μ ⊓ ν)(univ).toReal ≤ tvDist μ ν for probability measures. -/
private theorem residual_mass_le_tvDist
    {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((μ - μ ⊓ ν) Set.univ).toReal ≤ tvDist μ ν := by
  -- (μ - μ⊓ν)(univ).toReal = 1 - (μ⊓ν)(univ).toReal = 1 - (1 - tvNorm) = tvNorm = tvDist
  rw [tvDist_eq_tvNorm]
  have h_overlap := overlapMeasure_mass μ ν
  unfold overlapMeasure at h_overlap
  rw [Measure.sub_apply MeasurableSet.univ inf_le_left,
      ENNReal.toReal_sub_of_le
        (Measure.le_iff.mp inf_le_left Set.univ MeasurableSet.univ)
        (measure_ne_top μ Set.univ),
      measure_univ (μ := μ), ENNReal.toReal_one]
  linarith

/-- The canonical maximal coupling's disagreement probability is at most
the total mass of the residual measure, which equals tvDist. -/
private theorem canonicalMaximalCoupling_compact_ne_le
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [BorelSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((canonicalMaximalCoupling_compact μ ν) {p | p.1 ≠ p.2}).toReal ≤
      tvDist μ ν := by
  -- The coupling's total mass is finite (it equals μ's mass = 1)
  have hcmc_finite : (canonicalMaximalCoupling_compact μ ν) {p | p.1 ≠ p.2} ≠ ⊤ := by
    exact ((measure_mono (Set.subset_univ _)).trans_lt (by
      have h := canonicalMaximalCoupling_compact_fst μ ν
      calc (canonicalMaximalCoupling_compact μ ν) Set.univ
          = ((canonicalMaximalCoupling_compact μ ν).map Prod.fst) Set.univ := by
            rw [Measure.map_apply measurable_fst MeasurableSet.univ]; rfl
        _ = μ Set.univ := by rw [h]
        _ = 1 := measure_univ
        _ < ⊤ := ENNReal.one_lt_top)).ne
  calc ((canonicalMaximalCoupling_compact μ ν) {p | p.1 ≠ p.2}).toReal
      ≤ ((μ - μ ⊓ ν) Set.univ).toReal := by
        apply (ENNReal.toReal_le_toReal hcmc_finite (measure_ne_top _ _)).mpr
        exact canonicalMaximalCoupling_compact_ne_le_residual μ ν
    _ ≤ tvDist μ ν := residual_mass_le_tvDist μ ν

/-- The conditional distribution at {z} restricted to the z-marginal, pushed
forward via `Function.update σ z`, recovers the full conditional distribution.

This is the compact-space analog of `condDist_eq_marginal_map_update` from
DobrushinCoupling.lean, which required [Countable S] [MeasurableSingletonClass S].
In the compact Borel case we cannot use `Measurable.of_discrete`. -/
private lemma condDist_eq_marginal_map_update_compact
    (γ : GibbsSpec I S) (z : I) (σ : SpinConfig I S) :
    γ.condDist {z} σ = (marginalAtSite (γ.condDist {z} σ) z).map (Function.update σ z) := by
  -- Both sides are probability measures. We show they are equal by showing
  -- the map (update σ z ∘ (· z)) is the identity ae condDist {z} σ.
  -- Measurability of the update map
  have h_update_meas : Measurable (Function.update σ z) :=
    measurable_pi_lambda _ (fun i => by
      by_cases h : i = z
      · subst h; simp only [Function.update_self]; exact measurable_id
      · simp only [Function.update_of_ne h]; exact measurable_const)
  -- Unfold and use map_map
  unfold marginalAtSite
  rw [Measure.map_map h_update_meas (measurable_pi_apply z)]
  -- Now goal: condDist {z} σ = (condDist {z} σ).map (update σ z ∘ (· z))
  -- On the support Agree = {τ | ∀ x ∉ {z}, τ x = σ x}, (update σ z (τ z)) = τ
  set Agree := {τ : SpinConfig I S | ∀ x, x ∉ ({z} : Finset I) → τ x = σ x}
  have hid : ∀ τ ∈ Agree, Function.update σ z (τ z) = τ := by
    intro τ hτ; ext w
    by_cases hw : w = z
    · subst hw; simp [Function.update]
    · rw [Function.update_of_ne hw]; exact (hτ w (by simp [hw])).symm
  -- Agree is measurable (finite intersection of preimages of singletons)
  have hAgree_meas : MeasurableSet Agree := by
    change MeasurableSet {τ : SpinConfig I S | ∀ x, x ∉ ({z} : Finset I) → τ x = σ x}
    have : {τ : SpinConfig I S | ∀ x, x ∉ ({z} : Finset I) → τ x = σ x} =
        ⋂ x ∈ ({z} : Finset I)ᶜ, {τ : SpinConfig I S | τ x = σ x} := by
      ext τ; simp [Finset.mem_compl]
    rw [this]
    exact Finset.measurableSet_biInter _ (fun x _ => by
      change MeasurableSet ((fun (τ : SpinConfig I S) => τ x) ⁻¹' {σ x})
      exact (measurable_pi_apply x) (measurableSet_singleton (σ x)))
  -- Agreeᶜ has measure 0
  have hcompl : γ.condDist {z} σ Agreeᶜ = 0 := by
    rw [measure_compl hAgree_meas (measure_ne_top _ _), γ.proper {z} σ]; simp
  -- The composed map equals id ae
  have hmap_eq : (Function.update σ z ∘ (· z)) =ᵐ[γ.condDist {z} σ] id := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨Agree, mem_ae_iff.mpr hcompl, fun τ hτ => hid τ hτ⟩
  rw [Measure.map_congr hmap_eq, Measure.map_id]

theorem updateCoupling_compact_exists
    (γ : GibbsSpec I S) (z : I)
    (μ₁ μ₂ : Measure Ω)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (P : Measure (Ω × Ω)) [IsProbabilityMeasure P]
    (hP : IsCoupling P μ₁ μ₂)
    (hdlr₁ : ∀ (A : Set Ω), MeasurableSet A →
      (μ₁ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₁)
    (hdlr₂ : ∀ (A : Set Ω), MeasurableSet A →
      (μ₂ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₂) :
    ∃ (Q : Measure (Ω × Ω)),
      IsProbabilityMeasure Q ∧
      IsCoupling Q μ₁ μ₂ ∧
      (∀ w, w ≠ z → Q {p | p.1 w ≠ p.2 w} = P {p | p.1 w ≠ p.2 w}) ∧
      (Q {p | p.1 z ≠ p.2 z}).toReal ≤
        ∑ w : I, influenceCoeff γ z w *
          (P {p | p.1 w ≠ p.2 w}).toReal := by
  classical
  -- Abbreviation for the coupling kernel at each pair (σ, η)
  let cmc (σ η : Ω) : Measure (S × S) :=
    canonicalMaximalCoupling_compact
      (marginalAtSite (γ.condDist {z} σ) z)
      (marginalAtSite (γ.condDist {z} η) z)
  -- The update map ψ: (S × S) → (Ω × Ω), parametrized by (σ, η)
  let ψ (σ η : Ω) : S × S → Ω × Ω :=
    fun ss => (Function.update σ z ss.1, Function.update η z ss.2)
  -- Measurability of ψ for fixed (σ, η)
  have hψ_meas : ∀ (σ η : Ω), Measurable (ψ σ η) := by
    intro σ η
    refine Measurable.prod ?_ ?_
    · refine measurable_pi_lambda _ (fun i => ?_)
      -- Goal: Measurable (fun ss : S × S => (ψ σ η ss).1 i)
      -- = Measurable (fun ss => (Function.update σ z ss.1) i)
      by_cases hi : i = z
      · -- i = z: (Function.update σ z ss.1) z = ss.1
        have heq : (fun ss : S × S => (ψ σ η ss).1 i) = fun ss => ss.1 := by
          ext ⟨s1, s2⟩; dsimp [ψ]; rw [hi, Function.update_self]
        rw [heq]; exact measurable_fst
      · -- i ≠ z: (Function.update σ z ss.1) i = σ i
        have heq : (fun ss : S × S => (ψ σ η ss).1 i) = fun _ => σ i := by
          ext ⟨s1, s2⟩; dsimp [ψ]; rw [Function.update_of_ne hi]
        rw [heq]; exact measurable_const
    · refine measurable_pi_lambda _ (fun i => ?_)
      by_cases hi : i = z
      · have heq : (fun ss : S × S => (ψ σ η ss).2 i) = fun ss => ss.2 := by
          ext ⟨s1, s2⟩; dsimp [ψ]; rw [hi, Function.update_self]
        rw [heq]; exact measurable_snd
      · have heq : (fun ss : S × S => (ψ σ η ss).2 i) = fun _ => η i := by
          ext ⟨s1, s2⟩; dsimp [ψ]; rw [Function.update_of_ne hi]
        rw [heq]; exact measurable_const
  -- cmc gives probability measures
  have hcmc_prob : ∀ (σ η : Ω), IsProbabilityMeasure (cmc σ η) := by
    intro σ η
    constructor
    -- cmc σ η has total mass 1 because its first marginal is a probability measure
    have h := canonicalMaximalCoupling_compact_fst
      (marginalAtSite (γ.condDist {z} σ) z) (marginalAtSite (γ.condDist {z} η) z)
    -- (cmc σ η).map fst = marginalAtSite ... which has mass 1
    calc (cmc σ η) Set.univ
        = ((cmc σ η).map Prod.fst) Set.univ := by
          rw [Measure.map_apply measurable_fst MeasurableSet.univ]; rfl
      _ = (marginalAtSite (γ.condDist {z} σ) z) Set.univ := by rw [h]
      _ = 1 := measure_univ
  -- The full coupling kernel f : Ω × Ω → Measure(Ω × Ω)
  let f : Ω × Ω → Measure (Ω × Ω) := fun p => (cmc p.1 p.2).map (ψ p.1 p.2)
  -- Giry measurability of f
  have hf_meas : Measurable f := by
    -- f p = (cmc p.1 p.2).map (ψ p.1 p.2)
    -- We use Measure.measurable_of_measurable_coe: for each measurable B,
    -- p ↦ f p B is measurable.
    apply Measure.measurable_of_measurable_coe
    intro B hB
    -- f p B = (cmc p.1 p.2) (ψ p.1 p.2 ⁻¹' B)
    --       = ∫⁻ ss, B.indicator 1 (ψ p.1 p.2 ss) ∂(cmc p.1 p.2)
    have hf_eq : ∀ p : Ω × Ω, f p B =
        ∫⁻ ss, Set.indicator B 1 (ψ p.1 p.2 ss) ∂(cmc p.1 p.2) := by
      intro p
      show (cmc p.1 p.2).map (ψ p.1 p.2) B = _
      rw [Measure.map_apply (hψ_meas p.1 p.2) hB,
          ← lintegral_indicator_one (hψ_meas p.1 p.2 hB)]
      congr 1
    simp_rw [hf_eq]
    -- Build kernel from cmc
    have hcmc_meas : Measurable (fun p : Ω × Ω => cmc p.1 p.2) := by
      -- cmc σ η = canonicalMaximalCoupling_compact (marginalAtSite (condDist {z} σ) z)
      --                                             (marginalAtSite (condDist {z} η) z)
      -- marginalAtSite (condDist {z} σ) z = (condDist {z} σ).map (· z)
      -- σ ↦ condDist {z} σ is Giry-measurable by hcond_meas
      -- So σ ↦ marginalAtSite (condDist {z} σ) z is Giry-measurable
      have hcond_meas_local : Measurable (γ.condDist ({z} : Finset I)) := by
        apply Measure.measurable_of_measurable_coe
        intro A hA
        have hne_top : ∀ σ, γ.condDist {z} σ A ≠ ⊤ := fun σ =>
          (measure_lt_top (γ.condDist {z} σ) A).ne
        have heq : (fun σ => γ.condDist {z} σ A) =
            (fun σ => ENNReal.ofReal (γ.condDist {z} σ A).toReal) := by
          ext σ; exact (ENNReal.ofReal_toReal (hne_top σ)).symm
        rw [heq]
        exact ENNReal.measurable_ofReal.comp (γ.measurable_condDist {z} A hA)
      have h_marg_meas : Measurable (fun σ : Ω => marginalAtSite (γ.condDist {z} σ) z) := by
        unfold marginalAtSite
        exact (Measure.measurable_map _ (measurable_pi_apply z)).comp hcond_meas_local
      -- (σ, η) ↦ cmc σ η is Giry-measurable by canonicalMaximalCoupling_compact_measurable
      exact canonicalMaximalCoupling_compact_measurable
        (h_marg_meas.comp measurable_fst) (h_marg_meas.comp measurable_snd)
    let κ_cmc : Kernel (Ω × Ω) (S × S) := ⟨fun p => cmc p.1 p.2, hcmc_meas⟩
    haveI : IsFiniteKernel κ_cmc :=
      ⟨⟨1, ENNReal.one_lt_top, fun p => by
        simp only [κ_cmc, Kernel.coe_mk]
        haveI := hcmc_prob p.1 p.2; exact le_of_eq measure_univ⟩⟩
    -- The integrand g(p, ss) = B.indicator 1 (ψ p.1 p.2 ss) is jointly measurable
    -- Key: the joint map Ψ : (Ω × Ω) × (S × S) → Ω × Ω is measurable
    have hΨ_meas : Measurable (fun (pss : (Ω × Ω) × (S × S)) =>
        ψ pss.1.1 pss.1.2 pss.2) := by
      -- Ψ (p, ss) = (update p.1 z ss.1, update p.2 z ss.2)
      refine Measurable.prod ?_ ?_
      · -- (p, ss) ↦ update p.1 z ss.1
        refine measurable_pi_lambda _ (fun i => ?_)
        by_cases hi : i = z
        · -- i = z: (update p.1 z ss.1) z = ss.1
          have : (fun pss : (Ω × Ω) × (S × S) =>
              (ψ pss.1.1 pss.1.2 pss.2).1 i) =
              fun pss => pss.2.1 := by
            ext ⟨⟨σ, η⟩, ⟨s1, s2⟩⟩; dsimp [ψ]; rw [hi, Function.update_self]
          rw [this]; exact measurable_snd.fst
        · -- i ≠ z: (update p.1 z ss.1) i = p.1 i
          have : (fun pss : (Ω × Ω) × (S × S) =>
              (ψ pss.1.1 pss.1.2 pss.2).1 i) =
              fun pss => pss.1.1 i := by
            ext ⟨⟨σ, η⟩, ⟨s1, s2⟩⟩; dsimp [ψ]; rw [Function.update_of_ne hi]
          rw [this]; exact (measurable_pi_apply i).comp measurable_fst.fst
      · -- (p, ss) ↦ update p.2 z ss.2
        refine measurable_pi_lambda _ (fun i => ?_)
        by_cases hi : i = z
        · have : (fun pss : (Ω × Ω) × (S × S) =>
              (ψ pss.1.1 pss.1.2 pss.2).2 i) =
              fun pss => pss.2.2 := by
            ext ⟨⟨σ, η⟩, ⟨s1, s2⟩⟩; dsimp [ψ]; rw [hi, Function.update_self]
          rw [this]; exact measurable_snd.snd
        · have : (fun pss : (Ω × Ω) × (S × S) =>
              (ψ pss.1.1 pss.1.2 pss.2).2 i) =
              fun pss => pss.1.2 i := by
            ext ⟨⟨σ, η⟩, ⟨s1, s2⟩⟩; dsimp [ψ]; rw [Function.update_of_ne hi]
          rw [this]; exact (measurable_pi_apply i).comp measurable_fst.snd
    -- g is jointly measurable: uncurry g = B.indicator 1 ∘ Ψ
    have hg_meas : Measurable (fun (pss : (Ω × Ω) × (S × S)) =>
        Set.indicator B (1 : Ω × Ω → ENNReal) (ψ pss.1.1 pss.1.2 pss.2)) :=
      (measurable_one.indicator hB).comp hΨ_meas
    -- Apply Measurable.lintegral_kernel_prod_right
    exact @Measurable.lintegral_kernel_prod_right (Ω × Ω) (S × S) _ _ κ_cmc _
      (fun p ss => Set.indicator B 1 (ψ p.1 p.2 ss)) hg_meas
  -- f p is a probability measure for each p
  have hf_prob : ∀ p : Ω × Ω, IsProbabilityMeasure (f p) := by
    intro p
    show IsProbabilityMeasure ((cmc p.1 p.2).map (ψ p.1 p.2))
    haveI := hcmc_prob p.1 p.2
    exact Measure.isProbabilityMeasure_map (hψ_meas p.1 p.2).aemeasurable
  -- Define Q = P.bind f
  let Q := P.bind f
  have hQ_prob : IsProbabilityMeasure Q := by
    constructor
    show (P.bind f) Set.univ = 1
    rw [Measure.bind_apply MeasurableSet.univ hf_meas.aemeasurable]
    simp_rw [show ∀ p, f p Set.univ = 1 from fun p => by
      haveI := hf_prob p; exact measure_univ]
    simp [measure_univ]
  -- Q{w-ne} for w ≠ z: determined by P{w-ne} since update doesn't change w-coords
  have h_preserve : ∀ w, w ≠ z → Q {p | p.1 w ≠ p.2 w} = P {p | p.1 w ≠ p.2 w} := by
    intro w hw
    show (P.bind f) {p | p.1 w ≠ p.2 w} = P {p | p.1 w ≠ p.2 w}
    rw [Measure.bind_apply (measurableSet_disagreement w) hf_meas.aemeasurable]
    -- f p {w-ne} = cmc.map(ψ) {w-ne} = cmc (ψ⁻¹'{w-ne})
    -- ψ⁻¹'{w-ne} = if p.1 w ≠ p.2 w then univ else ∅ (since ψ doesn't change w-coords)
    have hf_wne : ∀ p : Ω × Ω, f p {q | q.1 w ≠ q.2 w} =
        if p.1 w ≠ p.2 w then 1 else 0 := by
      intro p
      show (cmc p.1 p.2).map (ψ p.1 p.2) {q | q.1 w ≠ q.2 w} = _
      rw [Measure.map_apply (hψ_meas p.1 p.2) (measurableSet_disagreement w)]
      -- The preimage: since ψ doesn't change the w-coordinate (w ≠ z),
      -- the w-disagreement depends only on p.1 w vs p.2 w
      have hpre : ψ p.1 p.2 ⁻¹' {q : Ω × Ω | q.1 w ≠ q.2 w} =
          if p.1 w ≠ p.2 w then Set.univ else ∅ := by
        ext ⟨s1, s2⟩
        simp only [Set.mem_preimage, Set.mem_setOf_eq]
        dsimp [ψ]
        rw [Function.update_of_ne hw, Function.update_of_ne hw]
        split_ifs with h <;> simp [h]
      rw [hpre]
      split_ifs
      · haveI := hcmc_prob p.1 p.2; exact measure_univ
      · exact measure_empty
    simp_rw [hf_wne]
    rw [show (fun p : Ω × Ω => if p.1 w ≠ p.2 w then (1 : ENNReal) else 0) =
        Set.indicator {p | p.1 w ≠ p.2 w} 1 from by
      ext p; simp [Set.indicator_apply, Set.mem_setOf_eq]]
    exact lintegral_indicator_one (measurableSet_disagreement w)
  -- Q{z-ne}: contraction via coupling bound + influence coefficients
  have h_contract : (Q {p | p.1 z ≠ p.2 z}).toReal ≤
      ∑ w : I, influenceCoeff γ z w * (P {p | p.1 w ≠ p.2 w}).toReal := by
    -- Step 1: Q{z-ne} as lintegral
    have hQ_zne : Q {p | p.1 z ≠ p.2 z} =
        ∫⁻ p, f p {q | q.1 z ≠ q.2 z} ∂P := by
      show (P.bind f) _ = _
      exact Measure.bind_apply (measurableSet_disagreement z) hf_meas.aemeasurable
    -- Step 2: f p {z-ne} = cmc{s1 ≠ s2}
    have hf_zne : ∀ p : Ω × Ω, f p {q | q.1 z ≠ q.2 z} =
        cmc p.1 p.2 {ss | ss.1 ≠ ss.2} := by
      intro p
      show (cmc p.1 p.2).map (ψ p.1 p.2) {q | q.1 z ≠ q.2 z} = _
      rw [Measure.map_apply (hψ_meas p.1 p.2) (measurableSet_disagreement z)]
      congr 1; ext ⟨s1, s2⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq, ne_eq]
      dsimp [ψ]
      simp [Function.update_self]
    -- Step 3: Pointwise bound: cmc{≠}.toReal ≤ tvDist ≤ Σ C(z,w) indicator
    have h_ptwise : ∀ p : Ω × Ω,
        (cmc p.1 p.2 {ss | ss.1 ≠ ss.2}).toReal ≤
          ∑ w : I, influenceCoeff γ z w *
            (if p.1 w = p.2 w then (0 : ℝ) else 1) := by
      intro p
      exact (canonicalMaximalCoupling_compact_ne_le _ _).trans
        (tvDist_marginal_le_influenceCoeff_sum γ z p.1 p.2)
    -- Step 4: Pointwise ENNReal bound
    have h_ptwise_enn : ∀ p : Ω × Ω,
        f p {q | q.1 z ≠ q.2 z} ≤
          ENNReal.ofReal (∑ w : I, influenceCoeff γ z w *
            (if p.1 w = p.2 w then (0 : ℝ) else 1)) := by
      intro p; rw [hf_zne p]
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal (h_ptwise p)
    -- Step 5: Integrate and decompose
    have h_lint_le : ∫⁻ p, f p {q | q.1 z ≠ q.2 z} ∂P ≤
        ∑ w : I, ENNReal.ofReal (influenceCoeff γ z w) *
          P {p | p.1 w ≠ p.2 w} := by
      calc ∫⁻ p, f p {q | q.1 z ≠ q.2 z} ∂P
          ≤ ∫⁻ p, ENNReal.ofReal (∑ w : I, influenceCoeff γ z w *
              (if p.1 w = p.2 w then (0 : ℝ) else 1)) ∂P :=
            lintegral_mono h_ptwise_enn
        _ = ∫⁻ p, ∑ w : I, ENNReal.ofReal (influenceCoeff γ z w *
              (if p.1 w = p.2 w then (0 : ℝ) else 1)) ∂P := by
            congr 1; ext p
            exact ENNReal.ofReal_sum_of_nonneg (fun w _ =>
              mul_nonneg (influenceCoeff_nonneg γ z w) (by split_ifs <;> norm_num))
        _ = ∑ w : I, ∫⁻ p, ENNReal.ofReal (influenceCoeff γ z w *
              (if p.1 w = p.2 w then (0 : ℝ) else 1)) ∂P := by
            rw [lintegral_finset_sum _ (fun w _ => by
              -- p ↦ ofReal(C(z,w) * if p.1 w = p.2 w then 0 else 1) is measurable
              apply Measurable.ennreal_ofReal
              apply measurable_const.mul
              have h_agree_meas : MeasurableSet {p : Ω × Ω | p.1 w = p.2 w} := by
                have : {p : Ω × Ω | p.1 w = p.2 w} = {p | p.1 w ≠ p.2 w}ᶜ := by
                  ext p; simp
                rw [this]; exact (measurableSet_disagreement w).compl
              exact Measurable.ite h_agree_meas measurable_const measurable_const)]
        _ = ∑ w : I, ENNReal.ofReal (influenceCoeff γ z w) *
              P {p | p.1 w ≠ p.2 w} := by
            congr 1; ext w
            rw [show (fun p : Ω × Ω => ENNReal.ofReal (influenceCoeff γ z w *
                  (if p.1 w = p.2 w then (0 : ℝ) else 1))) =
                (fun p => ENNReal.ofReal (influenceCoeff γ z w) *
                  ENNReal.ofReal (if p.1 w = p.2 w then (0 : ℝ) else 1)) from
              funext fun p => ENNReal.ofReal_mul (influenceCoeff_nonneg γ z w)]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr 1
            rw [show (fun p : Ω × Ω =>
                ENNReal.ofReal (if p.1 w = p.2 w then (0 : ℝ) else 1)) =
                Set.indicator {p : Ω × Ω | p.1 w ≠ p.2 w} 1 from by
              ext p; simp only [Set.indicator, Set.mem_setOf_eq, ne_eq, Pi.one_apply]
              by_cases h : p.1 w = p.2 w
              · simp [h, ENNReal.ofReal_zero]
              · simp [h, ENNReal.ofReal_one]]
            exact lintegral_indicator_one (measurableSet_disagreement w)
    -- Step 6: Convert to .toReal
    have h_rhs_ne_top : ∑ w : I, ENNReal.ofReal (influenceCoeff γ z w) *
        P {p | p.1 w ≠ p.2 w} ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun w _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P _))
    rw [show (∑ w : I, influenceCoeff γ z w *
          (P {p | p.1 w ≠ p.2 w}).toReal) =
        (∑ w : I, ENNReal.ofReal (influenceCoeff γ z w) *
          P {p | p.1 w ≠ p.2 w}).toReal from by
      rw [ENNReal.toReal_sum (fun w _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P _))]
      congr 1; ext w
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (influenceCoeff_nonneg γ z w)]]
    exact (ENNReal.toReal_le_toReal (measure_ne_top Q _) h_rhs_ne_top).mpr
      (hQ_zne ▸ h_lint_le)
  -- IsCoupling: Q has the right marginals
  -- Step A: condDist {z} is Giry-measurable
  have hcond_meas : Measurable (γ.condDist ({z} : Finset I)) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hne_top : ∀ σ, γ.condDist {z} σ A ≠ ⊤ := fun σ =>
      (measure_lt_top (γ.condDist {z} σ) A).ne
    have heq : (fun σ => γ.condDist {z} σ A) =
        (fun σ => ENNReal.ofReal (γ.condDist {z} σ A).toReal) := by
      ext σ; exact (ENNReal.ofReal_toReal (hne_top σ)).symm
    rw [heq]
    exact ENNReal.measurable_ofReal.comp (γ.measurable_condDist {z} A hA)
  -- Step B: DLR in ENNReal form: ∫⁻ σ, condDist {z} σ A ∂μ = μ A
  -- Helper: convert .toReal DLR to ENNReal lintegral
  have dlr_toReal_to_enn (μ : Measure Ω) [IsProbabilityMeasure μ]
      (hdlr_tr : ∀ (A : Set Ω), MeasurableSet A →
        (μ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ) :
      ∀ (A : Set Ω), MeasurableSet A →
        ∫⁻ σ, (γ.condDist {z} σ) A ∂μ = μ A := by
    intro A hA
    have h_ae_lt : ∀ᵐ σ ∂μ, (γ.condDist {z} σ) A < ⊤ :=
      Filter.Eventually.of_forall (fun σ => measure_lt_top _ A)
    have h_meas : AEMeasurable (fun σ => (γ.condDist {z} σ) A) μ :=
      ((Measure.measurable_coe hA).comp hcond_meas).aemeasurable
    -- lintegral in .toReal form
    have h_lint_real : (∫⁻ σ, (γ.condDist {z} σ) A ∂μ).toReal =
        ∫ σ, (γ.condDist {z} σ A).toReal ∂μ :=
      (integral_toReal h_meas h_ae_lt).symm
    -- Both sides equal the same .toReal value
    have h_eq_real : (μ A).toReal = (∫⁻ σ, (γ.condDist {z} σ) A ∂μ).toReal := by
      rw [hdlr_tr A hA, h_lint_real]
    -- Both are finite
    have h_lint_ne_top : ∫⁻ σ, (γ.condDist {z} σ) A ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top (measure_ne_top μ Set.univ) (by
        calc ∫⁻ σ, (γ.condDist {z} σ) A ∂μ
            ≤ ∫⁻ σ, 1 ∂μ := lintegral_mono (fun σ => by
              calc (γ.condDist {z} σ) A ≤ (γ.condDist {z} σ) Set.univ :=
                    measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ)
          _ = μ Set.univ := lintegral_one)
    exact ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) h_lint_ne_top).mp
      h_eq_real).symm
  have hdlr_enn₁ := dlr_toReal_to_enn μ₁ hdlr₁
  have hdlr_enn₂ := dlr_toReal_to_enn μ₂ hdlr₂
  -- Step C: (f p).map Prod.fst = condDist {z} p.1
  have hf_fst : ∀ p : Ω × Ω, (f p).map Prod.fst = γ.condDist {z} p.1 := by
    intro p
    show ((cmc p.1 p.2).map (ψ p.1 p.2)).map Prod.fst = γ.condDist {z} p.1
    rw [Measure.map_map measurable_fst (hψ_meas p.1 p.2)]
    -- Prod.fst ∘ ψ p.1 p.2 = (fun ss => Function.update p.1 z ss.1)
    -- = (Function.update p.1 z) ∘ Prod.fst
    have hcomp : Prod.fst ∘ ψ p.1 p.2 = (Function.update p.1 z) ∘ Prod.fst := by
      ext ⟨s1, s2⟩; rfl
    rw [hcomp, ← Measure.map_map
      (measurable_pi_lambda _ (fun i => by
        by_cases h : i = z
        · subst h; simp only [Function.update_self]; exact measurable_id
        · simp only [Function.update_of_ne h]; exact measurable_const))
      measurable_fst]
    -- (cmc p.1 p.2).map fst = marginalAtSite (condDist {z} p.1) z
    rw [canonicalMaximalCoupling_compact_fst]
    -- (marginalAtSite (condDist {z} p.1) z).map (update p.1 z) = condDist {z} p.1
    exact (condDist_eq_marginal_map_update_compact γ z p.1).symm
  -- Step D: (f p).map Prod.snd = condDist {z} p.2
  have hf_snd : ∀ p : Ω × Ω, (f p).map Prod.snd = γ.condDist {z} p.2 := by
    intro p
    show ((cmc p.1 p.2).map (ψ p.1 p.2)).map Prod.snd = γ.condDist {z} p.2
    rw [Measure.map_map measurable_snd (hψ_meas p.1 p.2)]
    have hcomp : Prod.snd ∘ ψ p.1 p.2 = (Function.update p.2 z) ∘ Prod.snd := by
      ext ⟨s1, s2⟩; rfl
    rw [hcomp, ← Measure.map_map
      (measurable_pi_lambda _ (fun i => by
        by_cases h : i = z
        · subst h; simp only [Function.update_self]; exact measurable_id
        · simp only [Function.update_of_ne h]; exact measurable_const))
      measurable_snd]
    rw [canonicalMaximalCoupling_compact_snd]
    exact (condDist_eq_marginal_map_update_compact γ z p.2).symm
  -- Step E: Q.map fst/snd via bind
  have hbind_fst : ∀ (A : Set Ω), MeasurableSet A →
      (P.bind f).map Prod.fst A = ∫⁻ p, (γ.condDist {z} p.1) A ∂P := by
    intro A hA
    rw [Measure.map_apply measurable_fst hA,
        Measure.bind_apply (measurable_fst hA) hf_meas.aemeasurable]
    exact lintegral_congr (fun p => by
      rw [show f p (Prod.fst ⁻¹' A) = (f p).map Prod.fst A from
        (Measure.map_apply measurable_fst hA).symm, hf_fst])
  have hbind_snd : ∀ (A : Set Ω), MeasurableSet A →
      (P.bind f).map Prod.snd A = ∫⁻ p, (γ.condDist {z} p.2) A ∂P := by
    intro A hA
    rw [Measure.map_apply measurable_snd hA,
        Measure.bind_apply (measurable_snd hA) hf_meas.aemeasurable]
    exact lintegral_congr (fun p => by
      rw [show f p (Prod.snd ⁻¹' A) = (f p).map Prod.snd A from
        (Measure.map_apply measurable_snd hA).symm, hf_snd])
  -- Step F: Change of variables + DLR
  have hlint_fst : ∀ (A : Set Ω), MeasurableSet A →
      ∫⁻ p, (γ.condDist {z} p.1) A ∂P = μ₁ A := by
    intro A hA
    have hcov : ∫⁻ p, (γ.condDist {z} p.1) A ∂P =
        ∫⁻ σ, (γ.condDist {z} σ) A ∂(P.map Prod.fst) :=
      (lintegral_map ((Measure.measurable_coe hA).comp hcond_meas) measurable_fst).symm
    rw [hcov, hP.fst_marginal, hdlr_enn₁ A hA]
  have hlint_snd : ∀ (A : Set Ω), MeasurableSet A →
      ∫⁻ p, (γ.condDist {z} p.2) A ∂P = μ₂ A := by
    intro A hA
    have hcov : ∫⁻ p, (γ.condDist {z} p.2) A ∂P =
        ∫⁻ σ, (γ.condDist {z} σ) A ∂(P.map Prod.snd) :=
      (lintegral_map ((Measure.measurable_coe hA).comp hcond_meas) measurable_snd).symm
    rw [hcov, hP.snd_marginal, hdlr_enn₂ A hA]
  have hQ_coup : IsCoupling Q μ₁ μ₂ := by
    refine IsCoupling.mk (isProb := hQ_prob) (fst_marginal := ?_) (snd_marginal := ?_)
    · ext A hA; rw [hbind_fst A hA, hlint_fst A hA]
    · ext A hA; rw [hbind_snd A hA, hlint_snd A hA]
  -- Assemble
  exact ⟨Q, hQ_prob, hQ_coup, h_preserve, h_contract⟩

/-! ## Main theorem: eliminates dobrushin_coupling_axiom_compact -/

/-- **Prokhorov coupling theorem.** Proves the existence of a
minimum-disagreement coupling satisfying Dobrushin contraction,
eliminating the need for `dobrushin_coupling_axiom_compact`.

The proof combines Parts I–IV (compactness + lsc + minimizer existence)
with Part V (single-site improvement) via a minimality argument:
if the minimizer P failed the contraction at z, the improved Q would
have strictly smaller total disagreement, contradicting minimality. -/
theorem prokhorov_coupling_theorem
    (γ : GibbsSpec I S)
    (μ₁ μ₂ : Measure Ω)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (T : Set I)
    (hμ₁ : ∀ z ∈ T, ∀ (A : Set Ω),
      MeasurableSet A →
      (μ₁ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₁)
    (hμ₂ : ∀ z ∈ T, ∀ (A : Set Ω),
      MeasurableSet A →
      (μ₂ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₂)
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    ∃ (P : Measure (Ω × Ω))
      (_ : IsCoupling P μ₁ μ₂),
      ∀ z ∈ T,
        (P {p : Ω × Ω | p.1 z ≠ p.2 z}).toReal ≤
          ∑' w, influenceCoeff γ z w *
            (P {p : Ω × Ω | p.1 w ≠ p.2 w}).toReal := by
  -- Step 1: Get minimum-disagreement coupling from Parts I-IV.
  obtain ⟨ν_min, hν_min_mem, hν_min_opt⟩ := exists_min_disagreement_coupling μ₁ μ₂
  -- Extract the minimizer as a bare Measure
  set P := (ν_min : Measure (Ω × Ω)) with hP_def
  haveI hP_prob : IsProbabilityMeasure P := ν_min.prop
  have hP_coup : IsCoupling P μ₁ μ₂ :=
    { isProb := hP_prob, fst_marginal := hν_min_mem.1, snd_marginal := hν_min_mem.2 }
  -- Step 2: Prove contraction at each z ∈ T using the minimum property.
  refine ⟨P, hP_coup, fun z hz => ?_⟩
  -- Convert tsum to Finset.sum (all terms are zero outside Finset.univ for Fintype I)
  rw [tsum_eq_sum (s := Finset.univ) (fun w hw => absurd (Finset.mem_univ w) hw)]
  -- Step 3: Apply updateCoupling_compact_exists to get an improved coupling Q_z
  obtain ⟨Q_z, hQ_z_prob, hQ_z_coup, hQ_z_preserve, hQ_z_contract⟩ :=
    updateCoupling_compact_exists γ z μ₁ μ₂ P hP_coup
      (fun A hA => hμ₁ z hz A hA) (fun A hA => hμ₂ z hz A hA)
  -- Step 4: Q_z is in the CouplingSet, so D(P) ≤ D(Q_z) by minimality
  haveI := hQ_z_prob
  let ν_Qz : ProbabilityMeasure (Ω × Ω) := ⟨Q_z, hQ_z_prob⟩
  have hν_Qz_mem : ν_Qz ∈ CouplingSet μ₁ μ₂ :=
    ⟨hQ_z_coup.fst_marginal, hQ_z_coup.snd_marginal⟩
  have hD_le : totalDisagreement ν_min ≤ totalDisagreement ν_Qz := hν_min_opt ν_Qz hν_Qz_mem
  -- Step 5: Extract P{z-ne} ≤ Q_z{z-ne} from D(P) ≤ D(Q_z)
  -- Since Q_z preserves disagreement at all w ≠ z, the total disagreement
  -- difference is exactly Q_z{z-ne} - P{z-ne}.
  have h_nondecrease : (P {p | p.1 z ≠ p.2 z}).toReal ≤
      (Q_z {p | p.1 z ≠ p.2 z}).toReal := by
    -- D(ν_min) = Σ_w P{w-ne}.toReal
    -- D(ν_Qz) = Σ_w Q_z{w-ne}.toReal
    -- For w ≠ z: Q_z{w-ne} = P{w-ne} by preservation
    -- So D(ν_Qz) - D(ν_min) = Q_z{z-ne}.toReal - P{z-ne}.toReal
    unfold totalDisagreement at hD_le
    -- Decompose both sums: z-term + rest
    have hP_sum : ∑ w : I, ((ν_min : Measure (Ω × Ω)) {p | p.1 w ≠ p.2 w}).toReal =
        (P {p | p.1 z ≠ p.2 z}).toReal +
          ∑ w ∈ Finset.univ.erase z, (P {p | p.1 w ≠ p.2 w}).toReal := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z)]
    have hQz_coe : ∀ A, (ν_Qz : Measure (Ω × Ω)) A = Q_z A := fun _ => rfl
    have hQ_sum : ∑ w : I, ((ν_Qz : Measure (Ω × Ω)) {p | p.1 w ≠ p.2 w}).toReal =
        (Q_z {p | p.1 z ≠ p.2 z}).toReal +
          ∑ w ∈ Finset.univ.erase z, (Q_z {p | p.1 w ≠ p.2 w}).toReal := by
      simp_rw [hQz_coe]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z)]
    -- The rest-parts are equal by preservation
    have hrest_eq : ∑ w ∈ Finset.univ.erase z, (Q_z {p | p.1 w ≠ p.2 w}).toReal =
        ∑ w ∈ Finset.univ.erase z, (P {p | p.1 w ≠ p.2 w}).toReal := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [hQ_z_preserve w (Finset.ne_of_mem_erase hw)]
    rw [hP_sum, hQ_sum, hrest_eq] at hD_le
    linarith
  -- Step 6: Combine P{z-ne} ≤ Q_z{z-ne} ≤ Σ C(z,w) * P{w-ne}
  exact le_trans h_nondecrease hQ_z_contract

/-- Alias for backward compatibility. Previously an axiom in DobrushinCoupling.lean,
now proved via `prokhorov_coupling_theorem`. -/
theorem dobrushin_coupling_axiom_compact
    (γ : GibbsSpec I S)
    (μ₁ μ₂ : Measure Ω)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (T : Set I)
    (hμ₁ : ∀ z ∈ T, ∀ (A : Set Ω),
      MeasurableSet A →
      (μ₁ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₁)
    (hμ₂ : ∀ z ∈ T, ∀ (A : Set Ω),
      MeasurableSet A →
      (μ₂ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₂)
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    ∃ (P : Measure (Ω × Ω))
      (_ : IsCoupling P μ₁ μ₂),
      ∀ z ∈ T,
        (P {p : Ω × Ω | p.1 z ≠ p.2 z}).toReal ≤
          ∑' w, influenceCoeff γ z w *
            (P {p : Ω × Ω | p.1 w ≠ p.2 w}).toReal :=
  prokhorov_coupling_theorem γ μ₁ μ₂ T hμ₁ hμ₂ hfinsupp h_dep_F

end
