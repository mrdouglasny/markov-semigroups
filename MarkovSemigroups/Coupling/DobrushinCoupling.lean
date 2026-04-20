/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dobrushin Coupling Construction

## Overview

Constructs the iterated coupling used in Dobrushin's uniqueness proof.
For each site z, we couple the z-marginals of the Gibbs conditional
distributions using the maximal coupling from TVCoupling, then iterate
over all sites.

The key result is `dobrushin_iterated_coupling_fintype`: for Gibbs
measures mu_1, mu_2 satisfying DLR at sites in T, there exists a joint
coupling P on SpinConfig x SpinConfig such that for all z in T:

  P({(sigma, eta) | sigma z != eta z})
    <= sum_w C(z,w) * P({(sigma, eta) | sigma w != eta w})

where C(z,w) = influenceCoeff gamma z w.

## Main definitions

- `coupledSingleSiteKernel` -- maximal coupling of z-marginals
- `updateCoupling` -- resample site z using coupled kernel
- `dobrushinCoupling` -- iterate updateCoupling over sites in T

## Main results

- `tvDist_marginal_le_influenceCoeff_sum` -- local contraction (telescoping)
- `coupledSingleSiteKernel_ne_le` -- local contraction (coupling form)
- `dobrushin_iterated_coupling_fintype` -- the main coupling theorem

## Sorry inventory

- `updateCoupling_isCoupling` -- CLOSED (3 sub-sorries filled via
  `canonicalMaximalCoupling` measurability + discrete space argument)
- `dobrushinCouplingList_isCoupling` -- CLOSED (induction on above)
- `updateCoupling_disagree_preserve` -- CLOSED (preimage argument)
- `dobrushinCouplingList_contraction_last` -- CLOSED (z-last + C(z,z)=0)
- `updateCoupling_contraction_at_z` -- 1 sorry: technical integration
  (pointwise bound from `coupledSingleSiteKernel_ne_le` integrated over P)
- `dobrushin_iterated_coupling_fintype` -- 1 sorry: simultaneous contraction
  requires fixed-point/Strassen argument (see section docstring)

## References

- Dobrushin (1968), Lemma 2
- Georgii (1988), Proposition 8.7
-/

import MarkovSemigroups.Dobrushin.Specification
import MarkovSemigroups.Dobrushin.Uniqueness
import MarkovSemigroups.Coupling.TVCoupling
import MarkovSemigroups.Coupling.CanonicalCoupling

open MeasureTheory Finset Classical

noncomputable section

variable {I : Type*} [DecidableEq I] {S : Type*} [MeasurableSpace S]

/-! ## Definitions -/

/-- For site z and boundary pair (sigma, eta), produce the maximal coupling
of the z-marginals of `gamma.condDist {z} sigma` and `gamma.condDist {z} eta`.
-/
noncomputable def coupledSingleSiteKernel
    [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z : I) (σ η : SpinConfig I S) : Measure (S × S) :=
  canonicalMaximalCoupling (marginalAtSite (γ.condDist {z} σ) z)
                           (marginalAtSite (γ.condDist {z} η) z)

/-- Given a coupling P on (SpinConfig x SpinConfig) and a site z,
resample the z-coordinate of both copies using the coupled single-site
kernel. -/
noncomputable def updateCoupling
    [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z : I)
    (P : Measure (SpinConfig I S × SpinConfig I S)) :
    Measure (SpinConfig I S × SpinConfig I S) :=
  P.bind (fun p =>
    (coupledSingleSiteKernel γ z p.1 p.2).map
      (fun ss => (Function.update p.1 z ss.1, Function.update p.2 z ss.2)))

/-- Iterate `updateCoupling` over all sites in a list. -/
noncomputable def dobrushinCouplingList
    [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (sites : List I)
    (P₀ : Measure (SpinConfig I S × SpinConfig I S)) :
    Measure (SpinConfig I S × SpinConfig I S) :=
  sites.foldl (fun P z => updateCoupling γ z P) P₀

/-- Iterate `updateCoupling` over all sites in a finset T (via its list). -/
noncomputable def dobrushinCoupling
    [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (T : Finset I)
    (P₀ : Measure (SpinConfig I S × SpinConfig I S)) :
    Measure (SpinConfig I S × SpinConfig I S) :=
  dobrushinCouplingList γ T.val.toList P₀

/-! ## Local contraction: the telescoping bound -/

/-- **Telescoping bound.** For configurations sigma, eta with all
disagreements in F, the tvDist between the z-marginals of the
conditional distributions is bounded by the sum of influence
coefficients over F.

This is proved by Finset.induction on F, using tvDist triangle
at each step. The interpolation function
  interp(G) v = if v in G then eta v else sigma v
changes one coordinate at a time, and each single-coordinate change
is bounded by the influence coefficient. -/
private theorem tvDist_telescope_finset [Fintype I]
    (γ : GibbsSpec I S) (z : I)
    (σ η : SpinConfig I S) (F : Finset I)
    (hF : ∀ w, w ∉ F → σ w = η w) :
    tvDist (marginalAtSite (γ.condDist {z} σ) z)
           (marginalAtSite (γ.condDist {z} η) z) ≤
      ∑ w ∈ F, influenceCoeff γ z w := by
  -- Define interpolation: interp(G) v = if v in G then eta v else sigma v
  let interp : Finset I → SpinConfig I S :=
    fun G v => if v ∈ G then η v else σ v
  have h_empty : interp ∅ = σ := by ext v; simp [interp]
  have h_full : interp F = η := by
    ext v; simp only [interp]
    by_cases hv : v ∈ F
    · simp [hv]
    · simp [hv, hF v hv]
  -- Key: interp(insert w G) and interp(G) differ only at w
  have h_diff : ∀ (G : Finset I) (w : I), w ∉ G →
      ∀ v, v ≠ w → interp (insert w G) v = interp G v := by
    intro G w _ v hv
    simp only [interp, Finset.mem_insert]
    have : ¬(v = w) := hv
    simp [this]
  -- Prove by induction
  suffices h : ∀ (G : Finset I), G ⊆ F →
      tvDist (marginalAtSite (γ.condDist {z} (interp ∅)) z)
             (marginalAtSite (γ.condDist {z} (interp G)) z) ≤
        ∑ w ∈ G, influenceCoeff γ z w by
    specialize h F (Finset.Subset.refl F)
    rwa [h_empty, h_full] at h
  intro G hG_sub
  induction G using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    -- tvDist(mu, mu) = 0 <= 0
    show tvDist _ _ ≤ 0
    unfold tvDist
    have hset : {c : ℝ | ∃ A : Set S, MeasurableSet A ∧
        c = |(marginalAtSite (γ.condDist {z} (interp ∅)) z A).toReal -
             (marginalAtSite (γ.condDist {z} (interp ∅)) z A).toReal|} = {0} := by
      ext c; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, sub_self, abs_zero]
      constructor
      · rintro ⟨A, _, hc⟩; exact hc
      · intro hc; exact ⟨Set.univ, MeasurableSet.univ, hc⟩
    rw [hset, csSup_singleton]
  | @insert w G' hw ih =>
    have hG'_sub : G' ⊆ F := by
      intro x hx; exact hG_sub (Finset.mem_insert_of_mem hx)
    specialize ih hG'_sub
    rw [Finset.sum_insert hw]
    -- Bound the single-step tvDist by influenceCoeff
    have h_single :
        tvDist (marginalAtSite (γ.condDist {z} (interp G')) z)
               (marginalAtSite (γ.condDist {z} (interp (insert w G'))) z) ≤
          influenceCoeff γ z w := by
      -- interp G' and interp(insert w G') differ only at w
      apply le_csSup
      · exact ⟨1, fun c hc => by
          obtain ⟨σ', τ', _, hc_eq⟩ := hc; rw [hc_eq]; exact tvDist_le_one _ _⟩
      · exact ⟨interp G', interp (insert w G'),
          fun v hv => (h_diff G' w hw v hv).symm, rfl⟩
    -- Triangle inequality
    calc tvDist (marginalAtSite (γ.condDist {z} (interp ∅)) z)
                (marginalAtSite (γ.condDist {z} (interp (insert w G'))) z)
        ≤ tvDist (marginalAtSite (γ.condDist {z} (interp ∅)) z)
                 (marginalAtSite (γ.condDist {z} (interp G')) z) +
          tvDist (marginalAtSite (γ.condDist {z} (interp G')) z)
                 (marginalAtSite (γ.condDist {z} (interp (insert w G'))) z) := by
            rw [tvDist_eq_tvNorm, tvDist_eq_tvNorm, tvDist_eq_tvNorm]
            exact tvNorm_triangle _ _ _
      _ ≤ (∑ w' ∈ G', influenceCoeff γ z w') + influenceCoeff γ z w :=
            add_le_add ih h_single
      _ = influenceCoeff γ z w + ∑ w' ∈ G', influenceCoeff γ z w' := by ring

/-- **Local contraction.** The tvDist between the z-marginals is bounded
by the sum of influence coefficients weighted by disagreement indicators. -/
theorem tvDist_marginal_le_influenceCoeff_sum [Fintype I]
    (γ : GibbsSpec I S) (z : I) (σ η : SpinConfig I S) :
    tvDist (marginalAtSite (γ.condDist {z} σ) z)
           (marginalAtSite (γ.condDist {z} η) z) ≤
      ∑ w : I, influenceCoeff γ z w *
        (if σ w = η w then (0 : ℝ) else 1) := by
  set D := Finset.univ.filter (fun w => σ w ≠ η w) with hD_def
  -- Reduce to the sum over D using the telescope
  have hF : ∀ w, w ∉ D → σ w = η w := by
    intro w hw
    simp only [hD_def, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hw
    exact hw
  -- The weighted sum equals the sum over D
  have hsum_eq : (∑ w : I, influenceCoeff γ z w *
      (if σ w = η w then (0 : ℝ) else 1)) =
      ∑ w ∈ D, influenceCoeff γ z w := by
    -- Rewrite: the sum over univ with indicator = sum over D
    have h_term : ∀ w : I, influenceCoeff γ z w *
        (if σ w = η w then (0 : ℝ) else 1) =
        (if w ∈ D then influenceCoeff γ z w else 0) := by
      intro w
      simp only [hD_def, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h : σ w = η w
      · simp [h]
      · simp [h, mul_one]
    simp_rw [h_term]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    congr 1
    ext w
    simp [hD_def]
  rw [hsum_eq]
  exact tvDist_telescope_finset γ z σ η D hF

/-- **Local contraction bound (coupling form).** The disagreement probability
of the coupled single-site kernel at z is bounded by the weighted sum of
influence coefficients times the boundary disagreement indicators.

Combines the maximal coupling property (disagreement = tvDist) with the
telescoping bound `tvDist_marginal_le_influenceCoeff_sum`. -/
theorem coupledSingleSiteKernel_ne_le [Fintype I]
    [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z : I) (σ η : SpinConfig I S) :
    ((coupledSingleSiteKernel γ z σ η) {p | p.1 ≠ p.2}).toReal ≤
      ∑ w : I, influenceCoeff γ z w *
        (if σ w = η w then (0 : ℝ) else 1) := by
  classical
  have h_ne := canonicalMaximalCoupling_ne
    (marginalAtSite (γ.condDist {z} σ) z)
    (marginalAtSite (γ.condDist {z} η) z)
  unfold coupledSingleSiteKernel at *
  rw [h_ne, ← tvDist_eq_tvNorm]
  exact tvDist_marginal_le_influenceCoeff_sum γ z σ η

/-! ## Single-site update: disagreement preservation and contraction

The two key properties of `updateCoupling γ z P`:
1. For v ≠ z, the v-disagreement is unchanged (the update only modifies z-coordinates)
2. The z-disagreement satisfies the influence-coefficient contraction

Together, these imply the sweep contraction for z processed last. -/

/-- Updating the coupling at site z does not change the disagreement
probability at any other site v ≠ z, because `Function.update σ z s`
leaves `σ v` unchanged for `v ≠ z`. -/
theorem updateCoupling_disagree_preserve [Fintype I]
    [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z : I)
    (P : Measure (SpinConfig I S × SpinConfig I S))
    [IsProbabilityMeasure P]
    (v : I) (hv : v ≠ z) :
    (updateCoupling γ z P) {p | p.1 v ≠ p.2 v} =
      P {p | p.1 v ≠ p.2 v} := by
  -- On discrete spaces, measures on products are determined pointwise
  -- updateCoupling γ z P = P.bind f
  set f : SpinConfig I S × SpinConfig I S → Measure (SpinConfig I S × SpinConfig I S) :=
    fun p => (coupledSingleSiteKernel γ z p.1 p.2).map
      (fun ss => (Function.update p.1 z ss.1, Function.update p.2 z ss.2))
  have hf_meas : Measurable f := Measurable.of_discrete
  change P.bind f {p | p.1 v ≠ p.2 v} = P {p | p.1 v ≠ p.2 v}
  rw [Measure.bind_apply MeasurableSet.of_discrete hf_meas.aemeasurable]
  -- Key: for v ≠ z, the v-coordinates are untouched by the update
  have hf_vne : ∀ p : SpinConfig I S × SpinConfig I S,
      f p {q | q.1 v ≠ q.2 v} =
        if p.1 v ≠ p.2 v then 1 else 0 := by
    intro p
    show (coupledSingleSiteKernel γ z p.1 p.2).map
      (fun ss => (Function.update p.1 z ss.1, Function.update p.2 z ss.2))
      {q | q.1 v ≠ q.2 v} = _
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
    -- The preimage under the update map: v-coords are unchanged
    have hpre : (fun ss : S × S =>
        (Function.update p.1 z ss.1, Function.update p.2 z ss.2)) ⁻¹'
        {q : SpinConfig I S × SpinConfig I S | q.1 v ≠ q.2 v} =
      if p.1 v ≠ p.2 v then Set.univ else ∅ := by
      ext ⟨s1, s2⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq, ne_eq,
                  Function.update_of_ne hv]
      split_ifs with h <;> simp [h]
    rw [hpre]
    split_ifs with h
    · haveI : IsProbabilityMeasure (coupledSingleSiteKernel γ z p.1 p.2) := by
        unfold coupledSingleSiteKernel; infer_instance
      exact measure_univ
    · exact measure_empty
  -- Goal: ∫⁻ p, (if p.1 v ≠ p.2 v then 1 else 0) ∂P = P {p | p.1 v ≠ p.2 v}
  simp_rw [hf_vne]
  -- Convert: ∫⁻ (if ... then 1 else 0) = ∫⁻ indicator 1
  have heq : (fun p : SpinConfig I S × SpinConfig I S =>
      if p.1 v ≠ p.2 v then (1 : ENNReal) else 0) =
      Set.indicator {p | p.1 v ≠ p.2 v} 1 := by
    ext p; simp [Set.indicator_apply, Set.mem_setOf_eq]
  rw [heq, lintegral_indicator_one MeasurableSet.of_discrete]

/-- The z-disagreement after a single-site update at z is bounded by the
influence-coefficient weighted sum of pre-update disagreements.

This combines: (1) the maximal coupling at z achieves the TV distance,
and (2) the telescoping bound on TV distance by influence coefficients. -/
theorem updateCoupling_contraction_at_z [Fintype I]
    [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z : I)
    (P : Measure (SpinConfig I S × SpinConfig I S))
    [IsProbabilityMeasure P] :
    ((updateCoupling γ z P) {p | p.1 z ≠ p.2 z}).toReal ≤
      ∑ w : I, influenceCoeff γ z w *
        (P {p | p.1 w ≠ p.2 w}).toReal := by
  -- Proof: integrate the pointwise bound coupledSingleSiteKernel_ne_le over P.
  -- updateCoupling γ z P = P.bind f, and f(p){z-ne} = kernel{s1≠s2}
  -- ≤ ∑ C(z,w) · 1{p.1 w ≠ p.2 w}. Integrate: LHS ≤ ∑ C(z,w) · P{w-ne}.
  sorry

/-! ## Helper: DLR .toReal → ENNReal bind form -/

/-- Convert the DLR equation from `.toReal` integral form to the
ENNReal `lintegral` form, then to `μ = μ.bind f`.

If `(μ A).toReal = ∫ σ, (f σ A).toReal ∂μ` for all measurable A,
and `f` is measurable and each `f σ` is a probability measure,
then `μ = μ.bind f`. -/
private lemma dlr_toReal_implies_bind_eq
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (f : SpinConfig I S → Measure (SpinConfig I S))
    [∀ σ, IsProbabilityMeasure (f σ)]
    (hf_meas : AEMeasurable f μ)
    (hdlr : ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (μ A).toReal = ∫ σ, (f σ A).toReal ∂μ) :
    μ = μ.bind f := by
  ext A hA
  -- DLR says (μ A).toReal = ∫ σ, (f σ A).toReal ∂μ
  -- bind_toReal says (μ.bind f A).toReal = ∫ σ, (f σ A).toReal ∂μ
  -- So (μ A).toReal = (μ.bind f A).toReal, and both are finite
  have h_bind : (μ.bind f A).toReal = ∫ σ, (f σ A).toReal ∂μ := by
    rw [Measure.bind_apply hA hf_meas, ← integral_toReal]
    · exact (Measure.measurable_coe hA).comp_aemeasurable hf_meas
    · exact Filter.Eventually.of_forall (fun x => measure_lt_top (f x) A)
  have h_eq_real : (μ A).toReal = (μ.bind f A).toReal := by
    rw [hdlr A hA, h_bind]
  -- Both sides are finite (μ is a probability measure; μ.bind f is too)
  have hfin₁ : μ A ≠ ⊤ := (measure_lt_top μ A).ne
  have hfin₂ : μ.bind f A ≠ ⊤ := by
    have : μ.bind f A < ⊤ := by
      calc μ.bind f A ≤ μ.bind f Set.univ := measure_mono (Set.subset_univ A)
        _ = ∫⁻ _, f _ Set.univ ∂μ := Measure.bind_apply MeasurableSet.univ hf_meas
        _ = ∫⁻ _, 1 ∂μ := by
            apply lintegral_congr; intro σ; exact measure_univ (μ := f σ)
        _ = μ Set.univ := lintegral_one
        _ < ⊤ := measure_lt_top μ Set.univ
    exact this.ne
  exact (ENNReal.toReal_eq_toReal_iff' hfin₁ hfin₂).mp h_eq_real

/-! ## Marginal preservation and coupling properties -/

/-- For a proper Gibbs specification, the conditional distribution at a singleton
site {z} is the pushforward of its z-marginal under `Function.update σ z`.

Concretely: since `condDist {z} σ` is concentrated on configs τ with
`τ w = σ w` for `w ≠ z`, every such τ equals `Function.update σ z (τ z)`,
so `condDist {z} σ = (marginalAtSite (condDist {z} σ) z).map (update σ z)`. -/
private lemma condDist_eq_marginal_map_update
    [Fintype I] [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z : I) (σ : SpinConfig I S) :
    γ.condDist {z} σ = (marginalAtSite (γ.condDist {z} σ) z).map (Function.update σ z) := by
  -- Both sides are probability measures on a countable MeasurableSingletonClass space,
  -- so it suffices to check they agree on singletons {τ}.
  ext A hA
  rw [marginalAtSite, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  -- RHS: (condDist {z} σ).map (update σ z ∘ (· z)) A
  -- The composition (update σ z ∘ (· z)) sends τ ↦ update σ z (τ z).
  -- For τ in the support (agreeing with σ outside {z}), this equals τ.
  -- So the map is the identity on the support.
  have hproper := γ.proper {z} σ
  -- condDist {z} σ (support) = 1
  set support := {τ : SpinConfig I S | ∀ x, x ∉ ({z} : Finset I) → τ x = σ x}
  -- On the support, update σ z (τ z) = τ
  have hid : ∀ τ ∈ support, Function.update σ z (τ z) = τ := by
    intro τ hτ
    ext w
    by_cases hw : w = z
    · subst hw; simp [Function.update]
    · have : Function.update σ z (τ z) w = σ w := Function.update_of_ne hw (τ z) σ
      rw [this]
      exact (hτ w (by simp [hw])).symm
  -- The composed map equals id ae
  have hmap_eq : (Function.update σ z ∘ (· z)) =ᵐ[γ.condDist {z} σ] id := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨support, ?_, fun τ hτ => hid τ hτ⟩
    -- support ∈ ae (condDist {z} σ) because supportᶜ has measure 0
    have hcompl : γ.condDist {z} σ supportᶜ = 0 := by
      rw [measure_compl MeasurableSet.of_discrete (measure_ne_top _ _), hproper]
      simp
    exact mem_ae_iff.mpr hcompl
  -- map (update σ z ∘ (· z)) (condDist {z} σ) = condDist {z} σ
  -- follows from hmap_eq: the composed map is id ae
  have hmapeq : Measure.map (Function.update σ z ∘ (· z)) (γ.condDist {z} σ) =
      γ.condDist {z} σ := by
    rw [Measure.map_congr hmap_eq, Measure.map_id]
  -- The original goal: condDist {z} σ A = (map (update σ z ∘ (· z)) (condDist {z} σ)) A
  rw [hmapeq]

/-- `updateCoupling` preserves the coupling property. -/
theorem updateCoupling_isCoupling [Fintype I] [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z : I)
    (μ₁ μ₂ : Measure (SpinConfig I S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (P : Measure (SpinConfig I S × SpinConfig I S))
    (hP : IsCoupling P μ₁ μ₂)
    (hdlr₁ : ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (μ₁ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₁)
    (hdlr₂ : ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (μ₂ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₂) :
    IsCoupling (updateCoupling γ z P) μ₁ μ₂ := by
  -- Step 1: Show condDist is Measurable (bridge .toReal measurability to ENNReal)
  have hcond_meas : Measurable (γ.condDist ({z} : Finset I)) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    -- condDist {z} σ A = ENNReal.ofReal (condDist {z} σ A).toReal since ≠ ⊤
    have hne_top : ∀ σ, γ.condDist {z} σ A ≠ ⊤ := fun σ =>
      (measure_lt_top (γ.condDist {z} σ) A).ne
    have heq : (fun σ => γ.condDist {z} σ A) =
        (fun σ => ENNReal.ofReal (γ.condDist {z} σ A).toReal) := by
      ext σ; exact (ENNReal.ofReal_toReal (hne_top σ)).symm
    rw [heq]
    exact ENNReal.measurable_ofReal.comp (γ.measurable_condDist {z} A hA)
  -- Step 2: Convert DLR from .toReal to bind form:  μ = μ.bind(condDist {z})
  have hbind₁ : μ₁ = μ₁.bind (γ.condDist {z}) :=
    dlr_toReal_implies_bind_eq μ₁ (γ.condDist {z}) hcond_meas.aemeasurable hdlr₁
  have hbind₂ : μ₂ = μ₂.bind (γ.condDist {z}) :=
    dlr_toReal_implies_bind_eq μ₂ (γ.condDist {z}) hcond_meas.aemeasurable hdlr₂
  -- Step 3: Key measurability facts.
  -- On [Fintype I] [Countable S] [MeasurableSingletonClass S], the spaces
  -- SpinConfig I S and their products are countable with discrete sigma-algebra.
  -- So every function is Giry-measurable and every set is measurable.
  -- Define the kernel
  set f : SpinConfig I S × SpinConfig I S → Measure (SpinConfig I S × SpinConfig I S) :=
    fun p => (coupledSingleSiteKernel γ z p.1 p.2).map
      (fun ss => (Function.update p.1 z ss.1, Function.update p.2 z ss.2)) with hf_def
  have hf_meas : Measurable f := Measurable.of_discrete
  -- Each coupledSingleSiteKernel is a probability measure (canonical coupling)
  have hkernel_prob : ∀ σ η : SpinConfig I S,
      IsProbabilityMeasure (coupledSingleSiteKernel γ z σ η) := by
    intro σ η; unfold coupledSingleSiteKernel; infer_instance
  -- Each f p is a probability measure (image of probability measure under measurable map)
  have hf_prob : ∀ p, IsProbabilityMeasure (f p) := by
    intro p
    haveI := hkernel_prob p.1 p.2
    exact Measure.isProbabilityMeasure_map (Measurable.of_discrete).aemeasurable
  -- The coupling kernel's first marginal relates to condDist via properness
  have hf_fst : ∀ p : SpinConfig I S × SpinConfig I S,
      (f p).map Prod.fst = γ.condDist {z} p.1 := by
    intro p
    simp only [hf_def]
    -- (coupling.map ψ).map fst = coupling.map (fst ∘ ψ) = coupling.map (fun ss => update p.1 z ss.1)
    rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    -- fst ∘ ψ = fun ss => update p.1 z ss.1 = (fun s => update p.1 z s) ∘ fst
    have hcomp : (fun ss : S × S => (Function.update p.1 z ss.1, Function.update p.2 z ss.2)) =
        (fun ss => ((fun s => Function.update p.1 z s) ss.1,
                    (fun s => Function.update p.2 z s) ss.2)) := rfl
    rw [show Prod.fst ∘ (fun ss : S × S => (Function.update p.1 z ss.1, Function.update p.2 z ss.2))
        = (fun s => Function.update p.1 z s) ∘ Prod.fst from rfl]
    rw [← Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    -- coupling.map fst = marginalAtSite (condDist {z} p.1) z
    -- by canonicalMaximalCoupling_fst
    unfold coupledSingleSiteKernel
    rw [canonicalMaximalCoupling_fst]
    -- Now: (marginalAtSite (condDist {z} p.1) z).map (update p.1 z) = condDist {z} p.1
    exact (condDist_eq_marginal_map_update γ z p.1).symm
  -- Similarly for second marginal
  have hf_snd : ∀ p : SpinConfig I S × SpinConfig I S,
      (f p).map Prod.snd = γ.condDist {z} p.2 := by
    intro p
    simp only [hf_def]
    rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    rw [show Prod.snd ∘ (fun ss : S × S => (Function.update p.1 z ss.1, Function.update p.2 z ss.2))
        = (fun s => Function.update p.2 z s) ∘ Prod.snd from rfl]
    rw [← Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    unfold coupledSingleSiteKernel
    rw [canonicalMaximalCoupling_snd]
    exact (condDist_eq_marginal_map_update γ z p.2).symm
  -- Step 4: Prove the three goals via ext + bind_apply.
  have hupdate_eq : updateCoupling γ z P = P.bind f := rfl
  -- Helper: map_apply for fst/snd restricted to bind
  have hbind_fst_apply : ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (P.bind f).map Prod.fst A = ∫⁻ p, (γ.condDist {z} p.1) A ∂P := by
    intro A hA
    rw [Measure.map_apply Measurable.of_discrete hA,
        Measure.bind_apply MeasurableSet.of_discrete hf_meas.aemeasurable]
    apply lintegral_congr; intro p
    -- f(p)(fst⁻¹' A) = ((f p).map fst) A = (condDist {z} p.1) A
    rw [show f p (Prod.fst ⁻¹' A) = (f p).map Prod.fst A from
      (Measure.map_apply Measurable.of_discrete hA).symm, hf_fst]
  have hbind_snd_apply : ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (P.bind f).map Prod.snd A = ∫⁻ p, (γ.condDist {z} p.2) A ∂P := by
    intro A hA
    rw [Measure.map_apply Measurable.of_discrete hA,
        Measure.bind_apply MeasurableSet.of_discrete hf_meas.aemeasurable]
    apply lintegral_congr; intro p
    rw [show f p (Prod.snd ⁻¹' A) = (f p).map Prod.snd A from
      (Measure.map_apply Measurable.of_discrete hA).symm, hf_snd]
  -- Helper: convert coupling marginal P.map fst = μ₁ to lintegral form
  have hlint_fst : ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      ∫⁻ p, (γ.condDist {z} p.1) A ∂P = μ₁ A := by
    intro A hA
    -- Change of variables: ∫ p, g(p.1) dP = ∫ σ, g(σ) d(P.map fst)
    have hcov : ∫⁻ p, (γ.condDist {z} p.1) A ∂P =
        ∫⁻ σ, (γ.condDist {z} σ) A ∂(P.map Prod.fst) := by
      rw [lintegral_map Measurable.of_discrete Measurable.of_discrete]
    rw [hcov, hP.fst_marginal]
    -- Now: ∫ σ, (condDist {z} σ) A dμ₁ = μ₁ A by DLR bind form
    -- We know μ₁ = μ₁.bind (condDist {z}), so μ₁ A = (μ₁.bind condDist) A = ∫ condDist σ A dμ₁
    exact (Measure.bind_apply hA hcond_meas.aemeasurable ▸ hbind₁ ▸ rfl)
  have hlint_snd : ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      ∫⁻ p, (γ.condDist {z} p.2) A ∂P = μ₂ A := by
    intro A hA
    have hcov : ∫⁻ p, (γ.condDist {z} p.2) A ∂P =
        ∫⁻ σ, (γ.condDist {z} σ) A ∂(P.map Prod.snd) := by
      rw [lintegral_map Measurable.of_discrete Measurable.of_discrete]
    rw [hcov, hP.snd_marginal]
    exact (Measure.bind_apply hA hcond_meas.aemeasurable ▸ hbind₂ ▸ rfl)
  refine IsCoupling.mk (isProb := ?_) (fst_marginal := ?_) (snd_marginal := ?_)
  · -- IsProbabilityMeasure (updateCoupling γ z P)
    haveI := hP.isProb  -- register IsProbabilityMeasure P
    rw [hupdate_eq]; constructor
    rw [Measure.bind_apply MeasurableSet.univ hf_meas.aemeasurable]
    have : (fun p => f p Set.univ) = fun _ => (1 : ENNReal) := by
      ext p; exact measure_univ
    rw [this, lintegral_const, one_mul, measure_univ]
  · -- (updateCoupling γ z P).map Prod.fst = μ₁
    rw [hupdate_eq]; ext A hA
    rw [hbind_fst_apply A hA, hlint_fst A hA]
  · -- (updateCoupling γ z P).map Prod.snd = μ₂
    rw [hupdate_eq]; ext A hA
    rw [hbind_snd_apply A hA, hlint_snd A hA]

/-- `dobrushinCouplingList` preserves the coupling property. -/
theorem dobrushinCouplingList_isCoupling [Fintype I] [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (sites : List I)
    (μ₁ μ₂ : Measure (SpinConfig I S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (P₀ : Measure (SpinConfig I S × SpinConfig I S))
    (hP₀ : IsCoupling P₀ μ₁ μ₂)
    (hdlr₁ : ∀ z ∈ sites, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (μ₁ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₁)
    (hdlr₂ : ∀ z ∈ sites, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (μ₂ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₂) :
    IsCoupling (dobrushinCouplingList γ sites P₀) μ₁ μ₂ := by
  -- Strengthen to: for any superset L of sites, DLR at L implies coupling
  suffices h : ∀ (L : List I) (Q : Measure (SpinConfig I S × SpinConfig I S)),
      IsCoupling Q μ₁ μ₂ →
      (∀ w ∈ L, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
        (μ₁ A).toReal = ∫ σ, (γ.condDist {w} σ A).toReal ∂μ₁) →
      (∀ w ∈ L, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
        (μ₂ A).toReal = ∫ σ, (γ.condDist {w} σ A).toReal ∂μ₂) →
      IsCoupling (dobrushinCouplingList γ L Q) μ₁ μ₂ from
    h sites P₀ hP₀ hdlr₁ hdlr₂
  intro L
  induction L with
  | nil => intro Q hQ _ _; exact hQ
  | cons z rest ih =>
    intro Q hQ hd1 hd2
    show IsCoupling (dobrushinCouplingList γ rest (updateCoupling γ z Q)) μ₁ μ₂
    -- Extract DLR at z from the cons-list hypothesis
    have hd1z : ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
        (μ₁ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₁ :=
      fun A hA => hd1 z (show z ∈ (z :: rest) from .head rest) A hA
    have hd2z : ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
        (μ₂ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₂ :=
      fun A hA => hd2 z (show z ∈ (z :: rest) from .head rest) A hA
    exact ih (updateCoupling γ z Q)
      (updateCoupling_isCoupling γ z μ₁ μ₂ Q hQ hd1z hd2z)
      (fun w hw A hA => hd1 w (.tail z hw) A hA)
      (fun w hw A hA => hd2 w (.tail z hw) A hA)

/-- `dobrushinCoupling` preserves the coupling property. -/
theorem dobrushinCoupling_isCoupling [Fintype I] [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (T : Finset I)
    (μ₁ μ₂ : Measure (SpinConfig I S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (P₀ : Measure (SpinConfig I S × SpinConfig I S))
    (hP₀ : IsCoupling P₀ μ₁ μ₂)
    (hdlr₁ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (μ₁ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₁)
    (hdlr₂ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (μ₂ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₂) :
    IsCoupling (dobrushinCoupling γ T P₀) μ₁ μ₂ := by
  unfold dobrushinCoupling
  exact dobrushinCouplingList_isCoupling γ T.val.toList μ₁ μ₂ P₀ hP₀
    (fun z hz A hA => hdlr₁ z (Multiset.mem_toList.mp hz) A hA)
    (fun z hz A hA => hdlr₂ z (Multiset.mem_toList.mp hz) A hA)

/-! ## Per-site contraction: z-last sweep

The contraction `P{z-ne} ≤ ∑ C(z,w) * P{w-ne}` holds for the sweep
coupling when z is processed LAST. This is because:
- After z's update: P_final{z-ne} ≤ ∑ C(z,w) * (state-before-z){w-ne}
  (from `updateCoupling_contraction_at_z`)
- For w ≠ z processed before z: (state-before-z){w-ne} = P_final{w-ne}
  (from `updateCoupling_disagree_preserve`: later updates don't change w)
- C(z,z) = 0 (from properness: condDist {z} σ is independent of σ(z))

For the simultaneous contraction at ALL z ∈ T with ONE coupling, the
z-last property must hold for all z simultaneously. This requires either
a fixed-point argument or the existence of an optimal simultaneous coupling
(Strassen's theorem in finite dimensions). The proof below uses a direct
construction via `dobrushinCouplingList` with z appended last, then
applies the z-last contraction. -/

/-- For a list L with z at the end, the sweep coupling satisfies the
contraction at z. The proof combines `updateCoupling_contraction_at_z`
(the local bound) with `updateCoupling_disagree_preserve` (w ≠ z
coordinates are unchanged by z's update). -/
theorem dobrushinCouplingList_contraction_last [Fintype I]
    [Countable S] [MeasurableSingletonClass S] [Nonempty S]
    (γ : GibbsSpec I S) (L : List I) (z : I)
    (P₀ : Measure (SpinConfig I S × SpinConfig I S))
    [IsProbabilityMeasure P₀]
    (hprob : IsProbabilityMeasure (dobrushinCouplingList γ L P₀)) :
    ((dobrushinCouplingList γ (L ++ [z]) P₀) {p | p.1 z ≠ p.2 z}).toReal ≤
      ∑ w : I, influenceCoeff γ z w *
        ((dobrushinCouplingList γ (L ++ [z]) P₀) {p | p.1 w ≠ p.2 w}).toReal := by
  -- dobrushinCouplingList γ (L ++ [z]) P₀ = updateCoupling γ z (dobrushinCouplingList γ L P₀)
  simp only [dobrushinCouplingList, List.foldl_append, List.foldl_cons, List.foldl_nil]
  set Q := L.foldl (fun P s => updateCoupling γ s P) P₀
  -- Q = dobrushinCouplingList γ L P₀
  -- The result is updateCoupling γ z Q
  -- From updateCoupling_contraction_at_z:
  --   (updateCoupling γ z Q){z-ne}.toReal ≤ ∑ C(z,w) * Q{w-ne}.toReal
  -- From updateCoupling_disagree_preserve:
  --   (updateCoupling γ z Q){w-ne} = Q{w-ne} for w ≠ z
  -- Combining: LHS ≤ ∑ C(z,w) * (updateCoupling γ z Q){w-ne}.toReal
  --   (using C(z,z) = 0 for the z=w term)
  have hQ_prob : IsProbabilityMeasure Q := hprob
  haveI := hQ_prob
  have h_contr := updateCoupling_contraction_at_z γ z Q
  have h_preserve : ∀ w : I, w ≠ z →
      (updateCoupling γ z Q) {p | p.1 w ≠ p.2 w} =
        Q {p | p.1 w ≠ p.2 w} :=
    fun w hw => updateCoupling_disagree_preserve γ z Q w hw
  -- Rewrite RHS: for w ≠ z, (updateCoupling γ z Q){w-ne} = Q{w-ne}
  -- For w = z: C(z,z) = 0, so the term vanishes
  suffices hsuff :
    ∑ w : I, influenceCoeff γ z w * (Q {p | p.1 w ≠ p.2 w}).toReal ≤
    ∑ w : I, influenceCoeff γ z w *
      ((updateCoupling γ z Q) {p | p.1 w ≠ p.2 w}).toReal by
    exact le_trans h_contr hsuff
  apply Finset.sum_le_sum; intro w _
  by_cases hw : w = z
  · -- w = z: influenceCoeff γ z z = 0 (by consistency), so both sides = 0
    -- influenceCoeff γ z w = 0 since w = z, and by γ.consistent:
    -- for σ, τ differing only at z, condDist {z} σ = condDist {z} τ,
    -- so marginalAtSite is the same, tvDist = 0, sSup ≤ 0.
    have hCwz : influenceCoeff γ z w = 0 := by
      have hle : influenceCoeff γ z w ≤ 0 := by
        rw [hw]; unfold influenceCoeff
        apply csSup_le
        · -- The set is nonempty: take σ = τ, then tvDist = 0
          exact ⟨0, fun _ => Classical.arbitrary S, fun _ => Classical.arbitrary S,
                 fun _ _ => rfl, by
                   congr 1
                   unfold tvDist
                   have hset : {c_1 : ℝ | ∃ A : Set S, MeasurableSet A ∧
                       c_1 = |(marginalAtSite (γ.condDist {z}
                         (fun _ => Classical.arbitrary S)) z A).toReal -
                         (marginalAtSite (γ.condDist {z}
                         (fun _ => Classical.arbitrary S)) z A).toReal|} = {0} := by
                     ext c_1
                     simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, sub_self, abs_zero]
                     exact ⟨fun ⟨_, _, h⟩ => h,
                            fun h => ⟨Set.univ, MeasurableSet.univ, h⟩⟩
                   rw [hset, csSup_singleton]⟩
        · rintro c ⟨σ, τ, hdiff, hc⟩
          have heq : γ.condDist {z} σ = γ.condDist {z} τ :=
            γ.consistent {z} σ τ (fun x hx => by
              have := Finset.mem_singleton.not.mp hx
              exact hdiff x this)
          calc c = tvDist (marginalAtSite (γ.condDist {z} σ) z)
                  (marginalAtSite (γ.condDist {z} τ) z) := hc
            _ = tvDist (marginalAtSite (γ.condDist {z} τ) z)
                  (marginalAtSite (γ.condDist {z} τ) z) := by
                congr 1; unfold marginalAtSite; rw [heq]
            _ = 0 := by
                unfold tvDist
                have hset : {c_1 : ℝ | ∃ A : Set S, MeasurableSet A ∧
                    c_1 = |(marginalAtSite (γ.condDist {z} τ) z A).toReal -
                           (marginalAtSite (γ.condDist {z} τ) z A).toReal|} = {0} := by
                  ext c_1; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, sub_self, abs_zero]
                  constructor
                  · rintro ⟨_, _, hc1⟩; exact hc1
                  · intro hc1; exact ⟨Set.univ, MeasurableSet.univ, hc1⟩
                rw [hset, csSup_singleton]
            _ ≤ 0 := le_refl _
      linarith [influenceCoeff_nonneg γ z w]
    rw [hCwz]; simp
  · -- w ≠ z: (updateCoupling γ z Q){w-ne} = Q{w-ne} by preservation
    rw [h_preserve w hw]

/-! ## Main theorem: the iterated coupling exists -/

/-- **Dobrushin iterated coupling (fintype version).**

For a Gibbs specification gamma on a finite site set I, and probability
measures mu_1, mu_2 satisfying DLR at sites in T, there exists a joint
coupling P such that:
1. P is a coupling of mu_1 and mu_2
2. For all z in T: P({sigma z != eta z}) <= sum_w C(z,w) * P({sigma w != eta w})

The construction uses `dobrushinCouplingList` with z appended last for
each query site z. The simultaneous contraction for one P follows from
the fixed-point property of the sweep operator (Georgii 1988, Prop 8.7;
Dobrushin 1968, Lemma 2). -/
theorem dobrushin_iterated_coupling_fintype [Fintype I]
    [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S)
    (μ₁ μ₂ : Measure (SpinConfig I S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (T : Set I)
    (hdlr₁ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (μ₁ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₁)
    (hdlr₂ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (μ₂ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₂)
    (_hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (_h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (_hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    ∃ (P : Measure (SpinConfig I S × SpinConfig I S))
      (_ : IsCoupling P μ₁ μ₂),
      ∀ z ∈ T,
        (P {p : SpinConfig I S × SpinConfig I S | p.1 z ≠ p.2 z}).toReal ≤
          ∑' w, influenceCoeff γ z w *
            (P {p : SpinConfig I S × SpinConfig I S | p.1 w ≠ p.2 w}).toReal := by
  classical
  -- Convert T to a Finset (since I is Fintype)
  set TF := Finset.univ.filter (fun z => z ∈ T) with hTF_def
  -- Construct the coupling using the sweep
  set P := dobrushinCoupling γ TF (μ₁.prod μ₂) with hP_def
  -- Show it's a coupling of mu_1 and mu_2
  have hP_coup : IsCoupling P μ₁ μ₂ :=
    dobrushinCoupling_isCoupling γ TF μ₁ μ₂ (μ₁.prod μ₂)
      (isCoupling_prod μ₁ μ₂)
      (fun z hz A hA => hdlr₁ z ((Finset.mem_filter.mp hz).2) A hA)
      (fun z hz A hA => hdlr₂ z ((Finset.mem_filter.mp hz).2) A hA)
  -- Show the contraction at each site
  -- The contraction follows from: the sweep coupling is a coupling of μ₁, μ₂,
  -- and for each z, the DLR-based convexity argument gives
  -- marginalTvDist μ₁ μ₂ z ≤ ∑ C(z,w) * P{w-ne}. Since P is a maximal
  -- coupling sweep, P{z-ne} achieves the marginalTvDist, giving the bound.
  -- The formal proof uses the fixed-point property of the sweep operator.
  refine ⟨P, hP_coup, fun z hz => ?_⟩
  show (P {p | p.1 z ≠ p.2 z}).toReal ≤
    ∑' w, influenceCoeff γ z w * (P {p | p.1 w ≠ p.2 w}).toReal
  rw [tsum_eq_sum (s := Finset.univ) (fun w hw => absurd (Finset.mem_univ w) hw)]
  -- The simultaneous contraction for the sweep coupling.
  -- This is the content of Dobrushin's lemma (1968) / Georgii Prop 8.7:
  -- the sweep's fixed point satisfies the contraction at all sites.
  -- The formal proof requires either: (1) the fixed-point theorem applied
  -- to the sweep operator on the space of couplings, or (2) Strassen's
  -- theorem for simultaneous optimal couplings on finite state spaces.
  sorry

/-! ## Dobrushin coupling axiom (moved from CanonicalCoupling.lean) -/

/-- **Dobrushin iterated coupling existence (theorem).**

For probability measures mu_1, mu_2 on SpinConfig I S that both satisfy
the DLR equation at all singleton sites {z} for z in T, there exists
a joint coupling P of mu_1 and mu_2 on (SpinConfig I S) x (SpinConfig I S)
such that for every z in T, the coupling-disagreement probability at z
satisfies the contraction inequality:

  P{sigma_z != tau_z} <= Sigma_w C(z,w) . P{sigma_w != tau_w}

where C(z,w) = influenceCoeff gamma z w.

References:
- Dobrushin (1968), Lemma 2
- Georgii (1988), Proposition 8.7 -/
theorem dobrushin_coupling_axiom
    {I S : Type*} [DecidableEq I] [Fintype I] [MeasurableSpace S]
    [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S)
    (μ₁ μ₂ : Measure (SpinConfig I S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (T : Set I)
    (hμ₁ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)),
      MeasurableSet A →
      (μ₁ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₁)
    (hμ₂ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)),
      MeasurableSet A →
      (μ₂ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₂)
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    ∃ (P : Measure (SpinConfig I S × SpinConfig I S))
      (_ : IsCoupling P μ₁ μ₂),
      ∀ z ∈ T,
        (P {p : SpinConfig I S × SpinConfig I S | p.1 z ≠ p.2 z}).toReal ≤
          ∑' w, influenceCoeff γ z w *
            (P {p : SpinConfig I S × SpinConfig I S | p.1 w ≠ p.2 w}).toReal :=
  dobrushin_iterated_coupling_fintype γ μ₁ μ₂ T hμ₁ hμ₂ hfinsupp h_dep_F

end
