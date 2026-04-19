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

- `updateCoupling_isCoupling` -- 3 sub-sorries remain:
  DLR-to-bind conversion is PROVED; gap is measurability of the
  maximalCoupling-based kernel + bind/map properness trace.
- `dobrushinCouplingList_isCoupling` -- CLOSED (induction on Sorry 1)
- `dobrushinCoupling_contraction_at_site` -- foldl state tracking;
  requires showing later updates don't increase w-disagreement
  for the contraction at z

## References

- Dobrushin (1968), Lemma 2
- Georgii (1988), Proposition 8.7
-/

import MarkovSemigroups.Dobrushin.Specification
import MarkovSemigroups.Dobrushin.Uniqueness
import MarkovSemigroups.Coupling.TVCoupling

open MeasureTheory Finset Classical

noncomputable section

variable {I : Type*} [DecidableEq I] {S : Type*} [MeasurableSpace S]

/-! ## Definitions -/

/-- For site z and boundary pair (sigma, eta), produce the maximal coupling
of the z-marginals of `gamma.condDist {z} sigma` and `gamma.condDist {z} eta`.
-/
noncomputable def coupledSingleSiteKernel
    [MeasurableEq S]
    (γ : GibbsSpec I S) (z : I) (σ η : SpinConfig I S) : Measure (S × S) :=
  maximalCoupling (marginalAtSite (γ.condDist {z} σ) z)
                  (marginalAtSite (γ.condDist {z} η) z)

/-- Given a coupling P on (SpinConfig x SpinConfig) and a site z,
resample the z-coordinate of both copies using the coupled single-site
kernel. -/
noncomputable def updateCoupling
    [MeasurableEq S]
    (γ : GibbsSpec I S) (z : I)
    (P : Measure (SpinConfig I S × SpinConfig I S)) :
    Measure (SpinConfig I S × SpinConfig I S) :=
  P.bind (fun p =>
    (coupledSingleSiteKernel γ z p.1 p.2).map
      (fun ss => (Function.update p.1 z ss.1, Function.update p.2 z ss.2)))

/-- Iterate `updateCoupling` over all sites in a list. -/
noncomputable def dobrushinCouplingList
    [MeasurableEq S]
    (γ : GibbsSpec I S) (sites : List I)
    (P₀ : Measure (SpinConfig I S × SpinConfig I S)) :
    Measure (SpinConfig I S × SpinConfig I S) :=
  sites.foldl (fun P z => updateCoupling γ z P) P₀

/-- Iterate `updateCoupling` over all sites in a finset T (via its list). -/
noncomputable def dobrushinCoupling
    [MeasurableEq S]
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
theorem coupledSingleSiteKernel_ne_le [Fintype I] [MeasurableEq S]
    (γ : GibbsSpec I S) (z : I) (σ η : SpinConfig I S) :
    ((coupledSingleSiteKernel γ z σ η) {p | p.1 ≠ p.2}).toReal ≤
      ∑ w : I, influenceCoeff γ z w *
        (if σ w = η w then (0 : ℝ) else 1) := by
  classical
  have h_ne := maximalCoupling_ne
    (marginalAtSite (γ.condDist {z} σ) z)
    (marginalAtSite (γ.condDist {z} η) z)
  unfold coupledSingleSiteKernel at *
  rw [h_ne, ← tvDist_eq_tvNorm]
  exact tvDist_marginal_le_influenceCoeff_sum γ z σ η

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

/-- `updateCoupling` preserves the coupling property.

**Proved infrastructure:** The DLR `.toReal` → ENNReal bind conversion is
complete (`hcond_meas`, `hbind₁`, `hbind₂`).

**Remaining gap (3 sub-sorries):**
1. `IsProbabilityMeasure`: Requires measurability of the coupled kernel
   `fun p => (coupledSingleSiteKernel ...).map ψ` for `Measure.bind_apply`.
2. First marginal `= μ₁`: Requires bind/map decomposition + properness
   (`condDist {z} σ` supported on configs agreeing with σ outside {z})
   + DLR bind form.
3. Second marginal `= μ₂`: Symmetric to (2).

The mathematical argument is clear; the gap is purely the measurability
of the `maximalCoupling`-based kernel in its parameters. -/
theorem updateCoupling_isCoupling [MeasurableEq S]
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
  -- Step 3: The marginal conditions.
  -- updateCoupling γ z P = P.bind(fun p => (coupledSingleSiteKernel ...).map ψ)
  -- where ψ(ss) = (Function.update p.1 z ss.1, Function.update p.2 z ss.2).
  --
  -- First marginal of updateCoupling equals μ₁:
  --   (P.bind f).map Prod.fst = P.bind(fun p => (f p).map Prod.fst)
  --   = P.bind(fun p => (marginal of condDist at z, mapped to full config))
  --   = μ₁.bind(condDist {z})   [by coupling + properness]
  --   = μ₁                       [by DLR bind form]
  --
  -- Each step requires measurability conditions that are technically challenging.
  -- We construct the coupling directly.
  refine IsCoupling.mk (isProb := ?_) (fst_marginal := ?_) (snd_marginal := ?_)
  · -- IsProbabilityMeasure (updateCoupling γ z P)
    sorry
  · -- (updateCoupling γ z P).map Prod.fst = μ₁
    sorry
  · -- (updateCoupling γ z P).map Prod.snd = μ₂
    sorry

/-- `dobrushinCouplingList` preserves the coupling property. -/
theorem dobrushinCouplingList_isCoupling [MeasurableEq S]
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
theorem dobrushinCoupling_isCoupling [MeasurableEq S]
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

/-! ## Per-site contraction after sweep -/

/-- After the Dobrushin coupling sweep, the disagreement at each
site z in T satisfies the contraction inequality. -/
theorem dobrushinCoupling_contraction_at_site [Fintype I] [MeasurableEq S]
    (γ : GibbsSpec I S) (T : Finset I)
    (P₀ : Measure (SpinConfig I S × SpinConfig I S))
    [IsProbabilityMeasure P₀]
    (z : I) (_hz : z ∈ T) :
    ((dobrushinCoupling γ T P₀) {p | p.1 z ≠ p.2 z}).toReal ≤
      ∑ w : I, influenceCoeff γ z w *
        ((dobrushinCoupling γ T P₀) {p | p.1 w ≠ p.2 w}).toReal := by
  sorry

/-! ## Main theorem: the iterated coupling exists -/

/-- **Dobrushin iterated coupling (fintype version).**

For a Gibbs specification gamma on a finite site set I, and probability
measures mu_1, mu_2 satisfying DLR at sites in T, there exists a joint
coupling P such that:
1. P is a coupling of mu_1 and mu_2
2. For all z in T: P({sigma z != eta z}) <= sum_w C(z,w) * P({sigma w != eta w})

This provides a constructive witness for the axiom
`dobrushin_iterated_coupling_exists` in CondTVBridge.lean
(modulo the DLR-to-Giry conversion in `updateCoupling_isCoupling`). -/
theorem dobrushin_iterated_coupling_fintype [Fintype I]
    [MeasurableSingletonClass S] [MeasurableEq S]
    [MeasurableEq (SpinConfig I S)]
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
  -- Construct the coupling
  set P := dobrushinCoupling γ TF (μ₁.prod μ₂) with hP_def
  -- Show it's a coupling of mu_1 and mu_2
  have hP_coup : IsCoupling P μ₁ μ₂ :=
    dobrushinCoupling_isCoupling γ TF μ₁ μ₂ (μ₁.prod μ₂)
      (isCoupling_prod μ₁ μ₂)
      (fun z hz A hA => hdlr₁ z ((Finset.mem_filter.mp hz).2) A hA)
      (fun z hz A hA => hdlr₂ z ((Finset.mem_filter.mp hz).2) A hA)
  -- Show the contraction at each site
  refine ⟨P, hP_coup, fun z hz => ?_⟩
  have hz_mem : z ∈ TF :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩
  -- Get the Finset.sum contraction from dobrushinCoupling_contraction_at_site
  have h_contr := dobrushinCoupling_contraction_at_site γ TF (μ₁.prod μ₂) z hz_mem
  -- Convert Finset.sum to tsum (I is Fintype, so tsum = sum over univ)
  show (P {p | p.1 z ≠ p.2 z}).toReal ≤
    ∑' w, influenceCoeff γ z w * (P {p | p.1 w ≠ p.2 w}).toReal
  rw [tsum_eq_sum (s := Finset.univ) (fun w hw => absurd (Finset.mem_univ w) hw)]
  exact h_contr

end
