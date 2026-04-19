/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Coupling Characterization of Total Variation Distance

## Overview

The total variation distance between two probability measures μ and ν
on a measurable space (X, F) satisfies:

  tvDist(μ, ν) = inf { P(σ ≠ τ) : P is a coupling of μ, ν }

A **coupling** of μ and ν is a probability measure P on X × X whose
marginals are μ and ν respectively.

The infimum is attained by the **maximal coupling**, which couples
the measures identically on their overlap and independently on
the residual.

## Main results

- `IsCoupling` — P is a coupling of μ, ν (marginal conditions)
- `tvDist_le_coupling` — lower bound: tvDist ≤ P(σ ≠ τ) for any coupling
- `maximal_coupling` — construction of the optimal coupling
- `tvDist_eq_inf_coupling` — coupling characterization of TV distance

## References

- Lindvall, *Lectures on the Coupling Method*, Wiley, 1992
- Levin, Peres, Wilmer, *Markov Chains and Mixing Times*, AMS, 2009, Ch 4
- Villani, *Optimal Transport*, Springer, 2009, Ch 1

## Mathlib contribution notes

This fills a gap: Mathlib has no coupling theory as of April 2026.
The coupling characterization is fundamental for:
- Dobrushin uniqueness (lattice spin systems)
- Markov chain convergence bounds
- Strassen's theorem
- Wasserstein distances
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

open MeasureTheory Set

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-! ## Couplings -/

/-- A coupling of two probability measures μ and ν on X is a
probability measure P on X × X whose marginals are μ and ν. -/
structure IsCoupling (P : Measure (X × X)) (μ ν : Measure X) where
  /-- P is a probability measure. -/
  [isProb : IsProbabilityMeasure P]
  /-- First marginal is μ. -/
  fst_marginal : P.map Prod.fst = μ
  /-- Second marginal is ν. -/
  snd_marginal : P.map Prod.snd = ν

/-- The product coupling: independent draws from μ and ν. -/
theorem isCoupling_prod (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    IsCoupling (μ.prod ν) μ ν where
  fst_marginal := by rw [Measure.map_fst_prod, measure_univ, one_smul]
  snd_marginal := by rw [Measure.map_snd_prod, measure_univ, one_smul]

/-! ## Total variation distance -/

/-- Total variation distance between probability measures.
Defined as sup_A |μ(A) - ν(A)| over measurable sets.

This is equivalent to (1/2)·‖μ - ν‖_TV but we use the
probability convention (range [0,1] instead of [0,2]). -/
def tvNorm (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : ℝ :=
  sSup {c : ℝ | ∃ A : Set X, MeasurableSet A ∧
    c = |(μ A).toReal - (ν A).toReal|}

/-! ## Lower bound: tvDist ≤ P(σ ≠ τ) -/

/-- For any coupling P of μ, ν and measurable A:
μ(A) - ν(A) ≤ P(σ ∈ A, τ ∉ A) ≤ P(σ ≠ τ). -/
theorem measure_sub_le_coupling_ne (P : Measure (X × X))
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hP : IsCoupling P μ ν)
    (A : Set X) (hA : MeasurableSet A) :
    (μ A).toReal - (ν A).toReal ≤
      (P {p : X × X | p.1 ≠ p.2}).toReal := by
  have hPprob := hP.isProb
  -- Rewrite μ(A) and ν(A) using marginal conditions
  have hμA : μ A = P (Prod.fst ⁻¹' A) := by
    rw [← hP.fst_marginal, Measure.map_apply measurable_fst hA]
  have hνA : ν A = P (Prod.snd ⁻¹' A) := by
    rw [← hP.snd_marginal, Measure.map_apply measurable_snd hA]
  -- Key set inclusion: {p | p.1 ∈ A ∧ p.2 ∉ A} ⊆ {p | p.1 ≠ p.2}
  have hsubset : (Prod.fst ⁻¹' A) \ (Prod.snd ⁻¹' A) ⊆ {p : X × X | p.1 ≠ p.2} := by
    intro p ⟨hp1, hp2⟩
    simp only [mem_preimage] at hp1 hp2
    simp only [mem_setOf_eq]
    intro heq
    exact hp2 (heq ▸ hp1)
  -- P(fst ⁻¹' A) - P(snd ⁻¹' A) ≤ P(fst ⁻¹' A \ snd ⁻¹' A) at ENNReal level
  have hdiff_le : P (Prod.fst ⁻¹' A) - P (Prod.snd ⁻¹' A) ≤
      P ((Prod.fst ⁻¹' A) \ (Prod.snd ⁻¹' A)) := by
    apply tsub_le_iff_right.mpr
    calc P (Prod.fst ⁻¹' A)
        ≤ P ((Prod.fst ⁻¹' A \ Prod.snd ⁻¹' A) ∪ Prod.snd ⁻¹' A) := by
          apply measure_mono; intro p hp; simp only [mem_union, mem_diff]; tauto
      _ ≤ P (Prod.fst ⁻¹' A \ Prod.snd ⁻¹' A) + P (Prod.snd ⁻¹' A) :=
          measure_union_le _ _
  -- Chain with the subset bound
  have hne_le : P ((Prod.fst ⁻¹' A) \ (Prod.snd ⁻¹' A)) ≤ P {p | p.1 ≠ p.2} :=
    measure_mono hsubset
  -- Combine at ENNReal level
  have henn : P (Prod.fst ⁻¹' A) - P (Prod.snd ⁻¹' A) ≤ P {p | p.1 ≠ p.2} :=
    le_trans hdiff_le hne_le
  -- Transfer to ℝ: a.toReal - b.toReal ≤ (a - b).toReal when b ≤ a... no.
  -- Actually we need: a.toReal - b.toReal ≤ c.toReal when a - b ≤ c (ENNReal)
  -- Since a.toReal - b.toReal ≤ (a - b).toReal (when b ≤ a) or ≤ 0 (when a ≤ b)
  rw [hμA, hνA]
  by_cases hab : P (Prod.snd ⁻¹' A) ≤ P (Prod.fst ⁻¹' A)
  · rw [← ENNReal.toReal_sub_of_le hab (measure_ne_top P _)]
    have hsub_le : P (Prod.fst ⁻¹' A) - P (Prod.snd ⁻¹' A) ≤ P {p | p.1 ≠ p.2} :=
      le_trans hdiff_le hne_le
    exact (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top (measure_ne_top P _) hsub_le) (measure_ne_top P _)).mpr hsub_le
  · push Not at hab
    have h1 : (P (Prod.fst ⁻¹' A)).toReal ≤ (P (Prod.snd ⁻¹' A)).toReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top P _) (measure_ne_top P _)).mpr (le_of_lt hab)
    linarith [@ENNReal.toReal_nonneg (P {p | p.1 ≠ p.2})]

/-- **Lower bound.** For any coupling P of μ, ν:
tvNorm(μ, ν) ≤ P(σ ≠ τ).

Proof: For any measurable A,
  μ(A) - ν(A) = P(fst ∈ A) - P(snd ∈ A)
              = P(fst ∈ A, snd ∈ A) + P(fst ∈ A, snd ∉ A)
              - P(fst ∈ A, snd ∈ A) - P(fst ∉ A, snd ∈ A)
              = P(fst ∈ A, snd ∉ A) - P(fst ∉ A, snd ∈ A)
              ≤ P(fst ∈ A, snd ∉ A)
              ≤ P(fst ≠ snd)
Take sup over A to get tvNorm ≤ P(fst ≠ snd). -/
theorem tvNorm_le_coupling (P : Measure (X × X))
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hP : IsCoupling P μ ν) :
    tvNorm μ ν ≤ (P {p : X × X | p.1 ≠ p.2}).toReal := by
  have hPprob := hP.isProb
  unfold tvNorm
  apply csSup_le
  -- Nonemptiness: use A = ∅
  · exact ⟨0, ∅, MeasurableSet.empty, by simp⟩
  -- Each element is bounded
  · rintro c ⟨A, hA, rfl⟩
    -- Need: |μ(A).toReal - ν(A).toReal| ≤ P(≠).toReal
    apply abs_le.mpr
    constructor
    · -- -(P(≠).toReal) ≤ μ(A) - ν(A), i.e., ν(A) - μ(A) ≤ P(≠)
      -- Apply measure_sub_le_coupling_ne to Aᶜ
      have hAc := measure_sub_le_coupling_ne P μ ν hP Aᶜ hA.compl
      -- μ(Aᶜ).toReal = 1 - μ(A).toReal
      have hμc : (μ Aᶜ).toReal = 1 - (μ A).toReal := by
        rw [prob_compl_eq_one_sub hA]
        exact ENNReal.toReal_sub_of_le (prob_le_one (s := A)) (by simp)
      -- ν(Aᶜ).toReal = 1 - ν(A).toReal
      have hνc : (ν Aᶜ).toReal = 1 - (ν A).toReal := by
        rw [prob_compl_eq_one_sub hA]
        exact ENNReal.toReal_sub_of_le (prob_le_one (s := A)) (by simp)
      linarith
    · -- μ(A) - ν(A) ≤ P(≠)
      exact measure_sub_le_coupling_ne P μ ν hP A hA

/-! ## Hahn decomposition and tvNorm -/

/-- The tvNorm equals ν(s) - μ(s) where s is the Hahn set (on which μ ≤ ν). -/
theorem tvNorm_eq_of_hahn (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set X} (hs : MeasurableSet s)
    (h_le_on_s : ∀ t, MeasurableSet t → t ⊆ s → μ t ≤ ν t)
    (h_le_on_sc : ∀ t, MeasurableSet t → t ⊆ sᶜ → ν t ≤ μ t) :
    tvNorm μ ν = (ν s).toReal - (μ s).toReal := by
  unfold tvNorm
  -- Helper: decompose measures of sets using measurable s and measurable A
  have decompose_real (m : Measure X) [IsFiniteMeasure m] (A : Set X) (_hA : MeasurableSet A) :
      (m A).toReal = (m (A ∩ s)).toReal + (m (A ∩ sᶜ)).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top m _) (measure_ne_top m _)]
    congr 1; rw [← diff_eq]; exact (measure_inter_add_diff A hs).symm
  have decompose_s (m : Measure X) [IsFiniteMeasure m] (A : Set X) (hA : MeasurableSet A) :
      (m s).toReal = (m (A ∩ s)).toReal + (m (Aᶜ ∩ s)).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top m _) (measure_ne_top m _)]
    congr 1
    rw [inter_comm A s, inter_comm Aᶜ s, ← diff_eq]
    exact (measure_inter_add_diff s hA).symm
  have decompose_sc (m : Measure X) [IsFiniteMeasure m] (A : Set X) (hA : MeasurableSet A) :
      (m sᶜ).toReal = (m (A ∩ sᶜ)).toReal + (m (Aᶜ ∩ sᶜ)).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top m _) (measure_ne_top m _)]
    congr 1
    rw [inter_comm A sᶜ, inter_comm Aᶜ sᶜ, ← diff_eq]
    exact (measure_inter_add_diff sᶜ hA).symm
  apply le_antisymm
  · -- sSup ≤ ν(s) - μ(s): every |μ(A) - ν(A)| ≤ ν(s) - μ(s)
    apply csSup_le
    · exact ⟨0, ∅, MeasurableSet.empty, by simp⟩
    rintro c ⟨A, hA, rfl⟩
    -- Hahn bounds on A's pieces:
    have hAs : (μ (A ∩ s)).toReal ≤ (ν (A ∩ s)).toReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top ν _)).mpr
        (h_le_on_s _ (hA.inter hs) inter_subset_right)
    have hAsc : (ν (A ∩ sᶜ)).toReal ≤ (μ (A ∩ sᶜ)).toReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top ν _) (measure_ne_top μ _)).mpr
        (h_le_on_sc _ (hA.inter hs.compl) inter_subset_right)
    have hAcs : (μ (Aᶜ ∩ s)).toReal ≤ (ν (Aᶜ ∩ s)).toReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top ν _)).mpr
        (h_le_on_s _ (hA.compl.inter hs) inter_subset_right)
    have hAcsc : (ν (Aᶜ ∩ sᶜ)).toReal ≤ (μ (Aᶜ ∩ sᶜ)).toReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top ν _) (measure_ne_top μ _)).mpr
        (h_le_on_sc _ (hA.compl.inter hs.compl) inter_subset_right)
    have hμA := decompose_real μ A hA
    have hνA := decompose_real ν A hA
    have hμs := decompose_s μ A hA
    have hνs := decompose_s ν A hA
    have hμsc := decompose_sc μ A hA
    have hνsc' := decompose_sc ν A hA
    -- Total mass = 1 for probability measures
    have hμ1 : (μ s).toReal + (μ sᶜ).toReal = 1 := by
      rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
          measure_add_measure_compl hs]; simp
    have hν1 : (ν s).toReal + (ν sᶜ).toReal = 1 := by
      rw [← ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _),
          measure_add_measure_compl hs]; simp
    rw [abs_le]
    constructor <;> linarith
  · -- ν(s) - μ(s) ≤ sSup: it's achieved by A = s
    apply le_csSup
    · -- bdd_above
      refine ⟨1, fun c ⟨A, _, hc⟩ => ?_⟩
      subst hc
      have h1 : (μ A).toReal ≤ 1 :=
        ENNReal.toReal_le_of_le_ofReal one_pos.le (by simp [prob_le_one])
      have h2 : (ν A).toReal ≤ 1 :=
        ENNReal.toReal_le_of_le_ofReal one_pos.le (by simp [prob_le_one])
      have h3 : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
      have h4 : 0 ≤ (ν A).toReal := ENNReal.toReal_nonneg
      rw [abs_le]; constructor <;> linarith
    · refine ⟨s, hs, ?_⟩
      have hle : (μ s).toReal ≤ (ν s).toReal :=
        (ENNReal.toReal_le_toReal (measure_ne_top μ s) (measure_ne_top ν s)).mpr
          (h_le_on_s s hs Subset.rfl)
      rw [abs_of_nonpos (by linarith)]
      linarith

/-! ## Maximal coupling construction -/

/-- The overlap measure: the minimum of μ and ν.
  γ(A) = inf_B (μ(A ∩ B) + ν(A ∩ Bᶜ))
In terms of densities: if μ = f·λ and ν = g·λ, then γ = min(f,g)·λ.

The total mass γ(X) = 1 - tvNorm(μ, ν) is the "overlap" between μ and ν. -/
def overlapMeasure (μ ν : Measure X) : Measure X :=
  μ ⊓ ν

/-- The overlap measure has total mass 1 - tvNorm(μ, ν). -/
theorem overlapMeasure_mass (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (overlapMeasure μ ν Set.univ).toReal = 1 - tvNorm μ ν := by
  -- Get Hahn decomposition: on s, μ ≤ ν; on sᶜ, ν ≤ μ
  obtain ⟨s, hs, h_le_on_s, h_le_on_sc⟩ := hahn_decomposition ν μ
  -- Unfold overlapMeasure to inf_apply
  unfold overlapMeasure
  rw [Measure.inf_apply MeasurableSet.univ]
  simp_rw [inter_univ]
  -- Show the sInf equals μ(s) + ν(sᶜ) (attained at the Hahn set)
  have h_inf_eq : sInf {m | ∃ t, m = μ t + ν tᶜ} = μ s + ν sᶜ := by
    apply le_antisymm
    · exact csInf_le ⟨0, fun m ⟨t, ht⟩ => ht ▸ zero_le _⟩ ⟨s, rfl⟩
    · apply le_csInf
      · exact ⟨μ s + ν sᶜ, s, rfl⟩
      rintro m ⟨t, rfl⟩
      -- For any t, find measurable A ⊇ t with μ A = μ t and ν A = ν t.
      obtain ⟨A, htA, hAm, hμA, hνA⟩ := exists_measurable_superset₂ μ ν t
      -- Step 1: μ(s) + ν(sᶜ) ≤ μ(A) + ν(Aᶜ) using Hahn on measurable sets
      have h_hahn_bound : μ s + ν sᶜ ≤ μ A + ν Aᶜ := by
        -- Hahn bounds:
        have h1 : μ (s \ A) ≤ ν (s \ A) := h_le_on_s _ (hs.diff hAm) diff_subset
        have h2 : ν (sᶜ ∩ A) ≤ μ (sᶜ ∩ A) :=
          h_le_on_sc _ (hs.compl.inter hAm) inter_subset_left
        -- Decompose: μ(s) = μ(s∩A) + μ(s\A), ν(sᶜ) = ν(sᶜ∩A) + ν(sᶜ\A)
        -- μ(A) = μ(A∩s) + μ(A\s), ν(Aᶜ) = ν(Aᶜ∩s) + ν(Aᶜ\s)
        -- s∩A = A∩s, s\A = Aᶜ∩s rewritten, A\s = sᶜ∩A, sᶜ\A = Aᶜ∩sᶜ = Aᶜ\s
        -- So μ(s) + ν(sᶜ) = μ(s∩A) + μ(s\A) + ν(sᶜ∩A) + ν(sᶜ\A)
        -- and μ(A) + ν(Aᶜ) = μ(s∩A) + μ(sᶜ∩A) + ν(s\A) + ν(sᶜ\A)
        -- (using set identities and s∩A = A∩s, sᶜ\A = Aᶜ\s)
        -- Diff: μ(s\A) + ν(sᶜ∩A) vs ν(s\A) + μ(sᶜ∩A) by key
        calc μ s + ν sᶜ
            = (μ (s ∩ A) + μ (s \ A)) + (ν (sᶜ ∩ A) + ν (sᶜ \ A)) := by
              rw [measure_inter_add_diff s hAm, measure_inter_add_diff sᶜ hAm]
          _ = μ (s ∩ A) + ν (sᶜ \ A) + (μ (s \ A) + ν (sᶜ ∩ A)) := by
              abel
          _ ≤ μ (s ∩ A) + ν (sᶜ \ A) + (ν (s \ A) + μ (sᶜ ∩ A)) := by
              gcongr
          _ = (μ (s ∩ A) + μ (sᶜ ∩ A)) + (ν (s \ A) + ν (sᶜ \ A)) := by
              abel
          _ = (μ (A ∩ s) + μ (A \ s)) + (ν (Aᶜ ∩ s) + ν (Aᶜ \ s)) := by
              -- s∩A = A∩s, sᶜ∩A = A∩sᶜ = A\s
              rw [inter_comm s A, show sᶜ ∩ A = A \ s from by ext; simp [mem_diff]; tauto,
                  show s \ A = Aᶜ ∩ s from by ext; simp [mem_diff]; tauto,
                  show sᶜ \ A = Aᶜ \ s from by ext; simp [mem_diff]; tauto]
          _ = μ A + ν Aᶜ := by
              rw [measure_inter_add_diff A hs, measure_inter_add_diff Aᶜ hs]
      -- Step 2: μ(A) + ν(Aᶜ) ≤ μ(t) + ν(tᶜ)
      calc μ s + ν sᶜ
          ≤ μ A + ν Aᶜ := h_hahn_bound
        _ ≤ μ t + ν tᶜ := add_le_add (hμA ▸ le_refl _)
            (measure_mono (Set.compl_subset_compl.mpr htA))
  -- Now convert from ENNReal to ℝ
  rw [h_inf_eq]
  rw [ENNReal.toReal_add (measure_ne_top μ s) (measure_ne_top ν sᶜ)]
  have hνsc : (ν sᶜ).toReal = 1 - (ν s).toReal := by
    rw [prob_compl_eq_one_sub hs]
    exact ENNReal.toReal_sub_of_le (prob_le_one (s := s)) (by simp)
  rw [hνsc]
  -- Goal: μ(s).toReal + (1 - ν(s).toReal) = 1 - tvNorm μ ν
  linarith [tvNorm_eq_of_hahn μ ν hs h_le_on_s h_le_on_sc]

/-- The residual measure of μ after removing the overlap. -/
def residualMeasure (μ ν : Measure X) : Measure X :=
  μ - overlapMeasure μ ν

/-- **Maximal coupling construction.**

The maximal coupling P of μ and ν is defined as:

  P = γ · diag + (1/(1-γ(X)))² · (μ-γ) ⊗ (ν-γ)

where γ = overlap(μ, ν), diag is the diagonal measure, and
(μ-γ), (ν-γ) are the residual measures (normalized).

On the overlap (mass = 1-tvDist), σ = τ with probability 1.
On the residual (mass = tvDist), σ and τ are independent draws
from the normalized residuals.

Total disagreement: P(σ ≠ τ) = tvDist(μ, ν). -/
theorem exists_maximal_coupling (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [MeasurableEq X] :
    ∃ P : Measure (X × X),
      IsCoupling P μ ν ∧
      (P {p : X × X | p.1 ≠ p.2}).toReal = tvNorm μ ν := by
  -- Obtain the Hahn decomposition: on s, μ ≤ ν; on sᶜ, ν ≤ μ
  obtain ⟨s, hs, h_le_on_s, h_le_on_sc⟩ := hahn_decomposition ν μ
  -- Define the diagonal embedding
  let diag : X → X × X := fun x => (x, x)
  have hdiag : Measurable diag := Measurable.prodMk measurable_id measurable_id
  -- Define residual measures
  set β := ν.restrict s - μ.restrict s with hβ_def -- excess of ν on s
  set γ := μ.restrict sᶜ - ν.restrict sᶜ with hγ_def -- excess of μ on sᶜ
  -- Hahn bounds as measure inequalities on restricted measures
  have hμs_le_νs : μ.restrict s ≤ ν.restrict s := by
    rw [Measure.le_iff]
    intro A hA
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
    exact h_le_on_s _ (hA.inter hs) inter_subset_right
  have hνsc_le_μsc : ν.restrict sᶜ ≤ μ.restrict sᶜ := by
    rw [Measure.le_iff]
    intro A hA
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
    exact h_le_on_sc _ (hA.inter hs.compl) inter_subset_right
  -- Key: β and γ add back to give the full measures
  have hβ_add : β + μ.restrict s = ν.restrict s :=
    Measure.sub_add_cancel_of_le hμs_le_νs
  have hγ_add : γ + ν.restrict sᶜ = μ.restrict sᶜ :=
    Measure.sub_add_cancel_of_le hνsc_le_μsc
  -- Total masses of β and γ
  have hβ_mass : β Set.univ = ν s - μ s := by
    rw [hβ_def, Measure.sub_apply MeasurableSet.univ hμs_le_νs]
    simp [Measure.restrict_apply MeasurableSet.univ]
  have hγ_mass : γ Set.univ = μ sᶜ - ν sᶜ := by
    rw [hγ_def, Measure.sub_apply MeasurableSet.univ hνsc_le_μsc]
    simp [Measure.restrict_apply MeasurableSet.univ]
  -- β and γ have the same total mass
  have hμs_le_νs' := h_le_on_s s hs Subset.rfl
  have hνsc_le_μsc' := h_le_on_sc sᶜ hs.compl Subset.rfl
  have hβγ_mass : β Set.univ = γ Set.univ := by
    rw [hβ_mass, hγ_mass]
    -- Need: ν s - μ s = μ sᶜ - ν sᶜ
    -- We show both, when added to (μ s + ν sᶜ), give 1
    have hfin : μ s + ν sᶜ ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨measure_ne_top μ s, measure_ne_top ν sᶜ⟩
    rw [← ENNReal.add_left_inj hfin]
    calc (ν s - μ s) + (μ s + ν sᶜ)
        = (ν s - μ s + μ s) + ν sᶜ := by ring
      _ = ν s + ν sᶜ := by rw [tsub_add_cancel_of_le hμs_le_νs']
      _ = μ s + μ sᶜ := by simp [measure_add_measure_compl hs]
      _ = μ s + (μ sᶜ - ν sᶜ + ν sᶜ) := by rw [tsub_add_cancel_of_le hνsc_le_μsc']
      _ = (μ sᶜ - ν sᶜ) + (μ s + ν sᶜ) := by ring
  -- Define d (in ENNReal) = mass of β = mass of γ
  set d := β Set.univ with hd_def
  -- d is finite
  have hd_ne_top : d ≠ ⊤ := measure_ne_top β Set.univ
  -- Map properties for the diagonal embedding
  have hdiag_fst : ∀ (m : Measure X), (m.map diag).map Prod.fst = m := by
    intro m
    rw [Measure.map_map measurable_fst hdiag]
    have : Prod.fst ∘ diag = (id : X → X) := funext fun x => rfl
    rw [this, Measure.map_id]
  have hdiag_snd : ∀ (m : Measure X), (m.map diag).map Prod.snd = m := by
    intro m
    rw [Measure.map_map measurable_snd hdiag]
    have : Prod.snd ∘ diag = (id : X → X) := funext fun x => rfl
    rw [this, Measure.map_id]
  -- Product measure marginals
  -- (γ.prod β).map fst = (β univ) • γ = d • γ
  have hprod_fst : (γ.prod β).map Prod.fst = d • γ := by
    rw [Measure.map_fst_prod]
  -- (γ.prod β).map snd = (γ univ) • β = d • β
  have hprod_snd : (γ.prod β).map Prod.snd = d • β := by
    rw [Measure.map_snd_prod, hβγ_mass]
  -- Key: d⁻¹ • d = 1 or d = 0, combined with γ + ν.restrict sᶜ = μ.restrict sᶜ
  -- First marginal: P.map fst = μ.restrict s + ν.restrict sᶜ + d⁻¹ • d • γ
  --                            = μ.restrict s + ν.restrict sᶜ + γ (if d > 0)
  --                            = μ.restrict s + μ.restrict sᶜ = μ (using hγ_add)
  -- When d = 0: P.map fst = μ.restrict s + ν.restrict sᶜ + 0
  --           and γ = 0 (since γ univ = d = 0), so μ.restrict sᶜ = ν.restrict sᶜ
  --           thus = μ.restrict s + μ.restrict sᶜ = μ
  have hd_inv_smul_γ : d⁻¹ • (d • γ) = γ := by
    by_cases hd0 : d = 0
    · have hγ_zero : γ = 0 := Measure.measure_univ_eq_zero.mp (hβγ_mass ▸ hd0)
      simp [hd0, hγ_zero]
    · rw [smul_smul, ENNReal.inv_mul_cancel hd0 hd_ne_top, one_smul]
  have hd_inv_smul_β : d⁻¹ • (d • β) = β := by
    by_cases hd0 : d = 0
    · have hβ_zero : β = 0 := Measure.measure_univ_eq_zero.mp hd0
      simp [hd0, hβ_zero]
    · rw [smul_smul, ENNReal.inv_mul_cancel hd0 hd_ne_top, one_smul]
  -- Now compute marginals
  have hfst_marginal : ((μ.restrict s).map diag + (ν.restrict sᶜ).map diag +
      d⁻¹ • (γ.prod β)).map Prod.fst = μ := by
    rw [Measure.map_add _ _ measurable_fst, Measure.map_add _ _ measurable_fst,
        hdiag_fst, hdiag_fst,
        Measure.map_smul, hprod_fst, hd_inv_smul_γ]
    -- Goal: μ.restrict s + ν.restrict sᶜ + γ = μ
    calc μ.restrict s + ν.restrict sᶜ + γ
        = μ.restrict s + (γ + ν.restrict sᶜ) := by abel
      _ = μ.restrict s + μ.restrict sᶜ := by rw [hγ_add]
      _ = μ := Measure.restrict_add_restrict_compl hs
  have hsnd_marginal : ((μ.restrict s).map diag + (ν.restrict sᶜ).map diag +
      d⁻¹ • (γ.prod β)).map Prod.snd = ν := by
    rw [Measure.map_add _ _ measurable_snd, Measure.map_add _ _ measurable_snd,
        hdiag_snd, hdiag_snd,
        Measure.map_smul, hprod_snd, hd_inv_smul_β]
    -- Goal: μ.restrict s + ν.restrict sᶜ + β = ν
    calc μ.restrict s + ν.restrict sᶜ + β
        = (β + μ.restrict s) + ν.restrict sᶜ := by abel
      _ = ν.restrict s + ν.restrict sᶜ := by rw [hβ_add]
      _ = ν := Measure.restrict_add_restrict_compl hs
  -- Define the coupling
  let P := (μ.restrict s).map diag + (ν.restrict sᶜ).map diag + d⁻¹ • (γ.prod β)
  refine ⟨P, ?_, ?_⟩
  · -- IsCoupling P μ ν
    -- Need: P is probability measure + marginals correct
    have hP_mass : P Set.univ = 1 := by
      have := congr_arg (· Set.univ) hfst_marginal
      simp [Measure.map_apply measurable_fst MeasurableSet.univ] at this
      exact this
    exact {
      isProb := ⟨hP_mass⟩
      fst_marginal := hfst_marginal
      snd_marginal := hsnd_marginal
    }
  · -- (P {p | p.1 ≠ p.2}).toReal = tvNorm μ ν
    -- Step 1: diagonal measure gives 0 on {p | p.1 ≠ p.2}
    have hne_meas : MeasurableSet {p : X × X | p.1 ≠ p.2} :=
      measurableSet_diagonal.compl
    have hdiag_ne : ∀ (m : Measure X), (m.map diag) {p : X × X | p.1 ≠ p.2} = 0 := by
      intro m
      rw [Measure.map_apply hdiag hne_meas]
      convert m.empty
      ext x
      simp [diag, mem_preimage, mem_setOf_eq]
    -- Step 2: γ is supported on sᶜ, β is supported on s
    -- Therefore (γ.prod β) is supported on sᶜ × s ⊆ {p | p.1 ≠ p.2}
    have hγ_support : ∀ A, MeasurableSet A → γ (A ∩ s) = 0 := by
      intro A hA
      -- γ = μ.restrict sᶜ - ν.restrict sᶜ, and restrict sᶜ gives 0 on subsets of s
      have h1 : (μ.restrict sᶜ) (A ∩ s) = 0 := by
        rw [Measure.restrict_apply (hA.inter hs)]
        simp [Set.inter_assoc, Set.compl_inter_self]
      exact le_antisymm (h1 ▸ Measure.sub_le (A ∩ s)) (zero_le _)
    have hβ_support : ∀ A, MeasurableSet A → β (A ∩ sᶜ) = 0 := by
      intro A hA
      have h1 : (ν.restrict s) (A ∩ sᶜ) = 0 := by
        rw [Measure.restrict_apply (hA.inter hs.compl)]
        have : A ∩ sᶜ ∩ s = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro x ⟨⟨_, hxsc⟩, hxs⟩; exact hxsc hxs
        rw [this]; exact measure_empty
      exact le_antisymm (h1 ▸ Measure.sub_le (A ∩ sᶜ)) (zero_le _)
    -- sᶜ × s ⊆ {p | p.1 ≠ p.2}: if x ∈ sᶜ, y ∈ s, then x ≠ y
    -- (γ.prod β) is supported on sᶜ × s, so {≠} has full measure
    have hprod_ne : (γ.prod β) {p : X × X | p.1 ≠ p.2} = (γ.prod β) Set.univ := by
      -- Show (γ.prod β) (diagonal X) = 0, then complement has full measure
      have hγs : γ s = 0 := by
        have := hγ_support univ MeasurableSet.univ; rwa [univ_inter] at this
      have hβsc : β sᶜ = 0 := by
        have := hβ_support univ MeasurableSet.univ; rwa [univ_inter] at this
      have hdiag_sub : diagonal X ⊆ (s ×ˢ s) ∪ (sᶜ ×ˢ sᶜ) := by
        intro ⟨x, y⟩ hxy
        simp only [diagonal, mem_setOf_eq] at hxy
        subst hxy
        simp only [mem_union, Set.mem_prod, mem_compl_iff]
        by_cases hxs : x ∈ s
        · exact Or.inl ⟨hxs, hxs⟩
        · exact Or.inr ⟨hxs, hxs⟩
      have hprod_diag_zero : (γ.prod β) (diagonal X) = 0 := by
        apply le_antisymm _ (zero_le _)
        calc (γ.prod β) (diagonal X)
            ≤ (γ.prod β) ((s ×ˢ s) ∪ (sᶜ ×ˢ sᶜ)) := measure_mono hdiag_sub
          _ ≤ (γ.prod β) (s ×ˢ s) + (γ.prod β) (sᶜ ×ˢ sᶜ) := measure_union_le _ _
          _ = γ s * β s + γ sᶜ * β sᶜ := by
              rw [Measure.prod_prod, Measure.prod_prod]
          _ = 0 := by rw [hγs, hβsc, zero_mul, mul_zero, zero_add]
      -- {p | p.1 ≠ p.2} = (diagonal X)ᶜ
      have hne_eq : {p : X × X | p.1 ≠ p.2} = (diagonal X)ᶜ := by
        ext ⟨x, y⟩; simp [diagonal]
      rw [hne_eq]
      have hdiag_meas : MeasurableSet (diagonal X) := measurableSet_diagonal
      rw [← measure_add_measure_compl hdiag_meas (μ := γ.prod β)]
      rw [hprod_diag_zero, zero_add]
    -- (γ.prod β) univ = d * d = d²
    have hprod_mass : (γ.prod β) Set.univ = d * d := by
      rw [← Set.univ_prod_univ, Measure.prod_prod, ← hβγ_mass]
    -- Step 3: P {p | p.1 ≠ p.2} = d
    have hP_ne : P {p : X × X | p.1 ≠ p.2} = d := by
      show ((μ.restrict s).map diag + (ν.restrict sᶜ).map diag + d⁻¹ • (γ.prod β))
        {p : X × X | p.1 ≠ p.2} = d
      rw [Measure.add_apply, Measure.add_apply, Measure.smul_apply,
          hdiag_ne, hdiag_ne, zero_add, zero_add,
          hprod_ne, hprod_mass, smul_eq_mul]
      by_cases hd0 : d = 0
      · simp [hd0]
      · rw [ENNReal.inv_mul_cancel_left hd0 hd_ne_top]
    -- Step 4: d.toReal = tvNorm μ ν
    have hd_eq_tv : d.toReal = tvNorm μ ν := by
      rw [hβ_mass]
      rw [ENNReal.toReal_sub_of_le hμs_le_νs' (measure_ne_top ν s)]
      exact (tvNorm_eq_of_hahn μ ν hs h_le_on_s h_le_on_sc).symm
    rw [hP_ne, hd_eq_tv]

/-! ## Main theorem: coupling characterization -/

/-- **Coupling characterization of total variation distance.**

tvNorm(μ, ν) = inf { P(σ ≠ τ) : P is a coupling of μ, ν }

The infimum is attained by the maximal coupling.

This is the fundamental result connecting total variation distance
to probabilistic coupling theory. -/
theorem tvNorm_eq_inf_coupling (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [MeasurableEq X] :
    tvNorm μ ν = sInf {c : ℝ | ∃ P : Measure (X × X),
      IsCoupling P μ ν ∧ c = (P {p : X × X | p.1 ≠ p.2}).toReal} := by
  apply le_antisymm
  · -- tvNorm ≤ sInf: for every coupling P, tvNorm ≤ P({≠})
    apply le_csInf
    · -- Nonemptiness: product coupling exists
      obtain ⟨P, hP, _⟩ := exists_maximal_coupling μ ν
      exact ⟨(P {p | p.1 ≠ p.2}).toReal, P, hP, rfl⟩
    · rintro c ⟨P, hP, rfl⟩
      exact tvNorm_le_coupling P μ ν hP
  · -- sInf ≤ tvNorm: the maximal coupling achieves tvNorm
    obtain ⟨P, hP, hPeq⟩ := exists_maximal_coupling μ ν
    apply csInf_le
    · -- Bounded below by 0
      exact ⟨0, fun c ⟨Q, _, hc⟩ => hc ▸ ENNReal.toReal_nonneg⟩
    · exact ⟨P, hP, hPeq.symm⟩

/-! ## Corollaries for Dobrushin theory -/

/-- **Coordinate disagreement bound.**

For any coupling P of μ, ν and any projection π:
  P(π(σ) ≠ π(τ)) ≤ P(σ ≠ τ).

In particular, for π = evaluation at site y:
  P(σ(y) ≠ τ(y)) ≤ P(σ ≠ τ) = tvNorm(μ, ν). -/
theorem coupling_coord_ne_le (P : Measure (X × X))
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hP : IsCoupling P μ ν)
    {Y : Type*} [MeasurableSpace Y]
    (π : X → Y) (hπ : Measurable π) :
    (P {p : X × X | π p.1 ≠ π p.2}).toReal ≤
      (P {p : X × X | p.1 ≠ p.2}).toReal := by
  have := hP.isProb
  apply ENNReal.toReal_le_toReal (measure_ne_top P _) (measure_ne_top P _) |>.mpr
  apply measure_mono
  intro p hp
  simp only [mem_setOf_eq] at hp ⊢
  intro heq
  exact hp (congrArg π heq)

/-- **Pointwise telescoping lemma.**

For a coordinate-Lipschitz function h with finitely supported Lipschitz constants c,
for any pair (σ, τ), the difference |h(σ) - h(τ)| can be bounded by summing the
coordinate Lipschitz constants over coordinates where σ and τ disagree. -/
private lemma pointwise_lipschitz_telescope
    {ι : Type*} [DecidableEq ι]
    {S : Type*} [DecidableEq S]
    (h : (ι → S) → ℝ)
    (c : ι → ℝ) (hc_nn : ∀ y, 0 ≤ c y)
    (hc_lip : ∀ (σ τ : ι → S) (y : ι),
      (∀ z, z ≠ y → σ z = τ z) → |h σ - h τ| ≤ c y)
    (F : Finset ι)
    (σ τ : ι → S)
    (h_support : ∀ z, z ∉ F → σ z = τ z) :
    |h σ - h τ| ≤ ∑ y ∈ F, c y * if σ y ≠ τ y then 1 else 0 := by
  induction F using Finset.cons_induction generalizing σ with
  | empty =>
    -- All coordinates agree, so σ = τ
    have : σ = τ := funext fun z => h_support z (Finset.notMem_empty z)
    simp [this]
  | cons a s ha ih =>
    rw [Finset.cons_eq_insert]
    -- Telescoping: |h σ - h τ| ≤ |h σ - h (σ[a := τ a])| + |h (σ[a := τ a]) - h τ|
    let σ' := Function.update σ a (τ a)
    calc |h σ - h τ|
        = |(h σ - h σ') + (h σ' - h τ)| := by ring_nf
      _ ≤ |h σ - h σ'| + |h σ' - h τ| := abs_add_le _ _
      _ ≤ c a * (if σ a ≠ τ a then 1 else 0) +
            ∑ y ∈ s, c y * (if σ' y ≠ τ y then 1 else 0) := by
          gcongr
          · -- |h σ - h σ'| ≤ c a (they differ only at a)
            by_cases heq : σ a = τ a
            · -- σ a = τ a, so σ' = σ, difference is 0
              simp only [heq, ne_eq, not_true_eq_false, ↓reduceIte, mul_zero]
              have hσ'σ : σ' = σ := by
                ext z; simp only [σ', Function.update_apply]
                split_ifs with hz
                · exact hz ▸ heq.symm
                · rfl
              simp [hσ'σ]
            · simp only [ne_eq, heq, not_false_eq_true, ↓reduceIte, mul_one]
              exact hc_lip σ σ' a (fun z hz => by
                simp only [σ', Function.update_of_ne hz])
          · -- |h σ' - h τ| ≤ Σ_{y ∈ s} by induction
            apply ih
            intro z hz
            simp only [σ', Function.update_apply]
            split_ifs with heq
            · exact heq ▸ rfl
            · exact h_support z (fun hmem => by
                rw [Finset.cons_eq_insert] at hmem
                simp only [Finset.mem_insert] at hmem
                exact hmem.elim heq hz)
      _ = ∑ y ∈ insert a s, c y * (if σ y ≠ τ y then 1 else 0) := by
          rw [Finset.sum_insert ha]
          -- Need to show that σ' y = σ y for y ∈ s (since y ≠ a)
          congr 1
          apply Finset.sum_congr rfl
          intro y hy
          have hne : y ≠ a := fun heq => ha (heq ▸ hy)
          congr 1
          simp [σ', Function.update_of_ne hne]

/-- **Integral Lipschitz bound via coupling.**

For h: X → [0,1] with coordinate Lipschitz constants c(y), and
any coupling P of μ, ν:

  |∫h dμ - ∫h dν| ≤ Σ_y c(y) · P(σ(y) ≠ τ(y))

When P is the maximal coupling, the RHS becomes ≤ (Σ c(y)) · tvNorm. -/
theorem integral_lipschitz_coupling_bound
    {ι : Type*} [MeasurableSpace ι]
    {S : Type*} [MeasurableSpace S] [MeasurableEq S]
    (μ ν : Measure (ι → S)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P : Measure ((ι → S) × (ι → S)))
    (hP : IsCoupling P μ ν)
    (h : (ι → S) → ℝ) (hh : Measurable h)
    (hh_bound : ∀ σ, |h σ| ≤ 1)
    -- Coordinate Lipschitz: changing σ at y changes h by ≤ c(y)
    (c : ι → ℝ) (hc_nn : ∀ y, 0 ≤ c y)
    (hc_lip : ∀ (σ τ : ι → S) (y : ι),
      (∀ z, z ≠ y → σ z = τ z) →
      |h σ - h τ| ≤ c y)
    -- Finite support (nearest-neighbor case)
    (hc_finsupp : (Function.support c).Finite)
    -- h depends only on F-coordinates (follows from measurability + single-coord invariance
    -- via a cylinder-set factorization argument; added as hypothesis for now)
    (h_dep_F : ∀ (σ τ : ι → S),
      (∀ y ∈ hc_finsupp.toFinset, σ y = τ y) → h σ = h τ) :
    |∫ σ, h σ ∂μ - ∫ σ, h σ ∂ν| ≤
      ∑ y ∈ hc_finsupp.toFinset, c y *
        (P {p : (ι → S) × (ι → S) | p.1 y ≠ p.2 y}).toReal := by
  classical
  have hPprob := hP.isProb
  set F := hc_finsupp.toFinset with hF_def
  -- ────────────────────────────────────────────────
  -- Preliminary: h does not depend on coordinates outside F.
  -- For z ∉ F we have c z = 0, so changing coordinate z preserves h.
  -- ────────────────────────────────────────────────
  have h_const_outside : ∀ (z : ι), z ∉ F → ∀ (ρ : ι → S) (v : S),
      h ρ = h (Function.update ρ z v) := by
    intro z hz ρ v
    have hcz : c z = 0 := by
      rwa [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hz
    have hle := hc_lip ρ (Function.update ρ z v) z
      (fun w hw => (Function.update_of_ne hw v ρ).symm)
    rw [hcz] at hle
    have := abs_nonpos_iff.mp hle
    linarith
  -- h depends only on F-coordinates (provided as hypothesis h_dep_F)
  -- The local name F = hc_finsupp.toFinset matches the hypothesis.
  -- ────────────────────────────────────────────────
  -- Step 1: Rewrite integrals using coupling marginals
  -- ────────────────────────────────────────────────
  have h_int_fst : Integrable (fun p : (ι → S) × (ι → S) => h p.1) P :=
    Integrable.of_bound (hh.comp measurable_fst).aestronglyMeasurable 1
      (ae_of_all _ (fun p => by simp [Real.norm_eq_abs, hh_bound p.1]))
  have h_int_snd : Integrable (fun p : (ι → S) × (ι → S) => h p.2) P :=
    Integrable.of_bound (hh.comp measurable_snd).aestronglyMeasurable 1
      (ae_of_all _ (fun p => by simp [Real.norm_eq_abs, hh_bound p.2]))
  have hfst : ∫ σ, h σ ∂μ = ∫ p, h p.1 ∂P := by
    rw [← hP.fst_marginal]
    exact integral_map measurable_fst.aemeasurable hh.aestronglyMeasurable
  have hsnd : ∫ σ, h σ ∂ν = ∫ p, h p.2 ∂P := by
    rw [← hP.snd_marginal]
    exact integral_map measurable_snd.aemeasurable hh.aestronglyMeasurable
  rw [hfst, hsnd, ← integral_sub h_int_fst h_int_snd]
  -- ────────────────────────────────────────────────
  -- Step 2: |∫ f| ≤ ∫ |f| ≤ ∫ (pointwise bound) = Σ c(y) · P(ne y)
  -- ────────────────────────────────────────────────
  -- We use norm_integral_le_lintegral_norm to go through ℝ≥0∞ and avoid
  -- measurability issues with the indicator-sum integrand.
  -- Pointwise bound: for all p, |h p.1 - h p.2| ≤ ∑ y ∈ F, c y * (if p.1 y ≠ p.2 y then 1 else 0)
  have h_ptwise : ∀ p : (ι → S) × (ι → S),
      |h p.1 - h p.2| ≤ ∑ y ∈ F, c y * if p.1 y ≠ p.2 y then 1 else 0 := by
    intro p
    -- Build τ' that agrees with p.2 on F and p.1 outside F
    let τ' : ι → S := fun i => if i ∈ F then p.2 i else p.1 i
    -- h(p.2) = h(τ') since they agree on F
    have hτ' : h p.2 = h τ' := h_dep_F p.2 τ' (fun y hy => by simp [τ', hy])
    -- p.1 and τ' agree outside F
    have h_agree : ∀ z, z ∉ F → p.1 z = τ' z := fun z hz => by simp [τ', hz]
    -- Apply telescope lemma to (p.1, τ')
    have htel := pointwise_lipschitz_telescope h c hc_nn hc_lip F p.1 τ' h_agree
    -- The indicator terms match: for y ∈ F, τ' y = p.2 y, so 1(p.1 y ≠ τ' y) = 1(p.1 y ≠ p.2 y)
    rw [hτ']
    calc |h p.1 - h τ'|
        ≤ ∑ y ∈ F, c y * if p.1 y ≠ τ' y then 1 else 0 := htel
      _ = ∑ y ∈ F, c y * if p.1 y ≠ p.2 y then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          -- For y ∈ F: τ' y = p.2 y, so the indicators match
          simp [τ', hy]
  -- Now bound: |∫ (h∘fst - h∘snd)| ≤ Σ c(y) · P(ne y)
  -- via |∫ f| ≤ ∫ |f| ≤ ∫ (pw bound) = Σ c(y) · ∫ 1(ne y) = Σ c(y) · P(ne y)
  -- Route: |∫ f dP| ≤ (∫⁻ ‖f‖ₑ dP).toReal (norm_integral_le_lintegral_norm)
  --        ≤ (∫⁻ (pw bound)ₑ dP).toReal (lintegral_mono, no measurability needed)
  --        ≤ (Σ c(y) * P(ne y)).toReal (lintegral_finset_sum + lintegral_indicator_one_le)
  --        = Σ c(y) * P(ne y).toReal (toReal distributes over finite nonneg sums)
  -- However, lintegral_finset_sum still requires AEMeasurable for each summand,
  -- and lintegral_indicator_one needs MeasurableSet. Both require MeasurableEq S.
  -- We use a direct lintegral bound that avoids these.
  -- Use norm_integral_le_lintegral_norm to go to lintegral world (no measurability needed)
  -- then bound lintegral pointwise using h_ptwise, then decompose.
  have h_nonneg_sum : ∀ p : (ι → S) × (ι → S),
      0 ≤ ∑ y ∈ F, c y * if p.1 y ≠ p.2 y then (1 : ℝ) else 0 :=
    fun p => Finset.sum_nonneg (fun y _ => mul_nonneg (hc_nn y) (by split_ifs <;> norm_num))
  calc |∫ p, (h p.1 - h p.2) ∂P|
      = ‖∫ p, (h p.1 - h p.2) ∂P‖ := (Real.norm_eq_abs _).symm
    _ ≤ (∫⁻ p, ENNReal.ofReal ‖h p.1 - h p.2‖ ∂P).toReal :=
        norm_integral_le_lintegral_norm _
    _ ≤ (∫⁻ p, ENNReal.ofReal (∑ y ∈ F,
          c y * if p.1 y ≠ p.2 y then 1 else 0) ∂P).toReal := by
        apply ENNReal.toReal_mono
        · -- The lintegral is finite (bounded by a constant on a probability space)
          apply ne_top_of_le_ne_top
            (ENNReal.ofReal_ne_top)
          calc ∫⁻ p, ENNReal.ofReal (∑ y ∈ F, c y * if p.1 y ≠ p.2 y then 1 else 0) ∂P
              ≤ ∫⁻ _, ENNReal.ofReal (∑ y ∈ F, c y) ∂P := by
                apply lintegral_mono
                intro p
                exact ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun y _ =>
                  le_trans (mul_le_mul_of_nonneg_left
                    (by split_ifs <;> norm_num : (if p.1 y ≠ p.2 y then (1 : ℝ) else 0) ≤ 1)
                    (hc_nn y))
                    (le_of_eq (mul_one (c y))))
            _ = ENNReal.ofReal (∑ y ∈ F, c y) * P Set.univ := lintegral_const _
            _ = ENNReal.ofReal (∑ y ∈ F, c y) := by
                rw [measure_univ, mul_one]
        · apply lintegral_mono
          intro p
          apply ENNReal.ofReal_le_ofReal
          rw [Real.norm_eq_abs]
          exact h_ptwise p
    _ ≤ (∑ y ∈ F, ENNReal.ofReal (c y) *
          P {p : (ι → S) × (ι → S) | p.1 y ≠ p.2 y}).toReal := by
        -- Decompose the lintegral of the sum into sum of lintegrals,
        -- then each term equals ofReal(c y) * P({p | p.1 y ≠ p.2 y}).
        -- Measurability of {p | p.1 y ≠ p.2 y}: follows from MeasurableEq S.
        have h_meas_ne : ∀ y : ι, MeasurableSet {p : (ι → S) × (ι → S) | p.1 y ≠ p.2 y} := by
          intro y
          apply MeasurableSet.compl
          exact measurableSet_eq_fun
            ((measurable_pi_apply y).comp measurable_fst)
            ((measurable_pi_apply y).comp measurable_snd)
        apply ENNReal.toReal_mono
        · -- RHS is finite
          exact ENNReal.sum_ne_top.mpr
            (fun y _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P _))
        · -- Rewrite ofReal of sum as sum of lintegrals, then evaluate each.
          -- Step 1: Push ofReal inside the sum
          have step1 : ∫⁻ p, ENNReal.ofReal (∑ y ∈ F, c y * if p.1 y ≠ p.2 y then 1 else 0) ∂P
              = ∫⁻ p, ∑ y ∈ F, ENNReal.ofReal (c y * if p.1 y ≠ p.2 y then 1 else 0) ∂P := by
            apply lintegral_congr; intro p
            rw [ENNReal.ofReal_sum_of_nonneg (fun y _ =>
              mul_nonneg (hc_nn y) (by split_ifs <;> norm_num))]
          -- Step 2: Swap sum and integral
          have step2 : ∫⁻ p, ∑ y ∈ F, ENNReal.ofReal (c y * if p.1 y ≠ p.2 y then 1 else 0) ∂P
              = ∑ y ∈ F, ∫⁻ p, ENNReal.ofReal (c y * if p.1 y ≠ p.2 y then 1 else 0) ∂P := by
            apply lintegral_finset_sum
            intro y _
            apply Measurable.ennreal_ofReal
            exact measurable_const.mul
              (Measurable.ite (h_meas_ne y) measurable_const measurable_const)
          -- Step 3: Factor out constant, rewrite indicator, evaluate
          have step3 : ∀ y, ∫⁻ p, ENNReal.ofReal (c y * if p.1 y ≠ p.2 y then 1 else 0) ∂P
              = ENNReal.ofReal (c y) * P {p : (ι → S) × (ι → S) | p.1 y ≠ p.2 y} := by
            intro y
            -- ofReal of product = product of ofReal
            have hfact : ∀ p : (ι → S) × (ι → S),
                ENNReal.ofReal (c y * if p.1 y ≠ p.2 y then (1 : ℝ) else 0) =
                ENNReal.ofReal (c y) * ENNReal.ofReal (if p.1 y ≠ p.2 y then 1 else 0) :=
              fun p => ENNReal.ofReal_mul (hc_nn y)
            rw [show (fun p : (ι → S) × (ι → S) =>
                  ENNReal.ofReal (c y * if p.1 y ≠ p.2 y then 1 else 0)) =
                (fun p : (ι → S) × (ι → S) =>
                  ENNReal.ofReal (c y) * ENNReal.ofReal (if p.1 y ≠ p.2 y then 1 else 0))
              from funext hfact]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr 1
            -- ∫⁻ ofReal(if ne then 1 else 0) = P({ne})
            have hind : (fun p : (ι → S) × (ι → S) =>
                ENNReal.ofReal (if p.1 y ≠ p.2 y then (1 : ℝ) else 0)) =
                Set.indicator {p : (ι → S) × (ι → S) | p.1 y ≠ p.2 y} 1 := by
              ext p
              simp only [Set.indicator, Set.mem_setOf_eq]
              split_ifs <;> simp [ENNReal.ofReal_zero, ENNReal.ofReal_one]
            rw [hind, lintegral_indicator_one (h_meas_ne y)]
          -- Combine all steps
          rw [step1, step2]
          exact le_of_eq (Finset.sum_congr rfl (fun y _ => step3 y))
    _ = ∑ y ∈ F, c y *
          (P {p : (ι → S) × (ι → S) | p.1 y ≠ p.2 y}).toReal := by
        rw [ENNReal.toReal_sum (fun y _ =>
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P _))]
        congr 1; ext y
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hc_nn y)]

/-! ## Explicit maximal coupling -/

/-- The explicit maximal coupling of two probability measures,
constructed via Hahn decomposition. This extracts the witness from
`exists_maximal_coupling` so that downstream proofs can refer to a
canonical coupling without carrying existential witnesses. -/
noncomputable def maximalCoupling (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [MeasurableEq X] :
    Measure (X × X) :=
  (exists_maximal_coupling μ ν).choose

/-- The maximal coupling is a coupling of μ and ν. -/
theorem maximalCoupling_isCoupling (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [MeasurableEq X] :
    IsCoupling (maximalCoupling μ ν) μ ν :=
  (exists_maximal_coupling μ ν).choose_spec.1

/-- The maximal coupling achieves the total variation distance:
P({(σ,τ) | σ ≠ τ}) = tvNorm(μ, ν). -/
theorem maximalCoupling_ne (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [MeasurableEq X] :
    ((maximalCoupling μ ν) {p | p.1 ≠ p.2}).toReal = tvNorm μ ν :=
  (exists_maximal_coupling μ ν).choose_spec.2

/-- The maximal coupling is a probability measure. -/
instance maximalCoupling_isProbabilityMeasure (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [MeasurableEq X] :
    IsProbabilityMeasure (maximalCoupling μ ν) :=
  (maximalCoupling_isCoupling μ ν).isProb

/-! ## Total variation triangle inequality -/

/-- The defining set of tvNorm is nonempty. -/
private lemma tvNorm_set_nonempty (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ({c : ℝ | ∃ A : Set X, MeasurableSet A ∧
      c = |(μ A).toReal - (ν A).toReal|} : Set ℝ).Nonempty :=
  ⟨0, ∅, MeasurableSet.empty, by simp⟩

/-- The defining set of tvNorm is bounded above by 1. -/
private lemma tvNorm_set_bddAbove (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    BddAbove {c : ℝ | ∃ A : Set X, MeasurableSet A ∧
      c = |(μ A).toReal - (ν A).toReal|} := by
  refine ⟨1, fun c hc => ?_⟩
  obtain ⟨A, _, hcA⟩ := hc
  rw [hcA]
  have h1 : (μ A).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal one_pos.le (by simp [prob_le_one])
  have h2 : (ν A).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal one_pos.le (by simp [prob_le_one])
  have h3 : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have h4 : 0 ≤ (ν A).toReal := ENNReal.toReal_nonneg
  rw [abs_le]; constructor <;> linarith

/-- Each measurable set difference is bounded by tvNorm. -/
private lemma abs_toReal_sub_le_tvNorm (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set X) (hA : MeasurableSet A) :
    |(μ A).toReal - (ν A).toReal| ≤ tvNorm μ ν :=
  le_csSup (tvNorm_set_bddAbove μ ν) ⟨A, hA, rfl⟩

/-- **Triangle inequality for total variation distance.**

tvNorm(μ, ρ) ≤ tvNorm(μ, ν) + tvNorm(ν, ρ).

Proof: For any measurable A,
  |μ(A) - ρ(A)| ≤ |μ(A) - ν(A)| + |ν(A) - ρ(A)|
                 ≤ tvNorm(μ, ν) + tvNorm(ν, ρ).
Taking the supremum over A gives the result. -/
theorem tvNorm_triangle (μ ν ρ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    tvNorm μ ρ ≤ tvNorm μ ν + tvNorm ν ρ := by
  unfold tvNorm
  apply csSup_le (tvNorm_set_nonempty μ ρ)
  rintro c ⟨A, hA, rfl⟩
  calc |(μ A).toReal - (ρ A).toReal|
      = |((μ A).toReal - (ν A).toReal) + ((ν A).toReal - (ρ A).toReal)| := by
        ring_nf
    _ ≤ |(μ A).toReal - (ν A).toReal| + |(ν A).toReal - (ρ A).toReal| :=
        abs_add_le _ _
    _ ≤ tvNorm μ ν + tvNorm ν ρ :=
        add_le_add (abs_toReal_sub_le_tvNorm μ ν A hA)
                   (abs_toReal_sub_le_tvNorm ν ρ A hA)

end
