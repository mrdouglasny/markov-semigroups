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
  suffices h_tv : tvNorm μ ν = (ν s).toReal - (μ s).toReal by linarith
  -- Show tvNorm = ν(s) - μ(s) (the Hahn set achieves the supremum)
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
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∃ P : Measure (X × X),
      IsCoupling P μ ν ∧
      (P {p : X × X | p.1 ≠ p.2}).toReal = tvNorm μ ν := by
  /-
  **Proof sketch for the maximal coupling.**

  Let s be the Hahn set from `hahn_decomposition ν μ`:
  - On s: μ(A) ≤ ν(A) for measurable A ⊆ s
  - On sᶜ: ν(A) ≤ μ(A) for measurable A ⊆ sᶜ

  Define:
  - β = ν.restrict s - μ.restrict s (excess of ν on s, mass d = tvNorm)
  - γ = μ.restrict sᶜ - ν.restrict sᶜ (excess of μ on sᶜ, mass d)
  - P = (μ.restrict s).map diag + (ν.restrict sᶜ).map diag + d⁻¹ • (γ.prod β)

  where diag x = (x, x).

  Marginal verification:
  - P.map fst = μ.restrict s + ν.restrict sᶜ + d⁻¹ · (β.univ • γ)
             = μ.restrict s + ν.restrict sᶜ + γ
             = μ.restrict s + μ.restrict sᶜ = μ
  - P.map snd = μ.restrict s + ν.restrict sᶜ + d⁻¹ · (γ.univ • β)
             = μ.restrict s + ν.restrict sᶜ + β
             = ν.restrict s + ν.restrict sᶜ = ν

  Disagreement: γ lives on sᶜ, β lives on s, so (γ.prod β) lives on
  sᶜ × s ⊆ {(x,y) | x ≠ y}. Thus:
    P({≠}) = d⁻¹ · (γ.prod β)({≠}) = d⁻¹ · d² = d = tvNorm.

  The formalization requires:
  1. Measure restriction/subtraction calculus (Measure.sub_apply, sub_add_cancel_of_le)
  2. Product measure marginals (map_fst_prod, map_snd_prod)
  3. Diagonal map properties (measurability, preimage of {≠})
  4. SFinite instances for restricted/subtracted measures
  5. Showing μ.restrict s + μ.restrict sᶜ = μ (Measure.restrict_add_restrict_compl)
  -/
  sorry

/-! ## Main theorem: coupling characterization -/

/-- **Coupling characterization of total variation distance.**

tvNorm(μ, ν) = inf { P(σ ≠ τ) : P is a coupling of μ, ν }

The infimum is attained by the maximal coupling.

This is the fundamental result connecting total variation distance
to probabilistic coupling theory. -/
theorem tvNorm_eq_inf_coupling (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
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
    {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
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
  -- and lintegral_indicator_one needs MeasurableSet. Both require MeasurableEq S
  -- (available from MeasurableSingletonClass S + Countable S).
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
        -- Measurability of {p | p.1 y ≠ p.2 y}: follows from MeasurableEq S
        -- (which holds for Countable S + MeasurableSingletonClass S).
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

end
