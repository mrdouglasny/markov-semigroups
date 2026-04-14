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
  sorry

/-- The overlap measure has total mass 1 - tvNorm(μ, ν). -/
theorem overlapMeasure_mass (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (overlapMeasure μ ν Set.univ).toReal = 1 - tvNorm μ ν := by
  sorry

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
  -- Follows from tvNorm_le_coupling (lower bound) and
  -- exists_maximal_coupling (upper bound / attainment).
  sorry

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

/-- **Integral Lipschitz bound via coupling.**

For h: X → [0,1] with coordinate Lipschitz constants c(y), and
any coupling P of μ, ν:

  |∫h dμ - ∫h dν| ≤ Σ_y c(y) · P(σ(y) ≠ τ(y))

When P is the maximal coupling, the RHS becomes ≤ (Σ c(y)) · tvNorm. -/
theorem integral_lipschitz_coupling_bound
    {ι : Type*} [MeasurableSpace ι]
    {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
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
    (hc_finsupp : (Function.support c).Finite) :
    |∫ σ, h σ ∂μ - ∫ σ, h σ ∂ν| ≤
      ∑ y ∈ hc_finsupp.toFinset, c y *
        (P {p : (ι → S) × (ι → S) | p.1 y ≠ p.2 y}).toReal := by
  sorry

end
