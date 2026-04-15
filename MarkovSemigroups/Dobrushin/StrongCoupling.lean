/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strong-Coupling Verification of Dobrushin's Condition

## Overview

For lattice gauge theories and other lattice models at strong coupling
(high temperature / large β in the action), the Dobrushin influence
coefficients can be bounded explicitly, verifying the uniqueness
condition.

The key idea: when the coupling is weak (β large in the gauge theory
convention, or β small in the Ising convention), each site is nearly
independent of its neighbors, so C(x,y) is small for x ~ y and
zero for non-neighbors. The column sum is then at most 2d · C_max,
which is < 1 when the coupling is sufficiently weak.

## Main results

- `dobrushin_nearest_neighbor` — for nearest-neighbor interactions,
  C(x,y) = 0 unless |x-y| = 1
- `strong_coupling_dobrushin` — verification of Dobrushin condition
  when the interaction strength is below a threshold

## References

- Chatterjee, *Gauge Theory Lecture Notes* (2026), Ch 16, Thm 16.3.1
- Dobrushin, Theor. Prob. Appl. 13 (1968)
- Simon, *The Statistical Mechanics of Lattice Gases*, Ch III
-/

import MarkovSemigroups.Dobrushin.Uniqueness

open MeasureTheory Finset

noncomputable section

variable {d : ℕ} {S : Type*} [MeasurableSpace S]

/-! ## Helper lemmas for total variation -/

/-- Total variation distance of a measure with itself is zero. -/
lemma tvDist_self {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] : tvDist μ μ = 0 := by
  unfold tvDist
  have hset : {c : ℝ | ∃ A : Set X, MeasurableSet A ∧
      c = |(μ A).toReal - (μ A).toReal|} = {0} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, sub_self, abs_zero]
    constructor
    · rintro ⟨A, _, hc⟩; exact hc
    · intro hc; exact ⟨Set.univ, MeasurableSet.univ, hc⟩
  rw [hset, csSup_singleton]

/-- Total variation distance of equal measures is zero. -/
lemma tvDist_eq {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ = ν) : tvDist μ ν = 0 := by
  subst h; exact tvDist_self μ

/-! ## Nearest-neighbor interactions -/

/-- Two lattice sites are nearest neighbors if they differ by 1 in
exactly one coordinate. -/
def isNeighbor {d : ℕ} (x y : LatticeSite d) : Bool :=
  latticeDist x y == 1

/-- A nearest-neighbor specification: the conditional at site x
depends only on the boundary values at neighbors of x. -/
structure IsNearestNeighbor (γ : GibbsSpec (LatticeSite d) S) : Prop where
  /-- If σ and τ agree on all neighbors of x, then the single-site
      conditional at x is the same. -/
  local_dep : ∀ (x : LatticeSite d) (σ τ : SpinConfig (LatticeSite d) S),
    (∀ y, isNeighbor x y = true → σ y = τ y) →
    γ.condDist {x} σ = γ.condDist {x} τ

/-- For nearest-neighbor specifications, C(x,y) = 0 when x and y
are not neighbors. -/
theorem influenceCoeff_zero_of_not_neighbor (γ : GibbsSpec (LatticeSite d) S)
    (hNN : IsNearestNeighbor γ) (x y : LatticeSite d)
    (hxy : isNeighbor x y = false) (hne : x ≠ y) :
    influenceCoeff γ x y = 0 := by
  unfold influenceCoeff
  -- The set defining influenceCoeff consists entirely of zeros,
  -- because non-neighbor modifications don't affect the conditional.
  set T := {c : ℝ | ∃ (σ τ : SpinConfig (LatticeSite d) S),
      (∀ z, z ≠ y → σ z = τ z) ∧
      c = tvDist (γ.condDist {x} σ) (γ.condDist {x} τ)}
  -- Every element of T is 0
  have hall : ∀ c ∈ T, c = 0 := by
    rintro c ⟨σ, τ, hagree, hc⟩
    -- σ and τ differ only at y. Since y is not a neighbor of x,
    -- all neighbors of x have the same value in σ and τ.
    have hneighbors : ∀ z, isNeighbor x z = true → σ z = τ z := by
      intro z hz
      apply hagree
      intro hzy; subst hzy; simp [hz] at hxy
    rw [hc, tvDist_eq]
    exact hNN.local_dep x σ τ hneighbors
  -- T ⊆ {0}
  have hsub : T ⊆ {0} := by
    intro c hc; exact Set.mem_singleton_iff.mpr (hall c hc)
  -- Either T is empty or T = {0}; in both cases sSup T = 0
  rcases Set.eq_empty_or_nonempty T with hempty | ⟨c, hc⟩
  · rw [hempty]; exact Real.sSup_empty
  · have : T = {0} := by
      apply Set.Subset.antisymm hsub
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact hall c hc ▸ hc
    rw [this, csSup_singleton]

/-- The set of all neighbors of y in Z^d, as a Finset.
Each coordinate i contributes at most two neighbors: y ± e_i. -/
private def neighborFinset (y : LatticeSite d) : Finset (LatticeSite d) :=
  (Finset.univ : Finset (Fin d)).biUnion fun i =>
    {Function.update y i (y i + 1), Function.update y i (y i - 1)}

/-- If the sum of nonneg naturals over Fin d equals 1, there is a unique nonzero index. -/
private lemma exists_unique_of_sum_eq_one {d : ℕ} {f : Fin d → ℕ}
    (hsum : ∑ i, f i = 1) :
    ∃ j, f j = 1 ∧ ∀ k, k ≠ j → f k = 0 := by
  -- Since ∑ f i = 1, there exists some j with f j ≠ 0
  have hne : ∃ j, f j ≠ 0 := by
    by_contra h
    push Not at h
    simp [funext (fun i => Nat.eq_zero_of_le_zero (Nat.le_of_eq (h i)))] at hsum
  obtain ⟨j, hj⟩ := hne
  refine ⟨j, ?_, ?_⟩
  · -- f j ≤ ∑ i, f i = 1, and f j ≠ 0, so f j = 1
    have hle : f j ≤ ∑ i, f i := Finset.single_le_sum (fun i _ => Nat.zero_le _)
      (Finset.mem_univ j)
    omega
  · -- For k ≠ j: f k ≤ ∑ i, f i - f j = 1 - 1 = 0
    intro k hk
    have hle_k : f k ≤ ∑ i, f i := Finset.single_le_sum (fun i _ => Nat.zero_le _)
      (Finset.mem_univ k)
    have hle_j : f j ≤ ∑ i, f i := Finset.single_le_sum (fun i _ => Nat.zero_le _)
      (Finset.mem_univ j)
    -- f k + f j ≤ ∑ i, f i = 1 (since k ≠ j, these are distinct terms)
    have hdist : f k + f j ≤ ∑ i, f i := by
      have h1 : f k + f j = ∑ i ∈ ({k, j} : Finset (Fin d)), f i := by
        simp [Finset.sum_pair hk]
      rw [h1]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega

/-- If (a - b).natAbs = 1 for integers, then a = b + 1 or a = b - 1. -/
private lemma int_natAbs_eq_one {a b : ℤ} (h : (a - b).natAbs = 1) :
    a = b + 1 ∨ a = b - 1 := by omega

/-- Any site at L1 distance 1 from y is in the neighbor finset. -/
private lemma mem_neighborFinset_of_isNeighbor {y x : LatticeSite d}
    (h : isNeighbor x y = true) : x ∈ neighborFinset y := by
  simp only [isNeighbor, beq_iff_eq] at h
  simp only [neighborFinset, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  -- latticeDist x y = 1 means ∑ i, (x i - y i).natAbs = 1
  unfold latticeDist at h
  -- Extract the unique coordinate that differs
  obtain ⟨j, hj_one, hj_rest⟩ := exists_unique_of_sum_eq_one h
  -- At coordinate j, x j = y j + 1 or x j = y j - 1
  obtain hcase | hcase := int_natAbs_eq_one hj_one
  · -- x j = y j + 1 case
    refine ⟨j, Or.inl ?_⟩
    funext k
    by_cases hk : k = j
    · subst hk; simp [Function.update_self, hcase]
    · rw [Function.update_of_ne hk]
      have hk0 := hj_rest k hk
      have := Int.natAbs_eq_zero.mp hk0
      omega
  · -- x j = y j - 1 case
    refine ⟨j, Or.inr ?_⟩
    funext k
    by_cases hk : k = j
    · subst hk; simp [Function.update_self, hcase]
    · rw [Function.update_of_ne hk]
      have hk0 := hj_rest k hk
      have := Int.natAbs_eq_zero.mp hk0
      omega

/-- The neighbor finset has at most 2d elements. -/
private lemma neighborFinset_card_le (y : LatticeSite d) :
    (neighborFinset y).card ≤ 2 * d := by
  unfold neighborFinset
  calc (Finset.univ.biUnion fun i =>
      ({Function.update y i (y i + 1), Function.update y i (y i - 1)} :
        Finset (LatticeSite d))).card
      ≤ ∑ i ∈ Finset.univ, ({Function.update y i (y i + 1),
          Function.update y i (y i - 1)} : Finset (LatticeSite d)).card :=
        card_biUnion_le
    _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin d)), 2 := by
        gcongr with i _
        exact Finset.card_le_two
    _ = 2 * d := by simp [Finset.sum_const, Finset.card_univ, mul_comm]

/-- The number of neighbors of y in any finite set is at most 2d. -/
private lemma card_filter_isNeighbor_le (y : LatticeSite d) (Λ : Finset (LatticeSite d)) :
    (Λ.filter (fun x => isNeighbor x y)).card ≤ 2 * d := by
  calc (Λ.filter (fun x => isNeighbor x y)).card
      ≤ (neighborFinset y).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter] at hx
        exact mem_neighborFinset_of_isNeighbor hx.2
    _ ≤ 2 * d := neighborFinset_card_le y

/-- isNeighbor is symmetric: latticeDist is symmetric since |a-b| = |b-a|. -/
private lemma isNeighbor_comm (x y : LatticeSite d) :
    isNeighbor x y = isNeighbor y x := by
  simp only [isNeighbor]
  unfold latticeDist
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  show (x i - y i).natAbs = (y i - x i).natAbs
  omega

/-- If isNeighbor x y, then y ∈ neighborFinset x. -/
private lemma mem_neighborFinset_of_isNeighbor' {x y : LatticeSite d}
    (h : isNeighbor x y = true) : y ∈ neighborFinset x := by
  rw [isNeighbor_comm] at h
  exact mem_neighborFinset_of_isNeighbor h

/-! ## Strong-coupling regime -/

/-- A specification has interaction strength bounded by β if each
single-site conditional satisfies a Lipschitz-type bound:
changing one neighbor's spin changes the conditional by at most β
in total variation.

This is the key quantitative input for Dobrushin. -/
structure InteractionBound (γ : GibbsSpec (LatticeSite d) S) (β : ℝ) : Prop where
  hβ_pos : 0 ≤ β
  /-- TV bound on influence of a single neighbor. -/
  tv_bound : ∀ (x y : LatticeSite d), influenceCoeff γ x y ≤
    if isNeighbor x y = true then β else 0

/-- InteractionBound gives influenceCoeff = 0 for non-neighbors. -/
private lemma InteractionBound.influenceCoeff_eq_zero_of_not_isNeighbor
    {γ : GibbsSpec (LatticeSite d) S} {β : ℝ} (hIB : InteractionBound γ β)
    (x y : LatticeSite d) (h : isNeighbor x y = false) :
    influenceCoeff γ x y = 0 := by
  have hle := hIB.tv_bound x y
  have hne : ¬(isNeighbor x y = true) := by rw [h]; decide
  rw [if_neg hne] at hle
  linarith [influenceCoeff_nonneg γ x y]

/-- InteractionBound gives influenceCoeff ≤ β for neighbors. -/
private lemma InteractionBound.influenceCoeff_le_beta
    {γ : GibbsSpec (LatticeSite d) S} {β : ℝ} (hIB : InteractionBound γ β)
    (x y : LatticeSite d) :
    influenceCoeff γ x y ≤ β := by
  have hle := hIB.tv_bound x y
  by_cases h : isNeighbor x y = true
  · rw [if_pos h] at hle; exact hle
  · simp only [Bool.not_eq_true] at h
    rw [hIB.influenceCoeff_eq_zero_of_not_isNeighbor x y h]
    exact hIB.hβ_pos

/-- **Strong-coupling Dobrushin condition.**

For a nearest-neighbor specification in d dimensions, if each
neighbor's influence is at most β and 2d · β < 1, then
Dobrushin's condition holds with α = 2d · β.

This gives a mass gap for all lattice models at sufficiently
high temperature / weak coupling. -/
def strong_coupling_dobrushin (γ : GibbsSpec (LatticeSite d) S)
    (hNN : IsNearestNeighbor γ)
    (β : ℝ) (hIB : InteractionBound γ β)
    (hβ_small : 2 * d * β < 1) :
    DobrushinCondition γ where
  α := 2 * d * β
  hα_pos := by
    apply mul_nonneg
    · apply mul_nonneg
      · norm_num
      · exact Nat.cast_nonneg d
    · exact hIB.hβ_pos
  hα_lt := by exact hβ_small
  col_summable := by
    -- For nearest-neighbor, C(x,y) = 0 for all but ≤ 2d sites x,
    -- so the function has finite support and is trivially summable.
    intro y
    apply summable_of_ne_finset_zero (s := neighborFinset y)
    intro x hx
    have hnn : isNeighbor x y = false := by
      by_contra h; simp only [Bool.not_eq_false] at h
      exact hx (mem_neighborFinset_of_isNeighbor h)
    exact hIB.influenceCoeff_eq_zero_of_not_isNeighbor x y hnn
  column_bound := by
    -- ∑' x, C(x,y) = finite sum over neighbors ≤ 2d · β
    intro y
    have hzero : ∀ x ∉ neighborFinset y, influenceCoeff γ x y = 0 := by
      intro x hx
      have hnn : isNeighbor x y = false := by
        by_contra h; simp only [Bool.not_eq_false] at h
        exact hx (mem_neighborFinset_of_isNeighbor h)
      exact hIB.influenceCoeff_eq_zero_of_not_isNeighbor x y hnn
    rw [tsum_eq_sum hzero]
    calc ∑ x ∈ neighborFinset y, influenceCoeff γ x y
        ≤ ∑ _x ∈ neighborFinset y, β := by
          gcongr with x _
          exact hIB.influenceCoeff_le_beta x y
      _ = (neighborFinset y).card * β := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * d) * β := by
          gcongr
          · exact hIB.hβ_pos
          · exact_mod_cast neighborFinset_card_le y
      _ = 2 * ↑d * β := by ring
  row_summable := by
    -- Symmetric: C(x,y) = 0 unless neighbor, same bound
    intro x
    apply summable_of_ne_finset_zero (s := neighborFinset x)
    intro y hy
    have hnn : isNeighbor x y = false := by
      by_contra h; simp only [Bool.not_eq_false] at h
      exact hy (mem_neighborFinset_of_isNeighbor' h)
    exact hIB.influenceCoeff_eq_zero_of_not_isNeighbor x y hnn
  row_bound := by
    -- Same as column_bound by symmetry of nearest-neighbor
    intro x
    have hzero : ∀ y ∉ neighborFinset x, influenceCoeff γ x y = 0 := by
      intro y hy
      have hnn : isNeighbor x y = false := by
        by_contra h; simp only [Bool.not_eq_false] at h
        exact hy (mem_neighborFinset_of_isNeighbor' h)
      exact hIB.influenceCoeff_eq_zero_of_not_isNeighbor x y hnn
    rw [tsum_eq_sum hzero]
    calc ∑ y ∈ neighborFinset x, influenceCoeff γ x y
        ≤ ∑ _y ∈ neighborFinset x, β := by
          gcongr with y _
          exact hIB.influenceCoeff_le_beta x y
      _ = (neighborFinset x).card * β := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * d) * β := by
          gcongr
          · exact hIB.hβ_pos
          · exact_mod_cast neighborFinset_card_le x
      _ = 2 * ↑d * β := by ring

end
