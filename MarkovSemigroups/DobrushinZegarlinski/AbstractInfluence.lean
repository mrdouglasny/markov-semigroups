/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Abstract Influence Matrix and the Neumann-Series Bound

This module isolates the *purely linear-algebraic* core of Dobrushin's
spatial-decay argument:

  A nonnegative real matrix `M : I × I → ℝ` whose every column and
  every row is summable with sum `≤ α < 1` admits a convergent Neumann
  series `Σₙ Mⁿ`, and the n-th iterate has rows summable with sum
  `≤ α^n`.

It is the common backend used both by the existing discrete TV
specialization (`MarkovSemigroups/Dobrushin/NeumannSeries.lean`, on
`influenceCoeff` / `DobrushinCondition`) and by the new continuous
Zegarlinski specialization (`DobrushinZegarlinski/InteractionMatrix.lean`,
on the gradient interaction `c · J_xy`).

The interface deliberately avoids any mention of probability, Markov
specifications, Gibbs measures, or topology of the spin space. The
only data are nonnegativity, summability, and a uniform sum bound on
columns and rows.

See `REFACTOR_NOTES.md` in this directory for how the existing TV
proofs could later be folded into this interface. The current file is
self-contained and re-proves the Neumann iterate bound from scratch.
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section

namespace MarkovSemigroups.DobrushinZegarlinski

/-- An abstract nonnegative real matrix on `I × I` whose columns and
rows are summable with sum bounded uniformly by some `α ∈ [0, 1)`.

This packages the *only* analytic data needed for the Neumann-series
spatial decay argument. Both the discrete Dobrushin influence
coefficient and the continuous Zegarlinski gradient interaction can
be wrapped in this structure. -/
structure AbstractInfluenceMatrix (I : Type*) where
  /-- Matrix entry `Mₓᵧ`. -/
  entry : I → I → ℝ
  /-- Dobrushin contraction constant. -/
  α : ℝ
  α_nonneg : 0 ≤ α
  α_lt_one : α < 1
  entry_nonneg : ∀ x y, 0 ≤ entry x y
  /-- For each `y`, the column `x ↦ entry x y` is summable. -/
  col_summable : ∀ y, Summable (fun x => entry x y)
  /-- Each column sums to at most `α`. -/
  col_bound : ∀ y, ∑' x, entry x y ≤ α
  /-- For each `x`, the row `y ↦ entry x y` is summable. -/
  row_summable : ∀ x, Summable (fun y => entry x y)
  /-- Each row sums to at most `α`. -/
  row_bound : ∀ x, ∑' y, entry x y ≤ α

namespace AbstractInfluenceMatrix

variable {I : Type*} [DecidableEq I]

/-- The n-step iterate `Mⁿ` at `(x, y)`. The base case `M⁰` is the
identity matrix; the recursive case is matrix multiplication. -/
def iterate (M : AbstractInfluenceMatrix I) : ℕ → I → I → ℝ
  | 0, x, y => if x = y then 1 else 0
  | n + 1, x, y => ∑' z, M.iterate n x z * M.entry z y

@[simp] lemma iterate_zero (M : AbstractInfluenceMatrix I) (x y : I) :
    M.iterate 0 x y = if x = y then 1 else 0 := rfl

lemma iterate_succ (M : AbstractInfluenceMatrix I) (n : ℕ) (x y : I) :
    M.iterate (n + 1) x y = ∑' z, M.iterate n x z * M.entry z y := rfl

lemma iterate_nonneg (M : AbstractInfluenceMatrix I) :
    ∀ (n : ℕ) (x y : I), 0 ≤ M.iterate n x y
  | 0, x, y => by
      rw [iterate_zero]
      split_ifs <;> norm_num
  | n + 1, x, y => by
      rw [iterate_succ]
      exact tsum_nonneg fun z =>
        mul_nonneg (M.iterate_nonneg n x z) (M.entry_nonneg z y)

/-- **Row-sum bound for iterates** (with summability).

For every `n` and `x`, the row `y ↦ Mⁿ(x, y)` is summable, and its
sum is bounded by `α^n`. Both facts proven together so the induction
carries summability.

Proof structure:
* base (`n = 0`): the row has finite support `{x}` with value 1;
* step: factor the double sum via Fubini after establishing
  summability of the product `Mⁿ(x, z) · M(z, y)` over `(z, y)`. -/
lemma iterate_row_summable_and_bound (M : AbstractInfluenceMatrix I) :
    ∀ (n : ℕ) (x : I),
      Summable (fun y => M.iterate n x y) ∧
      ∑' y, M.iterate n x y ≤ M.α ^ n
  | 0, x => by
      refine ⟨?_, ?_⟩
      · simp only [iterate_zero]
        exact summable_of_ne_finset_zero (s := {x}) fun b hb => by
          rw [Finset.mem_singleton] at hb
          exact if_neg (fun h => hb h.symm)
      · simp only [iterate_zero, pow_zero]
        rw [tsum_eq_single x (fun z hz => if_neg (fun h => hz h.symm))]
        simp
  | n + 1, x => by
      obtain ⟨ih_sum, ih_bd⟩ := M.iterate_row_summable_and_bound n x
      have h_row_z : ∀ z, Summable (fun y => M.entry z y) := M.row_summable
      have h_row_z_bd : ∀ z, ∑' y, M.entry z y ≤ M.α := M.row_bound
      have h_inner_eq : ∀ z,
          ∑' y, M.iterate n x z * M.entry z y =
            M.iterate n x z * ∑' y, M.entry z y := fun z => tsum_mul_left
      have h_pair_nn : ∀ p : I × I,
          0 ≤ M.iterate n x p.1 * M.entry p.1 p.2 :=
        fun p => mul_nonneg (M.iterate_nonneg n x p.1) (M.entry_nonneg p.1 p.2)
      have h_inner_sum : ∀ z, Summable
          (fun y => M.iterate n x z * M.entry z y) :=
        fun z => (h_row_z z).mul_left _
      have h_outer_sum : Summable (fun z =>
          ∑' y, M.iterate n x z * M.entry z y) := by
        refine Summable.of_nonneg_of_le
          (fun z => tsum_nonneg (fun y => mul_nonneg
            (M.iterate_nonneg n x z) (M.entry_nonneg z y)))
          (fun z => ?_) (ih_sum.mul_right M.α)
        rw [h_inner_eq z]
        exact mul_le_mul_of_nonneg_left (h_row_z_bd z) (M.iterate_nonneg n x z)
      have h_prod_sum : Summable (fun p : I × I =>
          M.iterate n x p.1 * M.entry p.1 p.2) := by
        rw [summable_prod_of_nonneg h_pair_nn]
        exact ⟨h_inner_sum, h_outer_sum⟩
      have h_swap_sum : Summable (fun p : I × I =>
          M.iterate n x p.2 * M.entry p.2 p.1) := by
        rw [show (fun p : I × I => M.iterate n x p.2 * M.entry p.2 p.1) =
              (fun p : I × I => M.iterate n x p.1 * M.entry p.1 p.2) ∘
                (Equiv.prodComm I I) from by ext ⟨a, b⟩; rfl]
        exact (Equiv.prodComm I I).summable_iff.mpr h_prod_sum
      have h_outer_y_sum : Summable (fun y =>
          ∑' z, M.iterate n x z * M.entry z y) := by
        have := ((summable_prod_of_nonneg
          (fun p : I × I => mul_nonneg
            (M.iterate_nonneg n x p.2) (M.entry_nonneg p.2 p.1))).mp h_swap_sum).2
        exact this
      have h_row_y_sum : ∀ y, Summable
          (fun z => M.iterate n x z * M.entry z y) := by
        intro y
        have := ((summable_prod_of_nonneg
          (fun p : I × I => mul_nonneg
            (M.iterate_nonneg n x p.2) (M.entry_nonneg p.2 p.1))).mp h_swap_sum).1 y
        exact this
      refine ⟨?_, ?_⟩
      · simp only [iterate]; exact h_outer_y_sum
      · simp only [iterate]
        calc ∑' y, ∑' z, M.iterate n x z * M.entry z y
            = ∑' z, ∑' y, M.iterate n x z * M.entry z y := by
              exact h_prod_sum.tsum_comm' h_inner_sum h_row_y_sum
          _ = ∑' z, M.iterate n x z * ∑' y, M.entry z y := by
              congr 1; ext z; exact h_inner_eq z
          _ ≤ ∑' z, M.iterate n x z * M.α := by
              refine Summable.tsum_le_tsum ?_ ?_ (ih_sum.mul_right M.α)
              · intro z
                exact mul_le_mul_of_nonneg_left (h_row_z_bd z)
                  (M.iterate_nonneg n x z)
              · refine Summable.of_nonneg_of_le
                  (fun z => mul_nonneg (M.iterate_nonneg n x z)
                    (tsum_nonneg (fun y => M.entry_nonneg z y)))
                  (fun z => mul_le_mul_of_nonneg_left (h_row_z_bd z)
                    (M.iterate_nonneg n x z))
                  (ih_sum.mul_right M.α)
          _ = (∑' z, M.iterate n x z) * M.α := tsum_mul_right
          _ ≤ M.α ^ n * M.α := mul_le_mul_of_nonneg_right ih_bd M.α_nonneg
          _ = M.α ^ (n + 1) := by ring

/-- Each row `y ↦ Mⁿ(x, y)` is summable. -/
lemma iterate_row_summable (M : AbstractInfluenceMatrix I) (n : ℕ) (x : I) :
    Summable (fun y => M.iterate n x y) :=
  (M.iterate_row_summable_and_bound n x).1

/-- Each row of `Mⁿ` sums to at most `α^n`. -/
lemma iterate_row_sum_bound (M : AbstractInfluenceMatrix I) (n : ℕ) (x : I) :
    ∑' y, M.iterate n x y ≤ M.α ^ n :=
  (M.iterate_row_summable_and_bound n x).2

/-- Pointwise entry bound: `Mⁿ(x, y) ≤ α^n`. Follows from the
row-sum bound by dropping all but the `y`-term. -/
lemma iterate_pointwise_bound (M : AbstractInfluenceMatrix I) (n : ℕ) (x y : I) :
    M.iterate n x y ≤ M.α ^ n := by
  have h_summ := M.iterate_row_summable n x
  have h_bd := M.iterate_row_sum_bound n x
  have h_le : M.iterate n x y ≤ ∑' z, M.iterate n x z := by
    have := h_summ.sum_le_tsum ({y} : Finset I)
      (fun z _ => M.iterate_nonneg n x z)
    simpa using this
  linarith

/-- **Neumann-series row bound.** The series `Σₙ (Σ' y, Mⁿ(x, y))`
converges and is bounded by `1/(1-α)`, the resolvent of `(I-M)`. -/
lemma neumann_series_row_bound (M : AbstractInfluenceMatrix I) (x : I) :
    ∑' n, (∑' y, M.iterate n x y) ≤ (1 - M.α)⁻¹ := by
  have h_nonneg : ∀ n, 0 ≤ ∑' y, M.iterate n x y := fun n =>
    tsum_nonneg (fun y => M.iterate_nonneg n x y)
  have h_bd : ∀ n, (∑' y, M.iterate n x y) ≤ M.α ^ n :=
    fun n => M.iterate_row_sum_bound n x
  have h_geom_sum : Summable (fun n : ℕ => M.α ^ n) :=
    summable_geometric_of_lt_one M.α_nonneg M.α_lt_one
  have h_lhs_sum : Summable (fun n => ∑' y, M.iterate n x y) :=
    Summable.of_nonneg_of_le h_nonneg h_bd h_geom_sum
  calc ∑' n, (∑' y, M.iterate n x y)
      ≤ ∑' n, M.α ^ n :=
        Summable.tsum_le_tsum h_bd h_lhs_sum h_geom_sum
    _ = (1 - M.α)⁻¹ := tsum_geometric_of_lt_one M.α_nonneg M.α_lt_one

/-- **Pointwise Neumann-series bound.** For any fixed entry `(x, y)`,
the resolvent series `Σₙ Mⁿ(x, y)` is bounded by `1/(1-α)`. -/
lemma neumann_series_pointwise_bound (M : AbstractInfluenceMatrix I) (x y : I) :
    ∑' n, M.iterate n x y ≤ (1 - M.α)⁻¹ := by
  have h_geom_sum : Summable (fun n : ℕ => M.α ^ n) :=
    summable_geometric_of_lt_one M.α_nonneg M.α_lt_one
  have h_bd : ∀ n, M.iterate n x y ≤ M.α ^ n :=
    fun n => M.iterate_pointwise_bound n x y
  have h_nonneg : ∀ n, 0 ≤ M.iterate n x y :=
    fun n => M.iterate_nonneg n x y
  have h_lhs_sum : Summable (fun n => M.iterate n x y) :=
    Summable.of_nonneg_of_le h_nonneg h_bd h_geom_sum
  calc ∑' n, M.iterate n x y
      ≤ ∑' n, M.α ^ n :=
        Summable.tsum_le_tsum h_bd h_lhs_sum h_geom_sum
    _ = (1 - M.α)⁻¹ := tsum_geometric_of_lt_one M.α_nonneg M.α_lt_one

/-! ## Distance-aware bounds (finite-range interactions)

For an "influence range" `R` such that `M(x, y) = 0` whenever the
hop-distance `d(x, y) > R`, the iterates inherit spatial structure:
`Mⁿ(x, y) = 0` for `n < d(x, y) / R`. Combined with the entrywise
`α^n` bound, this gives exponential decay
`Σₙ Mⁿ(x, y) ≤ α^{d(x,y)/R} / (1 - α)`.
-/

/-- **Distance-zero rule for iterates.** If the hop-distance `d`
satisfies `d(x, y) > n · R` (and `M` has range `R`, i.e., entries
vanish beyond `d > R`), then `Mⁿ(x, y) = 0`.

Requires `d` to be a pseudometric-like `ℕ`-valued function:
`d x x = 0` (reflexivity) and the triangle inequality. -/
lemma iterate_dist_zero (M : AbstractInfluenceMatrix I)
    (d : I → I → ℕ) (R : ℕ) (_hR_pos : 0 < R)
    (h_refl : ∀ x, d x x = 0)
    (h_triangle : ∀ x y z, d x y ≤ d x z + d z y)
    (h_support : ∀ x y, d x y > R → M.entry x y = 0) :
    ∀ (n : ℕ) (x y : I), d x y > n * R → M.iterate n x y = 0 := by
  intro n x y h_far
  induction n generalizing x y with
  | zero =>
    -- Base: n = 0, so d x y > 0, meaning x ≠ y.
    simp only [Nat.zero_mul] at h_far
    have hxy : x ≠ y := by
      intro heq
      rw [heq, h_refl] at h_far
      exact Nat.lt_irrefl 0 h_far
    simp [iterate, hxy]
  | succ n ih =>
    simp only [iterate]
    -- Each term (Mⁿ)_{x,z} * M(z, y) is 0.
    have hterm : ∀ z, M.iterate n x z * M.entry z y = 0 := by
      intro z
      by_cases hz : d x z > n * R
      · rw [ih x z hz]; ring
      · push_neg at hz
        have hzy : d z y > R := by
          have htri := h_triangle x y z
          have h1 : d x y > n * R + R := by
            have hrw : (n + 1) * R = n * R + R := by ring
            omega
          omega
        rw [h_support z y hzy]; ring
    simp_rw [hterm]
    exact tsum_zero

/-- **Threshold Neumann bound (general form).** If `Mⁿ(x, y) = 0`
for all `n < k`, the entrywise Neumann sum is bounded by
`α^k / (1 - α)`. The factoring isolates the "vanishing threshold"
hypothesis from the specific way it's derived (e.g., from a
distance / range condition). -/
lemma neumann_series_threshold_bound (M : AbstractInfluenceMatrix I)
    (x y : I) (k : ℕ)
    (h_zero : ∀ n, n < k → M.iterate n x y = 0) :
    ∑' n, M.iterate n x y ≤ M.α ^ k / (1 - M.α) := by
  -- Bounding function: b n := if n < k then 0 else α^n.
  let b : ℕ → ℝ := fun n => if n < k then 0 else M.α ^ n
  have h_b_nn : ∀ n, 0 ≤ b n := fun n => by
    by_cases hn : n < k
    · simp [b, hn]
    · simp [b, hn]; exact pow_nonneg M.α_nonneg n
  have h_b_le_pow : ∀ n, b n ≤ M.α ^ n := fun n => by
    by_cases hn : n < k
    · simp [b, hn]; exact pow_nonneg M.α_nonneg n
    · simp [b, hn]
  have h_b_summ : Summable b :=
    Summable.of_nonneg_of_le h_b_nn h_b_le_pow
      (summable_geometric_of_lt_one M.α_nonneg M.α_lt_one)
  have h_bd : ∀ n, M.iterate n x y ≤ b n := by
    intro n
    by_cases hn : n < k
    · simp [b, hn, h_zero n hn]
    · simp [b, hn]; exact M.iterate_pointwise_bound n x y
  -- Shift identity: ∑' n, b n = α^k / (1 - α).
  have h_shift : ∑' n, b n = M.α ^ k * (1 - M.α)⁻¹ := by
    have hinj : Function.Injective (fun m : ℕ => m + k) := by
      intro a a' h; simpa using h
    have h_supp : Function.support b ⊆ Set.range (fun m : ℕ => m + k) := by
      intro n hn
      have h_n_ge : ¬ n < k := by
        intro hlt
        exact hn (by simp [b, hlt])
      have h_le' : k ≤ n := Nat.not_lt.mp h_n_ge
      refine ⟨n - k, ?_⟩
      show n - k + k = n
      omega
    have hreindex : ∑' m, b (m + k) = ∑' n, b n :=
      hinj.tsum_eq (f := b) h_supp
    have h_pow_eq : ∀ m, b (m + k) = M.α ^ (m + k) := fun m => by
      have : ¬ m + k < k := by omega
      simp [b, this]
    calc ∑' n, b n = ∑' m, b (m + k) := hreindex.symm
      _ = ∑' m, M.α ^ (m + k) := by simp_rw [h_pow_eq]
      _ = ∑' m, M.α ^ k * M.α ^ m := by
          congr 1; ext m; rw [pow_add]; ring
      _ = M.α ^ k * ∑' m, M.α ^ m := tsum_mul_left
      _ = M.α ^ k * (1 - M.α)⁻¹ := by
          rw [tsum_geometric_of_lt_one M.α_nonneg M.α_lt_one]
  have h_iter_summ : Summable (fun n => M.iterate n x y) :=
    Summable.of_nonneg_of_le (fun n => M.iterate_nonneg n x y)
      (fun n => M.iterate_pointwise_bound n x y)
      (summable_geometric_of_lt_one M.α_nonneg M.α_lt_one)
  calc ∑' n, M.iterate n x y
      ≤ ∑' n, b n := Summable.tsum_le_tsum h_bd h_iter_summ h_b_summ
    _ = M.α ^ k * (1 - M.α)⁻¹ := h_shift
    _ = M.α ^ k / (1 - M.α) := by field_simp

/-- **Range-`R` Neumann bound.** If `M` has range `R` (`M(u, v) = 0`
whenever `d(u, v) > R`), and we choose `k` such that
`(k - 1) · R < d(x, y)` (the strict-below condition), then the
entrywise Neumann sum has exponential decay rate `α` over `k` steps:

  Σₙ Mⁿ(x, y) ≤ α^k / (1 - α).

The user typically picks `k = ⌈d(x, y) / R⌉` (the minimum number of
`R`-jumps from `x` to `y`); this `k` automatically satisfies the
hypothesis. The R=1 case (`neumann_series_nn_dist_bound`) specializes
with `k = d(x, y)`. -/
lemma neumann_series_dist_bound (M : AbstractInfluenceMatrix I)
    (d : I → I → ℕ) (R : ℕ) (hR_pos : 0 < R)
    (h_refl : ∀ x, d x x = 0)
    (h_triangle : ∀ x y z, d x y ≤ d x z + d z y)
    (h_support : ∀ x y, d x y > R → M.entry x y = 0)
    (x y : I) (k : ℕ) (hk_strict : ∀ n, n < k → n * R < d x y) :
    ∑' n, M.iterate n x y ≤ M.α ^ k / (1 - M.α) := by
  apply M.neumann_series_threshold_bound x y k
  intro n hn
  exact M.iterate_dist_zero d R hR_pos h_refl h_triangle h_support
    n x y (hk_strict n hn)

/-- **Nearest-neighbor Neumann bound.** If `M` has range 1
(`M(u, v) = 0` whenever `d(u, v) > 1`), then the entrywise Neumann
sum has exponential decay in `d(x, y)`:

  Σₙ Mⁿ(x, y) ≤ α^{d(x,y)} / (1 - α). -/
lemma neumann_series_nn_dist_bound (M : AbstractInfluenceMatrix I)
    (d : I → I → ℕ)
    (h_refl : ∀ x, d x x = 0)
    (h_triangle : ∀ x y z, d x y ≤ d x z + d z y)
    (h_support : ∀ x y, d x y > 1 → M.entry x y = 0)
    (x y : I) :
    ∑' n, M.iterate n x y ≤ M.α ^ d x y / (1 - M.α) := by
  apply M.neumann_series_threshold_bound x y (d x y)
  intro n hn
  exact M.iterate_dist_zero d 1 Nat.one_pos h_refl h_triangle h_support
    n x y (by simpa [mul_one] using hn)

end AbstractInfluenceMatrix

end MarkovSemigroups.DobrushinZegarlinski

end
