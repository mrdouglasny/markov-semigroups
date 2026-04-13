/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heat Kernel Positivity for Z-Matrices

A Z-matrix (or Stieltjes matrix) has nonpositive off-diagonal entries.
The matrix exponential exp(-tM) of a Z-matrix M has nonneg entries
for all t ≥ 0. Equivalently, -M is a Metzler matrix and exp(-tM)
is a positive semigroup.

## Proof

Write M = D + L where D = diag(M) and L has the off-diagonal entries.
Then -M = -D - L, and -L ≥ 0 entrywise (since M has nonpositive
off-diagonal). By the Euler approximation:

  exp(-tM) = lim_{n→∞} (I - tM/n)^n

For n large enough, I - tM/n = I - t(D+L)/n has nonneg entries:
- Diagonal: 1 - tD_{ii}/n > 0 for n > t·max|D_{ii}|
- Off-diagonal: -tL_{ij}/n ≥ 0 (since L_{ij} ≤ 0 for i ≠ j)

Products of entrywise-nonneg matrices are entrywise-nonneg,
so (I - tM/n)^n ≥ 0, and the limit preserves nonnegativity.

## References

- Simon, Functional Integration and Quantum Physics (1979), Ch. 22
- Berman-Plemmons, Nonnegative Matrices in the Mathematical Sciences
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.InfiniteSum.Order

noncomputable section

open Matrix BigOperators Finset

namespace MatrixSemigroup

variable {n : Type*} [Fintype n] [DecidableEq n]

-- Use linftyOp norm for matrices
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-- Each matrix entry is bounded by the linftyOp norm. -/
private theorem matrix_entry_le_norm (A : Matrix n n ℝ) (i j : n) :
    ‖A i j‖ ≤ ‖A‖ := by
  simp only [Matrix.linfty_opNorm_def]
  have h1 : ‖A i j‖₊ ≤ ∑ j' : n, ‖A i j'‖₊ :=
    Finset.single_le_sum (f := fun j' => ‖A i j'‖₊) (fun _ _ => zero_le _)
      (Finset.mem_univ j)
  have h2 : (∑ j' : n, ‖A i j'‖₊) ≤ Finset.univ.sup
      (fun i' : n => ∑ j' : n, ‖A i' j'‖₊) := by
    apply Finset.le_sup (f := fun i' : n => ∑ j' : n, ‖A i' j'‖₊)
    exact Finset.mem_univ i
  calc (‖A i j‖ : ℝ) = ↑‖A i j‖₊ := (coe_nnnorm _).symm
    _ ≤ ↑(∑ j' : n, ‖A i j'‖₊) := by exact_mod_cast h1
    _ ≤ ↑(Finset.univ.sup fun i' => ∑ j', ‖A i' j'‖₊) := by exact_mod_cast h2

/-! ## Z-matrix definition -/

/-- A Z-matrix has nonpositive off-diagonal entries. -/
def IsZMatrix (M : Matrix n n ℝ) : Prop :=
  ∀ i j, i ≠ j → M i j ≤ 0

/-- A matrix is entrywise nonneg. -/
def IsEntryNonneg (A : Matrix n n ℝ) : Prop :=
  ∀ i j, 0 ≤ A i j

/-! ## Basic properties of entrywise-nonneg matrices -/

theorem isEntryNonneg_one : IsEntryNonneg (1 : Matrix n n ℝ) := by
  intro i j
  simp [Matrix.one_apply]
  split_ifs <;> norm_num

theorem isEntryNonneg_add {A B : Matrix n n ℝ}
    (hA : IsEntryNonneg A) (hB : IsEntryNonneg B) :
    IsEntryNonneg (A + B) := by
  intro i j; simp [Matrix.add_apply]; linarith [hA i j, hB i j]

theorem isEntryNonneg_mul {A B : Matrix n n ℝ}
    (hA : IsEntryNonneg A) (hB : IsEntryNonneg B) :
    IsEntryNonneg (A * B) := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hA i k) (hB k j)

theorem isEntryNonneg_pow {A : Matrix n n ℝ}
    (hA : IsEntryNonneg A) (k : ℕ) :
    IsEntryNonneg (A ^ k) := by
  induction k with
  | zero => simp; exact isEntryNonneg_one
  | succ k ih => rw [pow_succ]; exact isEntryNonneg_mul ih hA

/-- Scaling a nonneg matrix by a nonneg scalar preserves nonnegativity. -/
theorem isEntryNonneg_smul {A : Matrix n n ℝ} {c : ℝ}
    (hA : IsEntryNonneg A) (hc : 0 ≤ c) :
    IsEntryNonneg (c • A) := by
  intro i j; simp [Matrix.smul_apply]; exact mul_nonneg hc (hA i j)

/-! ## I - tM/n is entrywise nonneg for large n -/

/-- For a Z-matrix M, the Euler factor I - (t/n)·M has nonneg entries
when n is large enough. -/
theorem euler_factor_nonneg (M : Matrix n n ℝ) (hZ : IsZMatrix M)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (hn : t * ‖M‖ < (n : ℝ)) :
    IsEntryNonneg (1 - (t / n) • M) := by
  intro i j
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    smul_eq_mul]
  by_cases hij : i = j
  · -- Diagonal: 1 - (t/n)·M_{ii}
    subst hij
    simp
    -- Need: 0 ≤ 1 - t/n · M i i, i.e., t/n · M i i ≤ 1
    -- |M i i| ≤ ‖M‖, so t/n · |M i i| ≤ t/n · ‖M‖ < 1
    have hn_pos : (0 : ℝ) < n := by
      by_contra h
      push_neg at h
      have : t * ‖M‖ < 0 := lt_of_lt_of_le hn (by exact_mod_cast h)
      linarith [mul_nonneg ht (norm_nonneg M)]
    have htn : t / ↑n * ‖M‖ < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hn_pos]; exact hn
    have hn_pos : (0 : ℝ) < n := by
      by_contra h; push_neg at h
      linarith [mul_nonneg ht (norm_nonneg M)]
    have htn_pos : 0 ≤ t / ↑n := div_nonneg ht hn_pos.le
    have htn_norm : t / ↑n * ‖M‖ < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hn_pos]; exact hn
    -- M i i ≤ |M i i| ≤ ‖M‖, so t/n · M i i ≤ t/n · ‖M‖ < 1
    have hMii : M i i ≤ ‖M‖ := by
      calc M i i ≤ |M i i| := le_abs_self _
        _ = ‖M i i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖M‖ := matrix_entry_le_norm M i i
    calc t / ↑n * M i i ≤ t / ↑n * ‖M‖ :=
          mul_le_mul_of_nonneg_left hMii htn_pos
      _ ≤ 1 := htn_norm.le
  · -- Off-diagonal: 0 - (t/n)·M_{ij} = -(t/n)·M_{ij} ≥ 0
    simp [hij]
    have : M i j ≤ 0 := hZ i j hij
    have : (0 : ℝ) ≤ t / n := div_nonneg ht (by positivity)
    linarith [mul_nonpos_of_nonneg_of_nonpos ‹0 ≤ t / ↑n› ‹M i j ≤ 0›]

/-! ## Exp of entrywise-nonneg matrix -/

/-- **exp of entrywise-nonneg matrix is entrywise-nonneg.**

exp(A) = Σ_k A^k/k! where each term A^k/k! is entrywise-nonneg
(from `isEntryNonneg_pow` and nonneg scalar 1/k!), so the sum is nonneg.

This requires extracting matrix entries from the tsum definition of
`NormedSpace.exp`. The mathematical content is trivial (tsum of nonneg
terms is nonneg) but the Lean API for entry extraction from matrix
tsum needs careful instance management. -/
theorem exp_entryNonneg_of_entryNonneg (A : Matrix n n ℝ)
    (hA : IsEntryNonneg A) :
    IsEntryNonneg (NormedSpace.exp A) := by
  intro i j
  -- exp(A) i j = ∑' k, ((k!)⁻¹ • A^k) i j, extracted via Pi.hasSum
  have hentry : HasSum (fun k => ((↑k.factorial : ℝ)⁻¹ • A ^ k) i j)
      (NormedSpace.exp A i j) :=
    Pi.hasSum.mp (Pi.hasSum.mp
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A) i) j
  rw [hentry.tsum_eq.symm]
  -- Each term (k!)⁻¹ * (A^k i j) is nonneg: (k!)⁻¹ ≥ 0 and A^k ≥ 0 entrywise
  exact tsum_nonneg fun k => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (isEntryNonneg_pow hA k i j)

/-! ## Main theorem: heat kernel positivity -/

/-- **Heat kernel positivity for Z-matrices.**

For a Z-matrix M (nonpositive off-diagonal entries), the matrix
exponential exp(-tM) has nonneg entries for all t ≥ 0.

Proof (Metzler shift): write -tM = (-tα)·1 + t·(α·1 - M) where
α ≥ max_i M_{ii}. Then α·1 - M ≥ 0 entrywise (Z-matrix!), so
t·(α·1 - M) ≥ 0. By commutativity of scalar matrices:
  exp(-tM) = exp(-tα) · exp(t·(α·1 - M))
The first factor is a positive scalar, and the second has nonneg entries
by `exp_entryNonneg_of_entryNonneg`. -/
theorem heat_kernel_entrywise_nonneg (M : Matrix n n ℝ)
    (hZ : IsZMatrix M) (t : ℝ) (ht : 0 ≤ t) :
    IsEntryNonneg (NormedSpace.exp ((-t) • M)) := by
  -- Choose α = ‖M‖ + 1 as upper bound on diagonal entries
  set α : ℝ := ‖M‖ + 1
  -- Write -tM = -tα·1 + t·(α·1 - M)
  have hsplit : (-t) • M = ((-t) * α) • (1 : Matrix n n ℝ) + t • (α • (1 : Matrix n n ℝ) - M) := by
    ext i j; simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.add_apply, smul_eq_mul]; ring
  rw [hsplit]
  -- Split exp by commutativity (scalar matrix commutes with everything)
  have hcomm : Commute (((-t) * α) • (1 : Matrix n n ℝ)) (t • (α • (1 : Matrix n n ℝ) - M)) :=
    Commute.smul_left (Commute.smul_right (Commute.one_left _) _) _
  rw [NormedSpace.exp_add_of_commute hcomm]
  -- exp(-tα·1) = exp(-tα) • 1 (scalar matrix)
  have hexp_scalar : NormedSpace.exp (((-t) * α) • (1 : Matrix n n ℝ)) =
      NormedSpace.exp ((-t) * α) • (1 : Matrix n n ℝ) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one,
        ← NormedSpace.algebraMap_exp_comm]
  rw [hexp_scalar]
  -- Product: (c • 1) * B = c • B
  rw [Algebra.smul_mul_assoc]
  -- exp(-tα) > 0 as a real number
  have hpos : (0 : ℝ) < NormedSpace.exp ((-t) * α) := by
    rw [← Real.exp_eq_exp_ℝ]; exact Real.exp_pos _
  -- t • (α·1 - M) is entrywise nonneg
  have hshift_nn : IsEntryNonneg (t • (α • (1 : Matrix n n ℝ) - M)) := by
    apply isEntryNonneg_smul ht
    exact euler_factor_shift_nonneg M hZ α (fun i => by
      calc M i i ≤ |M i i| := le_abs_self _
        _ = ‖M i i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖M‖ := matrix_entry_le_norm M i i
        _ < α := lt_add_one _)
  -- exp of nonneg matrix is nonneg
  have hexp_nn := exp_entryNonneg_of_entryNonneg _ hshift_nn
  -- Positive scalar times nonneg matrix is nonneg
  rw [one_mul]
  exact isEntryNonneg_smul hpos.le hexp_nn
where
  euler_factor_shift_nonneg (M : Matrix n n ℝ) (hZ : IsZMatrix M) (α : ℝ)
      (hα : ∀ i, M i i < α) : IsEntryNonneg (α • (1 : Matrix n n ℝ) - M) := by
    intro i j
    simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.sub_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp; linarith [hα i]
    · simp [hij]; linarith [hZ i j hij]
  isEntryNonneg_smul {A : Matrix n n ℝ} {c : ℝ} (hc : 0 ≤ c) (hA : IsEntryNonneg A) :
      IsEntryNonneg (c • A) := by
    intro i j; simp [Matrix.smul_apply]; exact mul_nonneg hc (hA i j)

end MatrixSemigroup

end
