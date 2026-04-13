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
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

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

/-! ## Main theorem: heat kernel positivity -/

/-- **Heat kernel positivity for Z-matrices.**

For a Z-matrix M (nonpositive off-diagonal entries), the matrix
exponential exp(-tM) has nonneg entries for all t ≥ 0.

This is the finite-dimensional analogue of positivity-preserving
semigroups. The proof uses the Euler approximation:
exp(-tM) = lim (I - tM/n)^n, where each factor is entrywise-nonneg
for large n (Step 4 of the semigroup proof, §11 of mass-gap-v3.tex). -/
axiom heat_kernel_entrywise_nonneg (M : Matrix n n ℝ)
    (hZ : IsZMatrix M) (t : ℝ) (ht : 0 ≤ t) :
    IsEntryNonneg (NormedSpace.exp ((-t) • M))

-- The Euler factor result above proves the "pointwise" step.
-- The limit step (Euler approximation converges to exp) requires
-- Mathlib's NormedSpace.exp theory. We axiomatize for now and
-- will fill when the Euler convergence API is available.
-- See: NormedSpace.exp_eq_tsum, tendsto_exp_of_nhds

end MatrixSemigroup

end
