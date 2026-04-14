/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lie-Trotter Product Formula for Finite Matrices

The Lie-Trotter product formula:

  exp(A + B) = lim_{n→∞} (exp(A/n) · exp(B/n))^n

for finite matrices A, B over ℂ. This is Step 2 of the semigroup
proof of the diamagnetic inequality (§11 of mass-gap-v3.tex).

## Proof strategy

1. Set Q_k = exp((A+B)/k). Then Q_k^k = exp(A+B) by `exp_nsmul`.
2. Set P_k = exp(A/k)·exp(B/k). Show ‖P_k - Q_k‖ ≤ C/k² (BCH error).
3. By telescoping: ‖P_k^k - Q_k^k‖ ≤ k · max(‖P_k‖,‖Q_k‖)^{k-1} · C/k².
4. Since ‖exp(X)‖ ≤ exp(‖X‖), we get max(...)^k ≤ exp(‖A‖+‖B‖),
   so the bound is O(1/k) → 0.

## References

- Trotter, Proc. Amer. Math. Soc. 10 (1959), 545-551
- Reed-Simon I, §VIII.8
-/

import MarkovSemigroups.Matrix.HeatKernel
import Mathlib.Tactic.NoncommRing

noncomputable section

open Matrix BigOperators Filter NormedSpace Finset

namespace MatrixSemigroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Telescoping norm bound for powers -/

/-- Telescoping recurrence: a^{m+1} - b^{m+1} = a^m(a-b) + (a^m - b^m)b. -/
private lemma pow_sub_pow_rec {R : Type*} [Ring R] (a b : R) (m : ℕ) :
    a ^ (m + 1) - b ^ (m + 1) = a ^ m * (a - b) + (a ^ m - b ^ m) * b := by
  simp only [pow_succ]; noncomm_ring

/-- **Telescoping norm bound for power differences in a normed ring.**

‖a^k - b^k‖ ≤ k · max(‖a‖, ‖b‖)^{k-1} · ‖a - b‖

Proved by induction using the non-commutative telescoping recurrence. -/
lemma norm_pow_sub_pow_le {R : Type*} [NormedRing R] [NormOneClass R] (a b : R) :
    ∀ k : ℕ, ‖a ^ k - b ^ k‖ ≤ ↑k * (max ‖a‖ ‖b‖) ^ (k - 1) * ‖a - b‖ := by
  intro k
  induction k with
  | zero => simp
  | succ m ih =>
    set M := max ‖a‖ ‖b‖
    rw [pow_sub_pow_rec, Nat.succ_sub_one]
    have hMnn : 0 ≤ M := le_max_of_le_left (norm_nonneg a)
    calc ‖a ^ m * (a - b) + (a ^ m - b ^ m) * b‖
        ≤ ‖a ^ m * (a - b)‖ + ‖(a ^ m - b ^ m) * b‖ := norm_add_le _ _
      _ ≤ ‖a ^ m‖ * ‖a - b‖ + ‖a ^ m - b ^ m‖ * ‖b‖ := by
          gcongr <;> exact norm_mul_le _ _
      _ ≤ ‖a‖ ^ m * ‖a - b‖ + (↑m * M ^ (m - 1) * ‖a - b‖) * ‖b‖ := by
          gcongr; exact norm_pow_le a m
      _ ≤ M ^ m * ‖a - b‖ + ↑m * M ^ (m - 1) * ‖a - b‖ * M := by
          have h1 : ‖a‖ ^ m ≤ M ^ m :=
            pow_le_pow_left₀ (norm_nonneg a) (le_max_left _ _) m
          have h3 : 0 ≤ ↑m * M ^ (m - 1) * ‖a - b‖ :=
            mul_nonneg (mul_nonneg (Nat.cast_nonneg' m) (pow_nonneg hMnn _)) (norm_nonneg _)
          nlinarith [norm_nonneg (a - b), le_max_right ‖a‖ ‖b‖]
      _ = (↑m + 1) * M ^ m * ‖a - b‖ := by
          cases m with
          | zero => simp
          | succ p =>
            simp only [Nat.succ_sub_one, Nat.cast_succ]
            have : M ^ (p + 1) = M ^ p * M := pow_succ M p
            rw [this]; ring
      _ = ↑(m + 1) * M ^ m * ‖a - b‖ := by push_cast; ring

/-! ## Norm bounds for matrix exponential -/

section NormBounds

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
instance matCompleteSpace : CompleteSpace (Matrix n n ℂ) :=
  FiniteDimensional.complete ℂ _

/-- **Norm of the matrix exponential is bounded by the real exponential of the norm.**
  ‖exp(X)‖ ≤ exp(‖X‖).
Standard bound from the power series. -/
lemma norm_exp_le_exp_norm [Nonempty n] (X : Matrix n n ℂ) :
    ‖exp X‖ ≤ Real.exp ‖X‖ := by
  -- The proof compares the matrix exponential power series
  -- Σ (k!)⁻¹ X^k with the real exponential power series
  -- Σ ‖X‖^k/k!, using triangle inequality and ‖X^k‖ ≤ ‖X‖^k.
  -- Technical issue: comparing tsums requires matching CompleteSpace instances.
  sorry

/-- **BCH error estimate**: ‖exp(A/k)·exp(B/k) - exp((A+B)/k)‖ ≤ C/k².

From the power series exp(X) = 1 + X + O(‖X‖²):
  exp(A/k)·exp(B/k) = (1+A/k+O(1/k²))(1+B/k+O(1/k²))
                     = 1+(A+B)/k+O(1/k²) = exp((A+B)/k)+O(1/k²).

Uses HasFPowerSeriesAt.isBigO_sub_partialSum_pow for the O(‖X‖²) bound. -/
lemma bch_error_bound [Nonempty n] (A B : Matrix n n ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ‖exp ((1 / (k : ℂ)) • A) * exp ((1 / (k : ℂ)) • B) -
       exp ((1 / (k : ℂ)) • (A + B))‖ ≤ C / (k : ℝ) ^ 2 := by
  sorry

/-- For k ≥ 1, max(‖P_k‖, ‖Q_k‖)^{k-1} ≤ exp(‖A‖ + ‖B‖),
where P_k = exp(A/k)exp(B/k) and Q_k = exp((A+B)/k).

Uses: ‖exp(X)‖ ≤ exp(‖X‖), submultiplicativity of norm,
and exp(x/k)^k = exp(x) for real exponentials. -/
private lemma norm_smul_inv_nat (X : Matrix n n ℂ) (k : ℕ) :
    ‖(1 / (k : ℂ)) • X‖ = ‖X‖ / k := by
  rw [norm_smul, norm_div, norm_one, Complex.norm_natCast, one_div, inv_mul_eq_div]

lemma max_norm_pow_le [Nonempty n] (A B : Matrix n n ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (max ‖exp ((1 / (k : ℂ)) • A) * exp ((1 / (k : ℂ)) • B)‖
         ‖exp ((1 / (k : ℂ)) • (A + B))‖) ^ (k - 1)
      ≤ Real.exp (‖A‖ + ‖B‖) := by
  set s := (1 / (k : ℂ))
  have hkpos : (0 : ℝ) < k := by positivity
  -- Bound both norms by exp((‖A‖+‖B‖)/k)
  have hP : ‖exp (s • A) * exp (s • B)‖ ≤ Real.exp ((‖A‖ + ‖B‖) / k) := by
    calc ‖exp (s • A) * exp (s • B)‖
        ≤ ‖exp (s • A)‖ * ‖exp (s • B)‖ := norm_mul_le _ _
      _ ≤ Real.exp ‖s • A‖ * Real.exp ‖s • B‖ := by
          gcongr <;> exact norm_exp_le_exp_norm _
      _ = Real.exp (‖A‖ / k + ‖B‖ / k) := by
          rw [← Real.exp_add, norm_smul_inv_nat A k, norm_smul_inv_nat B k]
      _ = Real.exp ((‖A‖ + ‖B‖) / k) := by ring_nf
  have hQ : ‖exp (s • (A + B))‖ ≤ Real.exp ((‖A‖ + ‖B‖) / k) := by
    calc ‖exp (s • (A + B))‖ ≤ Real.exp ‖s • (A + B)‖ := norm_exp_le_exp_norm _
      _ ≤ Real.exp ((‖A‖ + ‖B‖) / k) := by
          gcongr
          rw [norm_smul_inv_nat (A + B) k]
          exact div_le_div_of_nonneg_right (norm_add_le _ _) hkpos.le
  -- exp((‖A‖+‖B‖)/k) ≥ 1 since the exponent is nonneg
  have hge1 : 1 ≤ Real.exp ((‖A‖ + ‖B‖) / k) := Real.one_le_exp (by positivity)
  calc (max ‖exp (s • A) * exp (s • B)‖ ‖exp (s • (A + B))‖) ^ (k - 1)
      ≤ (Real.exp ((‖A‖ + ‖B‖) / k)) ^ (k - 1) :=
        pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _)) (max_le hP hQ) _
    _ ≤ (Real.exp ((‖A‖ + ‖B‖) / k)) ^ k :=
        pow_le_pow_right₀ hge1 (Nat.sub_le k 1)
    _ = Real.exp (‖A‖ + ‖B‖) := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp

end NormBounds

/-! ## Main theorem -/

section TrotterProof

-- The local instances are needed for the norm-based arguments in the proof.
-- The linftyOp topology is definitionally equal to the default Pi topology
-- on Matrix n n ℂ (proved by `ext U; exact Iff.rfl`), so convergence
-- results transfer freely between the two settings.
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-- **Lie-Trotter product formula for finite matrices.**

exp(A + B) = lim_{n→∞} (exp(A/n) · exp(B/n))^n

The convergence is in the operator norm (= default Pi topology for
finite matrices). Proof: telescoping bound + BCH error estimate. -/
theorem trotter_product_formula (A B : Matrix n n ℂ) :
    Filter.Tendsto
      (fun k : ℕ => ((exp ((1 / (k : ℂ)) • A)) *
                      (exp ((1 / (k : ℂ)) • B))) ^ k)
      Filter.atTop
      (nhds (exp (A + B))) := by
  -- Handle the degenerate case n = Empty
  rcases isEmpty_or_nonempty n with hempty | hne
  · haveI := hempty
    haveI : Subsingleton (Matrix n n ℂ) := inferInstance
    have : (fun k : ℕ => ((exp ((1 / (k : ℂ)) • A)) *
        (exp ((1 / (k : ℂ)) • B))) ^ k) = fun _ => exp (A + B) :=
      funext fun _ => Subsingleton.elim _ _
    rw [this]; exact tendsto_const_nhds
  · -- Nonempty case
    haveI : Nonempty n := hne
    -- Convert to ε-δ via Metric.tendsto_atTop.
    -- This works because the linftyOp topology (from local instances)
    -- is definitionally equal to the default Pi topology on Matrix n n ℂ.
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- Abbreviations
    set P := fun k : ℕ => exp ((1 / (k : ℂ)) • A) * exp ((1 / (k : ℂ)) • B)
    set Q := fun k : ℕ => exp ((1 / (k : ℂ)) • (A + B))
    -- Step 1: Q(k)^k = exp(A+B) for k ≥ 1
    have hQk : ∀ k : ℕ, 1 ≤ k → Q k ^ k = exp (A + B) := by
      intro k hk
      show (exp ((1 / (k : ℂ)) • (A + B))) ^ k = exp (A + B)
      rw [← Matrix.exp_nsmul k ((1 / (k : ℂ)) • (A + B))]
      congr 1
      rw [smul_comm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      simp [show (k : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (by omega)]
    -- Step 2: Get error bounds
    obtain ⟨C, hCpos, K₀, hBCH⟩ := bch_error_bound A B
    set E := Real.exp (‖A‖ + ‖B‖)
    -- Step 3: Choose N large enough
    obtain ⟨N, hN⟩ := exists_nat_gt (max (E * C / ε) (max K₀ 1))
    use N
    intro k hk
    have hN1 : (1 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _)
      (lt_of_le_of_lt (le_max_right (E * C / ε) _) hN)
    have hNK : (K₀ : ℝ) < N := lt_of_le_of_lt (le_max_left _ _)
      (lt_of_le_of_lt (le_max_right (E * C / ε) _) hN)
    have hk1 : 1 ≤ k := by
      have : 1 < (N : ℝ) := hN1
      have : 1 ≤ N := by exact_mod_cast this.le
      omega
    have hkK : K₀ ≤ k := by
      have : (K₀ : ℝ) < N := hNK
      have : K₀ < N := by exact_mod_cast this
      omega
    have hkpos : (0 : ℝ) < k := by positivity
    have hkR : E * C / ε < k := by
      calc E * C / ε < N := by linarith [le_max_left (E * C / ε) (max K₀ 1)]
        _ ≤ k := by exact_mod_cast hk
    -- Step 4: Bound dist(P(k)^k, exp(A+B))
    rw [dist_eq_norm, show exp (A + B) = Q k ^ k from (hQk k hk1).symm]
    -- Telescoping + BCH + exp norm bounds
    calc ‖P k ^ k - Q k ^ k‖
        ≤ ↑k * (max ‖P k‖ ‖Q k‖) ^ (k - 1) * ‖P k - Q k‖ :=
          norm_pow_sub_pow_le (P k) (Q k) k
      _ ≤ ↑k * E * (C / (k : ℝ) ^ 2) := by
          have hMk := max_norm_pow_le A B k hk1
          have hPQ : ‖P k - Q k‖ ≤ C / (k : ℝ) ^ 2 := hBCH k hkK
          have hMnn : 0 ≤ (max ‖P k‖ ‖Q k‖) ^ (k - 1) :=
            pow_nonneg (le_max_of_le_left (norm_nonneg _)) _
          have hEnn : 0 ≤ E := (Real.exp_pos _).le
          have hCdiv : 0 ≤ C / (k : ℝ) ^ 2 := div_nonneg hCpos.le (sq_nonneg _)
          have key : (max ‖P k‖ ‖Q k‖) ^ (k - 1) * ‖P k - Q k‖ ≤ E * (C / (k : ℝ) ^ 2) :=
            mul_le_mul hMk hPQ (norm_nonneg _) hEnn
          have hknn : (0 : ℝ) ≤ k := hkpos.le
          nlinarith
      _ = E * C / ↑k := by rw [sq]; field_simp
      _ < ε := by
          rw [div_lt_iff₀ hkpos]
          rw [div_lt_iff₀ hε] at hkR; linarith

end TrotterProof

end MatrixSemigroup

end
