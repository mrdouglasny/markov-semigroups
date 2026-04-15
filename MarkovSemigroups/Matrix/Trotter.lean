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

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1200000 in
/-- **Norm of the matrix exponential is bounded by the real exponential of the norm.**
  ‖exp(X)‖ ≤ exp(‖X‖).
Standard bound from the power series. -/
lemma norm_exp_le_exp_norm [Nonempty n] (X : Matrix n n ℂ) :
    ‖exp X‖ ≤ Real.exp ‖X‖ := by
  -- Compare the matrix exponential power series Σ (k!)⁻¹ • X^k with
  -- the real exponential power series Σ (k!)⁻¹ • ‖X‖^k = Real.exp ‖X‖,
  -- via HasSum.norm_le_of_bounded.
  have hX : HasSum (fun k : ℕ => (k.factorial⁻¹ : ℝ) • X ^ k) (exp X) :=
    @exp_series_hasSum_exp' ℝ (Matrix n n ℂ) _ _ _ _ _ matCompleteSpace X
  have hR : HasSum (fun k : ℕ => (k.factorial⁻¹ : ℝ) • ‖X‖ ^ k) (Real.exp ‖X‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact exp_series_hasSum_exp' (‖X‖ : ℝ)
  refine hX.norm_le_of_bounded hR (fun k => ?_)
  -- ‖(k!⁻¹ : ℝ) • X^k‖ ≤ (k!⁻¹ : ℝ) • ‖X‖^k
  have hkfact : (0 : ℝ) ≤ (k.factorial⁻¹ : ℝ) := by positivity
  have h1 : ‖(k.factorial⁻¹ : ℝ) • X ^ k‖ ≤ ‖(k.factorial⁻¹ : ℝ)‖ * ‖X ^ k‖ :=
    norm_smul_le _ _
  have h2 : ‖(k.factorial⁻¹ : ℝ)‖ = (k.factorial⁻¹ : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hkfact]
  have h3 : ‖X ^ k‖ ≤ ‖X‖ ^ k := norm_pow_le X k
  calc ‖(k.factorial⁻¹ : ℝ) • X ^ k‖
      ≤ ‖(k.factorial⁻¹ : ℝ)‖ * ‖X ^ k‖ := h1
    _ = (k.factorial⁻¹ : ℝ) * ‖X ^ k‖ := by rw [h2]
    _ ≤ (k.factorial⁻¹ : ℝ) * ‖X‖ ^ k := mul_le_mul_of_nonneg_left h3 hkfact
    _ = (k.factorial⁻¹ : ℝ) • ‖X‖ ^ k := by rw [smul_eq_mul]

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1200000 in
/-- **Taylor remainder bound**: `‖exp X - 1 - X‖ ≤ ‖X‖² · exp ‖X‖`.

Proved by comparing the tail `Σ_{k≥2} (k!)⁻¹ • X^k` against
`Σ_{k≥2} ‖X‖^k / k! = exp ‖X‖ - 1 - ‖X‖ ≤ ‖X‖² · exp ‖X‖`. -/
lemma norm_exp_sub_one_sub_self_le [Nonempty n] (X : Matrix n n ℂ) :
    ‖exp X - 1 - X‖ ≤ ‖X‖ ^ 2 * Real.exp ‖X‖ := by
  -- HasSum for exp X and Real.exp ‖X‖
  have hX0 : HasSum (fun k : ℕ => (k.factorial⁻¹ : ℝ) • X ^ k) (exp X) :=
    @exp_series_hasSum_exp' ℝ (Matrix n n ℂ) _ _ _ _ _ matCompleteSpace X
  have hR0 : HasSum (fun k : ℕ => (k.factorial⁻¹ : ℝ) * ‖X‖ ^ k) (Real.exp ‖X‖) := by
    have : HasSum (fun k : ℕ => (k.factorial⁻¹ : ℝ) • ‖X‖ ^ k) (Real.exp ‖X‖) := by
      rw [Real.exp_eq_exp_ℝ]; exact exp_series_hasSum_exp' (‖X‖ : ℝ)
    simpa [smul_eq_mul] using this
  -- Shift both sums by 2 via hasSum_nat_add_iff
  set fX : ℕ → Matrix n n ℂ := fun k => (k.factorial⁻¹ : ℝ) • X ^ k
  set fR : ℕ → ℝ := fun k => (k.factorial⁻¹ : ℝ) * ‖X‖ ^ k
  have hX_shift : HasSum (fun k : ℕ => fX (k + 2))
      (exp X - ∑ i ∈ Finset.range 2, fX i) := by
    rw [(hasSum_nat_add_iff 2 (f := fX))]; simpa using hX0
  have hR_shift : HasSum (fun k : ℕ => fR (k + 2))
      (Real.exp ‖X‖ - ∑ i ∈ Finset.range 2, fR i) := by
    rw [(hasSum_nat_add_iff 2 (f := fR))]; simpa using hR0
  have hX : HasSum
      (fun k : ℕ => ((k + 2).factorial⁻¹ : ℝ) • X ^ (k + 2))
      (exp X - ∑ i ∈ Finset.range 2, (i.factorial⁻¹ : ℝ) • X ^ i) := hX_shift
  have hR : HasSum
      (fun k : ℕ => ((k + 2).factorial⁻¹ : ℝ) * ‖X‖ ^ (k + 2))
      (Real.exp ‖X‖ - ∑ i ∈ Finset.range 2, (i.factorial⁻¹ : ℝ) * ‖X‖ ^ i) := hR_shift
  -- Identify the partial sums: for matrix side = 1 + X
  have hPS_mat : (∑ i ∈ Finset.range 2,
      ((i.factorial⁻¹ : ℝ) • X ^ i : Matrix n n ℂ)) = 1 + X := by
    rw [show (2 : ℕ) = 0 + 1 + 1 from rfl,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
      inv_one, pow_zero, pow_one]
    -- Remaining: 1 • 1 + 1 • X = 1 + X  (via Matrix-smul by (1 : ℝ))
    simp only [show ((1 : ℝ) • (1 : Matrix n n ℂ)) = 1 from one_smul _ _,
      show ((1 : ℝ) • X) = X from one_smul _ _]
  have hPS_real : (∑ i ∈ Finset.range 2,
      ((i.factorial⁻¹ : ℝ) * ‖X‖ ^ i)) = 1 + ‖X‖ := by
    simp [Finset.sum_range_succ]
  rw [hPS_mat] at hX
  rw [hPS_real] at hR
  -- Apply norm bound to hX against hR
  have step1 : ‖exp X - (1 + X)‖ ≤ Real.exp ‖X‖ - (1 + ‖X‖) := by
    refine hX.norm_le_of_bounded hR (fun k => ?_)
    have hkfact : (0 : ℝ) ≤ ((k + 2).factorial⁻¹ : ℝ) := by positivity
    calc ‖((k + 2).factorial⁻¹ : ℝ) • X ^ (k + 2)‖
        ≤ ‖((k + 2).factorial⁻¹ : ℝ)‖ * ‖X ^ (k + 2)‖ := norm_smul_le _ _
      _ = ((k + 2).factorial⁻¹ : ℝ) * ‖X ^ (k + 2)‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hkfact]
      _ ≤ ((k + 2).factorial⁻¹ : ℝ) * ‖X‖ ^ (k + 2) :=
          mul_le_mul_of_nonneg_left (norm_pow_le X (k + 2)) hkfact
  -- rewrite LHS to exp X - 1 - X
  have hLHS : exp X - 1 - X = exp X - (1 + X) := by
    rw [sub_sub]
  rw [hLHS]
  -- bound: Real.exp ‖X‖ - (1 + ‖X‖) ≤ ‖X‖² * Real.exp ‖X‖
  have hNN : 0 ≤ ‖X‖ := norm_nonneg _
  have step2 : Real.exp ‖X‖ - (1 + ‖X‖) ≤ ‖X‖ ^ 2 * Real.exp ‖X‖ := by
    -- Use: Real.add_one_le_exp y gives 1 + y ≤ exp y.
    -- Also: exp y - 1 - y = ∑_{k≥2} y^k/k! ≤ y² · exp y for y ≥ 0.
    -- Direct proof: use tsum bound.
    have hrY : HasSum (fun k : ℕ => ((k + 2).factorial⁻¹ : ℝ) * ‖X‖ ^ (k + 2))
        (Real.exp ‖X‖ - (1 + ‖X‖)) := hR
    have hrZ : HasSum (fun k : ℕ => ‖X‖ ^ 2 * ((k.factorial⁻¹ : ℝ) * ‖X‖ ^ k))
        (‖X‖ ^ 2 * Real.exp ‖X‖) := hR0.mul_left (‖X‖ ^ 2)
    refine hasSum_le (fun k => ?_) hrY hrZ
    have h_fact : ((k + 2).factorial : ℝ)⁻¹ ≤ (k.factorial : ℝ)⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact_mod_cast Nat.factorial_le (Nat.le_add_right k 2)
    have hpow : ‖X‖ ^ (k + 2) = ‖X‖ ^ 2 * ‖X‖ ^ k := by ring
    rw [hpow]
    have hXk2nn : (0 : ℝ) ≤ ‖X‖ ^ 2 * ‖X‖ ^ k := by positivity
    calc ((k + 2).factorial⁻¹ : ℝ) * (‖X‖ ^ 2 * ‖X‖ ^ k)
        ≤ (k.factorial⁻¹ : ℝ) * (‖X‖ ^ 2 * ‖X‖ ^ k) := by
          exact mul_le_mul_of_nonneg_right h_fact hXk2nn
      _ = ‖X‖ ^ 2 * ((k.factorial⁻¹ : ℝ) * ‖X‖ ^ k) := by ring
  linarith [step1, step2]

/-- `‖(1/k) • X‖ = ‖X‖ / k` for `X : Matrix n n ℂ` and `k : ℕ`. -/
private lemma norm_smul_inv_nat (X : Matrix n n ℂ) (k : ℕ) :
    ‖(1 / (k : ℂ)) • X‖ = ‖X‖ / k := by
  rw [norm_smul, norm_div, norm_one, Complex.norm_natCast, one_div, inv_mul_eq_div]

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1200000 in
/-- **BCH error estimate**: ‖exp(A/k)·exp(B/k) - exp((A+B)/k)‖ ≤ C/k².

From the Taylor remainder exp(X) = 1 + X + O(‖X‖²):
  exp(A/k)·exp(B/k) = (1+A/k+O(1/k²))(1+B/k+O(1/k²))
                     = 1+(A+B)/k+AB/k²+O(1/k²) = exp((A+B)/k)+O(1/k²).

Uses `norm_exp_sub_one_sub_self_le` for the O(‖X‖²) Taylor remainder. -/
lemma bch_error_bound [Nonempty n] (A B : Matrix n n ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ‖exp ((1 / (k : ℂ)) • A) * exp ((1 / (k : ℂ)) • B) -
       exp ((1 / (k : ℂ)) • (A + B))‖ ≤ C / (k : ℝ) ^ 2 := by
  set M : ℝ := ‖A‖ + ‖B‖ with hM_def
  set E : ℝ := Real.exp M with hE_def
  have hMnn : 0 ≤ M := by rw [hM_def]; positivity
  have hEpos : 0 < E := Real.exp_pos _
  set C : ℝ := ‖A‖ ^ 2 * E * E + (1 + M) * (‖B‖ ^ 2 * E) + ‖A‖ * ‖B‖ + M ^ 2 * E + 1
    with hC_def
  refine ⟨C, by rw [hC_def]; positivity, 1, fun k hk => ?_⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hksqpos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hkinv_le_one : (1 : ℝ) / k ≤ 1 := by
    rw [div_le_one hkpos]; exact hk1
  -- Abbreviations
  set a : Matrix n n ℂ := (1 / (k : ℂ)) • A
  set b : Matrix n n ℂ := (1 / (k : ℂ)) • B
  set s : Matrix n n ℂ := (1 / (k : ℂ)) • (A + B)
  have hs_eq : s = a + b := by
    simp only [a, b, s, smul_add]
  -- Norm bounds for a, b, s
  have hna : ‖a‖ = ‖A‖ / k := norm_smul_inv_nat A k
  have hnb : ‖b‖ = ‖B‖ / k := norm_smul_inv_nat B k
  have hns : ‖s‖ ≤ M / k := by
    show ‖(1 / (k : ℂ)) • (A + B)‖ ≤ M / k
    rw [norm_smul_inv_nat (A + B) k]
    exact div_le_div_of_nonneg_right (norm_add_le _ _) hkpos.le
  have hAnn : 0 ≤ ‖A‖ := norm_nonneg _
  have hBnn : 0 ≤ ‖B‖ := norm_nonneg _
  have hnaM : ‖a‖ ≤ M := by
    rw [hna]
    calc ‖A‖ / k ≤ ‖A‖ := by rw [div_le_iff₀ hkpos]; nlinarith
    _ ≤ M := by rw [hM_def]; linarith
  have hnbM : ‖b‖ ≤ M := by
    rw [hnb]
    calc ‖B‖ / k ≤ ‖B‖ := by rw [div_le_iff₀ hkpos]; nlinarith
    _ ≤ M := by rw [hM_def]; linarith
  have hnsM : ‖s‖ ≤ M :=
    le_trans hns (by rw [div_le_iff₀ hkpos]; nlinarith)
  -- exp bounds
  have hexpa : ‖exp a‖ ≤ E := le_trans (norm_exp_le_exp_norm a) (Real.exp_le_exp.mpr hnaM)
  have hexpb : ‖exp b‖ ≤ E := le_trans (norm_exp_le_exp_norm b) (Real.exp_le_exp.mpr hnbM)
  -- Taylor remainders
  have hta : ‖exp a - 1 - a‖ ≤ ‖a‖ ^ 2 * E := by
    calc ‖exp a - 1 - a‖ ≤ ‖a‖ ^ 2 * Real.exp ‖a‖ := norm_exp_sub_one_sub_self_le a
      _ ≤ ‖a‖ ^ 2 * E :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hnaM) (by positivity)
  have htb : ‖exp b - 1 - b‖ ≤ ‖b‖ ^ 2 * E := by
    calc ‖exp b - 1 - b‖ ≤ ‖b‖ ^ 2 * Real.exp ‖b‖ := norm_exp_sub_one_sub_self_le b
      _ ≤ ‖b‖ ^ 2 * E :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hnbM) (by positivity)
  have hts : ‖exp s - 1 - s‖ ≤ ‖s‖ ^ 2 * E := by
    calc ‖exp s - 1 - s‖ ≤ ‖s‖ ^ 2 * Real.exp ‖s‖ := norm_exp_sub_one_sub_self_le s
      _ ≤ ‖s‖ ^ 2 * E :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hnsM) (by positivity)
  -- Bounds in terms of ‖A‖, ‖B‖, M over k²
  have hna_sq : ‖a‖ ^ 2 ≤ ‖A‖ ^ 2 / (k : ℝ) ^ 2 := by
    rw [hna, div_pow]
  have hnb_sq : ‖b‖ ^ 2 ≤ ‖B‖ ^ 2 / (k : ℝ) ^ 2 := by
    rw [hnb, div_pow]
  have hns_sq : ‖s‖ ^ 2 ≤ M ^ 2 / (k : ℝ) ^ 2 := by
    have hsnn : 0 ≤ ‖s‖ := norm_nonneg _
    have hMkpos : (0 : ℝ) ≤ M / k := by positivity
    have : ‖s‖ ^ 2 ≤ (M / k) ^ 2 := by
      rw [sq, sq]
      exact mul_le_mul hns hns hsnn hMkpos
    calc ‖s‖ ^ 2 ≤ (M / k) ^ 2 := this
      _ = M ^ 2 / (k : ℝ) ^ 2 := by rw [div_pow]
  -- Key decomposition:
  -- exp a · exp b - exp s = (exp a - 1 - a) · exp b
  --                        + (1 + a) · (exp b - 1 - b)
  --                        + a · b
  --                        - (exp s - 1 - s)
  -- (algebraic identity, ignoring commutativity, verified by expansion.)
  have hdecomp :
      exp a * exp b - exp s =
        (exp a - 1 - a) * exp b + (1 + a) * (exp b - 1 - b) + a * b
          - (exp s - 1 - s) := by
    rw [hs_eq]
    noncomm_ring
  rw [hdecomp]
  -- Triangle inequality
  have tineq : ‖(exp a - 1 - a) * exp b + (1 + a) * (exp b - 1 - b) + a * b
                - (exp s - 1 - s)‖
      ≤ ‖(exp a - 1 - a) * exp b‖ + ‖(1 + a) * (exp b - 1 - b)‖ + ‖a * b‖
          + ‖exp s - 1 - s‖ := by
    calc ‖(exp a - 1 - a) * exp b + (1 + a) * (exp b - 1 - b) + a * b
              - (exp s - 1 - s)‖
        ≤ ‖(exp a - 1 - a) * exp b + (1 + a) * (exp b - 1 - b) + a * b‖
            + ‖exp s - 1 - s‖ := norm_sub_le _ _
      _ ≤ (‖(exp a - 1 - a) * exp b + (1 + a) * (exp b - 1 - b)‖ + ‖a * b‖)
            + ‖exp s - 1 - s‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ ((‖(exp a - 1 - a) * exp b‖ + ‖(1 + a) * (exp b - 1 - b)‖) + ‖a * b‖)
            + ‖exp s - 1 - s‖ := by
          gcongr
          exact norm_add_le _ _
  refine le_trans tineq ?_
  -- Bound each piece
  have bound1 : ‖(exp a - 1 - a) * exp b‖ ≤ ‖A‖ ^ 2 * E * E / (k : ℝ) ^ 2 := by
    calc ‖(exp a - 1 - a) * exp b‖ ≤ ‖exp a - 1 - a‖ * ‖exp b‖ := norm_mul_le _ _
      _ ≤ (‖a‖ ^ 2 * E) * E := by
          refine mul_le_mul hta hexpb (norm_nonneg _) ?_
          positivity
      _ ≤ (‖A‖ ^ 2 / (k : ℝ) ^ 2 * E) * E := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hna_sq hEpos.le) le_rfl
            hEpos.le ?_
          positivity
      _ = ‖A‖ ^ 2 * E * E / (k : ℝ) ^ 2 := by ring
  have bound2 : ‖(1 + a) * (exp b - 1 - b)‖ ≤ (1 + M) * (‖B‖ ^ 2 * E) / (k : ℝ) ^ 2 := by
    have hone : ‖(1 : Matrix n n ℂ)‖ = 1 := norm_one
    have h1a : ‖1 + a‖ ≤ 1 + M := by
      calc ‖(1 : Matrix n n ℂ) + a‖ ≤ ‖(1 : Matrix n n ℂ)‖ + ‖a‖ := norm_add_le _ _
        _ = 1 + ‖a‖ := by rw [hone]
        _ ≤ 1 + M := by linarith [hnaM]
    calc ‖(1 + a) * (exp b - 1 - b)‖ ≤ ‖1 + a‖ * ‖exp b - 1 - b‖ := norm_mul_le _ _
      _ ≤ (1 + M) * (‖b‖ ^ 2 * E) := by
          refine mul_le_mul h1a htb (norm_nonneg _) ?_
          linarith
      _ ≤ (1 + M) * (‖B‖ ^ 2 / (k : ℝ) ^ 2 * E) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          exact mul_le_mul_of_nonneg_right hnb_sq hEpos.le
      _ = (1 + M) * (‖B‖ ^ 2 * E) / (k : ℝ) ^ 2 := by ring
  have bound3 : ‖a * b‖ ≤ ‖A‖ * ‖B‖ / (k : ℝ) ^ 2 := by
    calc ‖a * b‖ ≤ ‖a‖ * ‖b‖ := norm_mul_le _ _
      _ = (‖A‖ / k) * (‖B‖ / k) := by rw [hna, hnb]
      _ = ‖A‖ * ‖B‖ / (k : ℝ) ^ 2 := by rw [div_mul_div_comm, sq]
  have bound4 : ‖exp s - 1 - s‖ ≤ M ^ 2 * E / (k : ℝ) ^ 2 := by
    calc ‖exp s - 1 - s‖ ≤ ‖s‖ ^ 2 * E := hts
      _ ≤ M ^ 2 / (k : ℝ) ^ 2 * E := mul_le_mul_of_nonneg_right hns_sq hEpos.le
      _ = M ^ 2 * E / (k : ℝ) ^ 2 := by ring
  have total :
      ‖(exp a - 1 - a) * exp b‖ + ‖(1 + a) * (exp b - 1 - b)‖ + ‖a * b‖
          + ‖exp s - 1 - s‖
        ≤ (‖A‖ ^ 2 * E * E + (1 + M) * (‖B‖ ^ 2 * E) + ‖A‖ * ‖B‖ + M ^ 2 * E)
            / (k : ℝ) ^ 2 := by
    have hsum : ‖A‖ ^ 2 * E * E / (k : ℝ) ^ 2 +
        (1 + M) * (‖B‖ ^ 2 * E) / (k : ℝ) ^ 2 +
        ‖A‖ * ‖B‖ / (k : ℝ) ^ 2 +
        M ^ 2 * E / (k : ℝ) ^ 2 =
        (‖A‖ ^ 2 * E * E + (1 + M) * (‖B‖ ^ 2 * E) + ‖A‖ * ‖B‖ + M ^ 2 * E)
            / (k : ℝ) ^ 2 := by ring
    linarith [bound1, bound2, bound3, bound4, hsum]
  refine le_trans total ?_
  -- Final: show LHS/k² ≤ C/k² with C = LHS + 1
  rw [hC_def]
  rw [div_le_div_iff₀ hksqpos hksqpos]
  nlinarith [hksqpos]

/-- For k ≥ 1, max(‖P_k‖, ‖Q_k‖)^{k-1} ≤ exp(‖A‖ + ‖B‖),
where P_k = exp(A/k)exp(B/k) and Q_k = exp((A+B)/k).

Uses: ‖exp(X)‖ ≤ exp(‖X‖), submultiplicativity of norm,
and exp(x/k)^k = exp(x) for real exponentials. -/
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
