/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Neumann Series Bound for the Influence Matrix

Under Dobrushin's condition (column/row sums ≤ α < 1), the Neumann
series Σ C^n converges, giving the resolvent (I-C)⁻¹. The entries
(I-C)⁻¹_{xy} control spatial correlation decay.

## Key bounds

For the influence matrix C = (C(x,y))_{x,y}:
- Powers: (C^n)_{xy} ≤ α^n   (using row_bound iteratively)
- Sum: Σ_n (C^n)_{xy} ≤ 1/(1-α)

For nearest-neighbor influence (finite support), the POWER bound is
sharper: (C^n)_{xy} = 0 when n < dist(x,y) in the influence graph.
This gives exponential decay: entries decay at rate α^{dist(x,y)}.

## Main results

- `iterateInfluence`: n-step iterate of influence matrix
- `iterateInfluence_bound`: (C^n)_{xy} ≤ α^n under row_bound
- `iterateInfluence_sum_bound`: Σ_n (C^n)_{xy} ≤ 1/(1-α)
- `iterateInfluence_dist_bound`: for finite-support, zero below dist

## References

- Dobrushin (1968), proof of uniqueness via Neumann series
- Georgii (1988), §8, Theorem 8.2
- Chatterjee (2026), §16.2 (correlation decay)
-/

import MarkovSemigroups.Dobrushin.Uniqueness

open MeasureTheory

noncomputable section

variable {I : Type*} [DecidableEq I] {S : Type*} [MeasurableSpace S]

/-- The n-step iterate of the influence matrix.
(C^n)_{xy} = Σ_{z₁,...,z_{n-1}} C(x,z₁) · C(z₁,z₂) · ... · C(z_{n-1}, y).

Base case: C^0 = I (identity matrix). -/
def iterateInfluence (γ : GibbsSpec I S) : ℕ → I → I → ℝ
  | 0, x, y => if x = y then 1 else 0
  | n + 1, x, y => ∑' z, iterateInfluence γ n x z * influenceCoeff γ z y

/-- The 0-th iterate is the identity: 1 on diagonal, 0 off. -/
lemma iterateInfluence_zero (γ : GibbsSpec I S) (x y : I) :
    iterateInfluence γ 0 x y = if x = y then 1 else 0 := rfl

/-- The 0-th iterate is nonneg. -/
lemma iterateInfluence_zero_nonneg (γ : GibbsSpec I S) (x y : I) :
    0 ≤ iterateInfluence γ 0 x y := by
  rw [iterateInfluence_zero]
  split_ifs <;> linarith

/-- The 1st iterate is the influence matrix itself. -/
lemma iterateInfluence_one (γ : GibbsSpec I S) (x y : I) :
    iterateInfluence γ 1 x y = influenceCoeff γ x y := by
  simp only [iterateInfluence]
  -- ∑' z, (if x = z then 1 else 0) * C(z, y) = C(x, y)
  -- This is the delta-function sum.
  rw [tsum_eq_single x]
  · simp
  · intro z hz
    simp [Ne.symm hz]

/-- Iterates of the influence matrix are nonneg. -/
lemma iterateInfluence_nonneg (γ : GibbsSpec I S) (n : ℕ) (x y : I) :
    0 ≤ iterateInfluence γ n x y := by
  induction n generalizing x y with
  | zero => exact iterateInfluence_zero_nonneg γ x y
  | succ n ih =>
    simp only [iterateInfluence]
    -- Sum of products of nonnegs is nonneg
    apply tsum_nonneg
    intro z
    exact mul_nonneg (ih x z) (influenceCoeff_nonneg γ z y)

/-- **Row-sum bound for iterates, with summability.** Under Dobrushin's
row_bound, the row `y ↦ (C^n)_{x,y}` is summable AND its sum is
bounded by `α^n`. Proved together so the induction carries summability. -/
lemma iterateInfluence_row_summable_and_bound (γ : GibbsSpec I S)
    (hD : DobrushinCondition γ) (n : ℕ) (x : I) :
    Summable (fun y => iterateInfluence γ n x y) ∧
    ∑' y, iterateInfluence γ n x y ≤ hD.α ^ n := by
  induction n generalizing x with
  | zero =>
    refine ⟨?_, ?_⟩
    · -- summability of y ↦ (if x = y then 1 else 0)
      simp only [iterateInfluence_zero]
      exact summable_of_ne_finset_zero (s := {x}) (fun b hb => by
        simp [Finset.mem_singleton] at hb
        simp [Ne.symm hb])
    · simp only [iterateInfluence_zero, pow_zero]
      rw [tsum_eq_single x (fun z hz => by simp [Ne.symm hz])]
      simp
  | succ n ih =>
    -- Step: (C^{n+1})_{x,y} = ∑' z, (C^n)_{x,z} · C(z, y)
    -- We split ∑' y ∑' z ... via Fubini.
    -- Let g(z, y) = (C^n)_{x,z} · C(z, y). We need summability over I × I.
    set g : I × I → ℝ := fun p => iterateInfluence γ n x p.1 * influenceCoeff γ p.2 p.2
    -- Actually we need g z y = (C^n)_{x,z} * C(z,y). Pair (z, y).
    -- Step A: For each z, ∑' y, C(z, y) ≤ α by row_bound, and summable by row_summable.
    have h_row_z : ∀ z, Summable (fun y => influenceCoeff γ z y) := hD.row_summable
    have h_row_z_bd : ∀ z, ∑' y, influenceCoeff γ z y ≤ hD.α := hD.row_bound
    obtain ⟨ih_sum, ih_bd⟩ := ih x
    -- Step B: Inner sum ∑' y, (C^n)_{x,z} · C(z, y) = (C^n)_{x,z} · ∑' y, C(z, y)
    have h_inner_eq : ∀ z,
        ∑' y, iterateInfluence γ n x z * influenceCoeff γ z y =
          iterateInfluence γ n x z * ∑' y, influenceCoeff γ z y := fun z =>
      tsum_mul_left
    -- Step C: Show (C^{n+1})_{x, ·} is summable by factoring through z,
    -- i.e. the double sum is finite. Use that
    -- ∑' z, (C^n)_{x,z} * (∑' y, C(z,y)) ≤ ∑' z, (C^n)_{x,z} * α = α * α^n.
    -- Summability via `summable_prod_of_nonneg`.
    have h_g_nn : ∀ p : I × I, 0 ≤ iterateInfluence γ n x p.1 * influenceCoeff γ p.2 p.2 ∨ True :=
      fun _ => Or.inr trivial
    -- Work in the correct pair ordering (z, y).
    have h_pair_nn : ∀ p : I × I,
        0 ≤ iterateInfluence γ n x p.1 * influenceCoeff γ p.1 p.2 :=
      fun p => mul_nonneg (iterateInfluence_nonneg γ n x p.1)
        (influenceCoeff_nonneg γ p.1 p.2)
    -- Inner summable: for each z, the y-sum is summable (bounded by C(z, ·))
    have h_inner_sum : ∀ z, Summable
        (fun y => iterateInfluence γ n x z * influenceCoeff γ z y) :=
      fun z => (h_row_z z).mul_left _
    -- Outer summable: z ↦ ∑' y, (C^n)_{x,z} * C(z, y) = (C^n)_{x,z} * (∑' y C(z,y))
    -- is bounded termwise by (C^n)_{x,z} * α, and (C^n)_{x, ·} is summable by IH.
    have h_outer_sum : Summable (fun z =>
        ∑' y, iterateInfluence γ n x z * influenceCoeff γ z y) := by
      refine Summable.of_nonneg_of_le
        (fun z => tsum_nonneg (fun y => mul_nonneg
          (iterateInfluence_nonneg γ n x z) (influenceCoeff_nonneg γ z y)))
        (fun z => ?_) (ih_sum.mul_right hD.α)
      rw [h_inner_eq z]
      exact mul_le_mul_of_nonneg_left (h_row_z_bd z)
        (iterateInfluence_nonneg γ n x z)
    -- Product summability via summable_prod_of_nonneg
    have h_prod_sum : Summable (fun p : I × I =>
        iterateInfluence γ n x p.1 * influenceCoeff γ p.1 p.2) := by
      rw [summable_prod_of_nonneg h_pair_nn]
      exact ⟨h_inner_sum, h_outer_sum⟩
    -- Now use Fubini: ∑' y, (C^{n+1})_{x,y} = ∑' y ∑' z = ∑' z ∑' y (swap)
    -- Define row function: f y = (C^{n+1})_{x,y} = ∑' z, (C^n)_{x,z} * C(z,y)
    -- Via swap-summability for y-z:
    have h_swap_sum : Summable (fun p : I × I =>
        iterateInfluence γ n x p.2 * influenceCoeff γ p.2 p.1) := by
      -- Convert from h_prod_sum via Equiv.prodComm
      rw [show (fun p : I × I =>
          iterateInfluence γ n x p.2 * influenceCoeff γ p.2 p.1) =
        (fun p : I × I =>
          iterateInfluence γ n x p.1 * influenceCoeff γ p.1 p.2) ∘
        (Equiv.prodComm I I) from by ext ⟨a, b⟩; rfl]
      exact (Equiv.prodComm I I).summable_iff.mpr h_prod_sum
    -- Summability of rows: for each y, ∑' z (C^n)_{x,z} * C(z, y) is summable
    have h_row_y_sum : ∀ y, Summable
        (fun z => iterateInfluence γ n x z * influenceCoeff γ z y) := by
      intro y
      have := ((summable_prod_of_nonneg
        (fun p : I × I => mul_nonneg
          (iterateInfluence_nonneg γ n x p.2)
          (influenceCoeff_nonneg γ p.2 p.1))).mp h_swap_sum).1 y
      exact this
    -- Summability of outer y
    have h_outer_y_sum : Summable (fun y =>
        ∑' z, iterateInfluence γ n x z * influenceCoeff γ z y) := by
      have := ((summable_prod_of_nonneg
        (fun p : I × I => mul_nonneg
          (iterateInfluence_nonneg γ n x p.2)
          (influenceCoeff_nonneg γ p.2 p.1))).mp h_swap_sum).2
      exact this
    refine ⟨?_, ?_⟩
    · -- Summability of ∑' y (C^{n+1})_{x,y}
      simp only [iterateInfluence]
      exact h_outer_y_sum
    · -- Bound: ∑' y (C^{n+1})_{x,y} ≤ α^{n+1}
      simp only [iterateInfluence]
      calc ∑' y, ∑' z, iterateInfluence γ n x z * influenceCoeff γ z y
          = ∑' z, ∑' y, iterateInfluence γ n x z * influenceCoeff γ z y := by
            -- Fubini: swap order.
            -- tsum_comm' : ∑' c, ∑' b, f b c = ∑' b, ∑' c, f b c
            -- Here b = z, c = y, f b c = (C^n)_{x,b} * C(b, c).
            exact h_prod_sum.tsum_comm' h_inner_sum h_row_y_sum
        _ = ∑' z, iterateInfluence γ n x z * ∑' y, influenceCoeff γ z y := by
            congr 1; ext z; exact h_inner_eq z
        _ ≤ ∑' z, iterateInfluence γ n x z * hD.α := by
            refine Summable.tsum_le_tsum ?_ ?_ (ih_sum.mul_right hD.α)
            · intro z
              exact mul_le_mul_of_nonneg_left (h_row_z_bd z)
                (iterateInfluence_nonneg γ n x z)
            · -- summable of z ↦ (C^n)_{x,z} * ∑' y C(z,y)
              refine Summable.of_nonneg_of_le
                (fun z => mul_nonneg (iterateInfluence_nonneg γ n x z)
                  (tsum_nonneg (fun y => influenceCoeff_nonneg γ z y)))
                (fun z => mul_le_mul_of_nonneg_left (h_row_z_bd z)
                  (iterateInfluence_nonneg γ n x z))
                (ih_sum.mul_right hD.α)
        _ = (∑' z, iterateInfluence γ n x z) * hD.α := tsum_mul_right
        _ ≤ hD.α ^ n * hD.α :=
            mul_le_mul_of_nonneg_right ih_bd hD.hα_pos
        _ = hD.α ^ (n + 1) := by ring

/-- **Row-sum bound for iterates.** Under Dobrushin's row_bound,
∑' y, (C^n)_{xy} ≤ α^n.

Proof by induction on n. The base case (n=0) gives 1 ≤ α^0 = 1.
The step uses Fubini and the row_bound. -/
lemma iterateInfluence_row_sum_bound (γ : GibbsSpec I S)
    (hD : DobrushinCondition γ) (n : ℕ) (x : I) :
    ∑' y, iterateInfluence γ n x y ≤ hD.α ^ n :=
  (iterateInfluence_row_summable_and_bound γ hD n x).2

/-- Summability companion: each row `y ↦ (C^n)_{x,y}` is summable. -/
lemma iterateInfluence_row_summable (γ : GibbsSpec I S)
    (hD : DobrushinCondition γ) (n : ℕ) (x : I) :
    Summable (fun y => iterateInfluence γ n x y) :=
  (iterateInfluence_row_summable_and_bound γ hD n x).1

/-- **Neumann series bound.** Σ_n (C^n)_{xy} is summable (in n), and
the sum over n of the row-sums is bounded by 1/(1-α).

This gives the resolvent bound ((I-C)⁻¹)_{xy} in the matrix norm. -/
lemma neumann_series_bound (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (x : I) :
    ∑' n, (∑' y, iterateInfluence γ n x y) ≤ (1 - hD.α)⁻¹ := by
  -- Compare term-by-term with geometric series Σ α^n = 1/(1-α).
  have h_nonneg : ∀ n, 0 ≤ ∑' y, iterateInfluence γ n x y := fun n =>
    tsum_nonneg (fun y => iterateInfluence_nonneg γ n x y)
  have h_bd : ∀ n, (∑' y, iterateInfluence γ n x y) ≤ hD.α ^ n :=
    fun n => iterateInfluence_row_sum_bound γ hD n x
  have h_geom_sum : Summable (fun n : ℕ => hD.α ^ n) :=
    summable_geometric_of_lt_one hD.hα_pos hD.hα_lt
  have h_lhs_sum : Summable (fun n => ∑' y, iterateInfluence γ n x y) :=
    Summable.of_nonneg_of_le h_nonneg h_bd h_geom_sum
  calc ∑' n, (∑' y, iterateInfluence γ n x y)
      ≤ ∑' n, hD.α ^ n :=
        Summable.tsum_le_tsum h_bd h_lhs_sum h_geom_sum
    _ = (1 - hD.α)⁻¹ := tsum_geometric_of_lt_one hD.hα_pos hD.hα_lt

/-! ## Path bounds for finite-support influence

For specifications with finite-support influence (e.g., nearest-neighbor),
the iterates inherit spatial structure. If `influenceCoeff γ x y = 0`
unless d(x, y) ≤ R, then `(C^n)_{xy} = 0` unless d(x, y) ≤ nR.

This gives exponential spatial decay: `(C^n)_{xy} ≤ α^n` AND
`(C^n)_{xy} = 0` below the distance threshold. Combined:
  ∑_{n ≥ n₀} (C^n)_{xy} ≤ α^{n₀} / (1 - α)
where n₀ = ⌈d(x,y) / R⌉. -/

/-- For finite-support influence: if the "hop distance" d satisfies
d(x, y) > nR where R is the influence range, then (C^n)_{xy} = 0.

Requires `d` to be a pseudometric-like ℕ-valued function:
`d x x = 0` (reflexivity) and the triangle inequality. -/
lemma iterateInfluence_dist_zero (γ : GibbsSpec I S)
    (d : I → I → ℕ) (R : ℕ) (hR_pos : 0 < R)
    (h_refl : ∀ x, d x x = 0)
    (h_triangle : ∀ x y z, d x y ≤ d x z + d z y)
    (h_support : ∀ x y, d x y > R → influenceCoeff γ x y = 0)
    (n : ℕ) (x y : I) (h_far : d x y > n * R) :
    iterateInfluence γ n x y = 0 := by
  induction n generalizing x y with
  | zero =>
    -- Base: n = 0, so d x y > 0, meaning x ≠ y.
    simp only [Nat.zero_mul] at h_far
    have hxy : x ≠ y := by
      intro heq
      rw [heq, h_refl] at h_far
      exact Nat.lt_irrefl 0 h_far
    simp [iterateInfluence, hxy]
  | succ n ih =>
    simp only [iterateInfluence]
    -- Each term (C^n)_{x,z} * C(z, y) is 0.
    have hterm : ∀ z, iterateInfluence γ n x z * influenceCoeff γ z y = 0 := by
      intro z
      by_cases hz : d x z > n * R
      · -- IH gives (C^n)_{xz} = 0
        rw [ih x z hz]
        ring
      · -- Then d z y > R, so C(z, y) = 0
        push_neg at hz
        have hzy : d z y > R := by
          -- d x y ≤ d x z + d z y, so d z y ≥ d x y - d x z > (n+1)R - nR = R
          have htri := h_triangle x y z
          -- h_far : d x y > (n+1) * R = n*R + R
          have h1 : d x y > n * R + R := by
            have hrw : (n + 1) * R = n * R + R := by ring
            omega
          omega
        rw [h_support z y hzy]
        ring
    simp_rw [hterm]
    exact tsum_zero

end
