/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Polynomial Chaos Concentration (Janson Theorem 5.10)

For a centered $F \in \mathcal H^{\le d}$ (a polynomial of total
degree $\le d$ in a finite-dim Gaussian vector), there is a
universal constant $c_d > 0$ depending only on $d$ such that
$$
\mathbb P\bigl(|F| > \lambda \, \|F\|_{L^2}\bigr)
  \;\le\; 2 \exp\bigl(-c_d \, \lambda^{2/d}\bigr),
\qquad \lambda > 0.
$$

The exponent $2/d$ is sharp (saturated by $F = \phi_1^d$). The
constant $c_d$ is dimension-independent (independent of $n$, the
size of the Gaussian vector).

## Equivalent Bonami-Nelson L^p form

$$
\|F\|_{L^p} \;\le\; (p - 1)^{d/2} \, \|F\|_{L^2},
\qquad p \ge 2.
$$

## Proof outline (three ingredients)

1. **OU hypercontractivity** restricted to chaos $\mathcal H_k$
   (`OUEigenfunctions`): for $f \in \mathcal H_k$ and $p \ge 2$,
   $\|f\|_{L^p} \le (p-1)^{k/2} \|f\|_{L^2}$.
2. **Markov / Chebyshev**: $\mathbb P(|F| > \lambda \|F\|_2) \le
   (\|F\|_p / (\lambda \|F\|_2))^p$.
3. **Optimize** $p$: set $p - 1 = (\lambda/e)^{2/d}$.

This file is the LD endpoint that downstream consumers call.

## Main theorems

- `bonami_nelson_chaos` — L^p improvement on a single chaos $\mathcal H_k$.
- `bonami_nelson_chaosLE` — L^p improvement on $\mathcal H^{\le d}$
  (with a multiplicative degree-dependent constant).
- `polynomial_chaos_concentration` — the Janson 5.10 tail bound.

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), Theorem 5.10
  (the gold-standard reference for this bound).
- A. Bonami, *Étude des coefficients de Fourier des fonctions de
  $L^p(G)$*, Ann. Inst. Fourier 20 (1970).
- E. Nelson, "The free Markov field," J. Funct. Anal. 12 (1973).
- R. Adamczak, P. Wolff, "Concentration inequalities for non-Lipschitz
  functions," Probab. Theory Related Fields 162 (2015) — modern
  treatment with explicit constants.

## Status

API + axiom skeleton (2026-05-08). The Bonami-Nelson L^p improvement
on a single chaos follows immediately from the OU eigenfunction
identity (`ouSemigroup_act_wienerChaos`) plus the abstract
hypercontractivity inequality already in
`Abstract/Hypercontractivity.lean`. The concentration tail bound is
a Markov + optimize derivation from the L^p bound. Both are stated
as axioms here pending the OU semigroup being concretely available;
the proof scripts are short once the prerequisites are wired.
-/

import MarkovSemigroups.Gaussian.OUEigenfunctions

noncomputable section

namespace MeasureTheory.Lp

/-- The coercion `Lp E p μ → (α → E)` distributes over `Finset` sums almost
everywhere. Inductive bridge from `coeFn_zero` and `coeFn_add`; not currently
in Mathlib at v4.29.0. -/
theorem coeFn_finset_sum {α E ι : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] {p : ENNReal} [DecidableEq ι]
    (s : Finset ι) (f : ι → Lp E p μ) :
    ((∑ i ∈ s, f i : Lp E p μ) : α → E)
      =ᵐ[μ] ∑ i ∈ s, ((f i : Lp E p μ) : α → E) := by
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero E p μ
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih]
        with x hx_add hx_ih
      simp only [Pi.add_apply, Finset.sum_apply] at hx_add hx_ih ⊢
      rw [hx_add, hx_ih]

end MeasureTheory.Lp

namespace MarkovSemigroups.Gaussian

open MeasureTheory

variable {n : ℕ}

/-- **Bonami-Nelson L^p improvement on a single Wiener chaos.**

For $f \in \mathcal H_k$ and $p \ge 2$:
$$
\|f\|_{L^p} \;\le\; (p - 1)^{k/2} \, \|f\|_{L^2}.
$$

**Reference:** Bonami (1970) for the 1D case; Nelson (1973) for the
infinite-dim OU semigroup. Janson §5.1.

**Proof strategy:** The OU semigroup $T_t$ is hypercontractive: it
maps $L^2 \to L^p$ for $e^{2t} = p - 1$ with operator norm $\le 1$
(`Abstract/Hypercontractivity.lean`). Restricted to $\mathcal H_k$,
$T_t$ acts as multiplication by $e^{-kt}$
(`ouSemigroup_act_wienerChaos`), hence
$\|f\|_{L^p} \cdot e^{-kt} \le \|f\|_{L^2}$. Solving for
$\|f\|_{L^p}$ with $e^{2t} = p - 1$ gives the bound. -/
theorem bonami_nelson_chaos (n k : ℕ)
    (f : Lp ℝ 2 (stdGaussianFin n))
    (hf : f ∈ wienerChaos n k)
    (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (f : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n) ≤
      ENNReal.ofReal ((p - 1) ^ ((k : ℝ) / 2)) *
        eLpNorm (f : (Fin n → ℝ) → ℝ) 2 (stdGaussianFin n) := by
  -- Choose t = (1/2) log(p-1). With p ≥ 2 we get t ≥ 0 and e^{2t} = p - 1.
  set t : ℝ := (1 / 2) * Real.log (p - 1) with ht_def
  have hp1 : (1 : ℝ) ≤ p - 1 := by linarith
  have hp1_pos : (0 : ℝ) < p - 1 := by linarith
  have ht_nonneg : 0 ≤ t := by
    have hlog : 0 ≤ Real.log (p - 1) := Real.log_nonneg hp1
    rw [ht_def]; positivity
  have h_exp_2t : Real.exp (2 * t) = p - 1 := by
    have h2t : 2 * t = Real.log (p - 1) := by rw [ht_def]; ring
    rw [h2t, Real.exp_log hp1_pos]
  have h_nelson : p - 1 ≤ Real.exp (2 * t) := by rw [h_exp_2t]
  -- Apply OU hypercontractivity at this t.
  have h_hyper :=
    ouSemigroupAct_eLpNorm_hypercontractive p hp t ht_nonneg h_nelson f
  -- Identify T_t f = e^{-kt} • f using the chaos action axiom.
  have h_chaos := ouSemigroupAct_eq_smul_of_mem_wienerChaos k t ht_nonneg f hf
  -- Substitute: eLpNorm (T_t f) p ≤ eLpNorm f 2 becomes
  --             eLpNorm (e^{-kt} • f) p ≤ eLpNorm f 2.
  have h_coe :
      ((ouSemigroupAct n t f : Lp ℝ 2 (stdGaussianFin n)) :
        (Fin n → ℝ) → ℝ)
        =ᵐ[stdGaussianFin n]
          Real.exp (-(k : ℝ) * t) • ((f : (Fin n → ℝ) → ℝ)) := by
    have := Lp.coeFn_smul (Real.exp (-(k : ℝ) * t)) f
    have hsm : ((Real.exp (-(k : ℝ) * t) • f :
        Lp ℝ 2 (stdGaussianFin n)) : (Fin n → ℝ) → ℝ)
          =ᵐ[stdGaussianFin n]
            Real.exp (-(k : ℝ) * t) • ((f : (Fin n → ℝ) → ℝ)) := this
    have hcong : ouSemigroupAct n t f =
        Real.exp (-(k : ℝ) * t) • f := h_chaos
    exact hcong ▸ hsm
  rw [eLpNorm_congr_ae h_coe] at h_hyper
  rw [eLpNorm_const_smul] at h_hyper
  -- h_hyper : ‖e^{-kt}‖ₑ * eLpNorm f p ≤ eLpNorm f 2
  have h_exp_pos : 0 < Real.exp (-(k : ℝ) * t) := Real.exp_pos _
  have h_enorm : ‖Real.exp (-(k : ℝ) * t)‖ₑ =
      ENNReal.ofReal (Real.exp (-(k : ℝ) * t)) := by
    rw [Real.enorm_eq_ofReal h_exp_pos.le]
  rw [h_enorm] at h_hyper
  -- Now we have ENNReal.ofReal e^{-kt} * eLpNorm f p ≤ eLpNorm f 2.
  -- Multiply both sides by ENNReal.ofReal e^{kt} and identify
  -- e^{kt} = (p-1)^{k/2}.
  have h_mul_inv : ENNReal.ofReal (Real.exp (-(k : ℝ) * t)) *
      ENNReal.ofReal (Real.exp ((k : ℝ) * t)) = 1 := by
    rw [← ENNReal.ofReal_mul h_exp_pos.le, ← Real.exp_add]
    have : -(k : ℝ) * t + (k : ℝ) * t = 0 := by ring
    rw [this, Real.exp_zero, ENNReal.ofReal_one]
  have h_exp_kt_pos : 0 < Real.exp ((k : ℝ) * t) := Real.exp_pos _
  have h_step :
      eLpNorm (f : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n)
        ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * t)) *
            eLpNorm (f : (Fin n → ℝ) → ℝ) 2 (stdGaussianFin n) := by
    have h_left :
        ENNReal.ofReal (Real.exp ((k : ℝ) * t)) *
          (ENNReal.ofReal (Real.exp (-(k : ℝ) * t)) *
            eLpNorm (f : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n))
          = eLpNorm (f : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p)
              (stdGaussianFin n) := by
      rw [← mul_assoc, mul_comm (ENNReal.ofReal _)
        (ENNReal.ofReal (Real.exp (-(k : ℝ) * t))), h_mul_inv, one_mul]
    calc eLpNorm (f : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n)
        = ENNReal.ofReal (Real.exp ((k : ℝ) * t)) *
            (ENNReal.ofReal (Real.exp (-(k : ℝ) * t)) *
              eLpNorm (f : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p)
                (stdGaussianFin n)) := h_left.symm
      _ ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * t)) *
          eLpNorm (f : (Fin n → ℝ) → ℝ) 2 (stdGaussianFin n) := by
            exact mul_le_mul_right h_hyper
              (ENNReal.ofReal (Real.exp ((k : ℝ) * t)))
  -- Identify e^{kt} = (p-1)^{k/2} as nonneg reals.
  have h_kt_eq : Real.exp ((k : ℝ) * t) = (p - 1) ^ ((k : ℝ) / 2) := by
    have hkt : (k : ℝ) * t = Real.log (p - 1) * ((k : ℝ) / 2) := by
      rw [ht_def]; ring
    rw [hkt, ← Real.rpow_def_of_pos hp1_pos ((k : ℝ) / 2)]
  rw [h_kt_eq] at h_step
  exact h_step

/-- **Bonami-Nelson L^p improvement on $\mathcal H^{\le d}$.**

Triangle inequality across $k = 0, \dots, d$ extends the per-chaos
bound `bonami_nelson_chaos` to $\mathcal H^{\le d}$ at the cost of a
degree-$d$ prefactor:
$$
\|F\|_{L^p} \;\le\; (d + 1) \, (p - 1)^{d/2} \, \|F\|_{L^2}.
$$

(A sharper $\sqrt{d+1}$ factor is available via Cauchy–Schwarz on the
chaos decomposition + the `wienerChaos_orthogonal` Pythagoras; the
$(d+1)$ factor here is adequate for the downstream concentration
derivation.)

**Reference:** Janson §5.1.

**Proof strategy:**
1. Decompose `F = ∑_{k=0..d} f_k` with `f_k = chaosProjection n k F`
   via `chaosProjection_sum_eq_of_mem_wienerChaosLE`.
2. Triangle inequality on `eLpNorm` (`eLpNorm_sum_le`):
   `‖F‖_p ≤ ∑_k ‖f_k‖_p`.
3. Per-chaos `bonami_nelson_chaos` on each summand:
   `‖f_k‖_p ≤ (p-1)^{k/2} ‖f_k‖_2`.
4. Bound `(p-1)^{k/2} ≤ (p-1)^{d/2}` for `k ≤ d` (Real.rpow monotone
   in the exponent for `p-1 ≥ 1`).
5. `eLpNorm`-contractive `chaosProjection`
   (`chaosProjection_eLpNorm_two_le`):
   `‖f_k‖_2 ≤ ‖F‖_2` for each `k`.
6. Sum over `k = 0, …, d` (cardinality `d+1`):
   `∑_k (p-1)^{d/2} ‖f_k‖_2 ≤ (d+1) (p-1)^{d/2} ‖F‖_2`. -/
theorem bonami_nelson_chaosLE (n d : ℕ)
    (F : Lp ℝ 2 (stdGaussianFin n))
    (hF : F ∈ wienerChaosLE n d)
    (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (F : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n) ≤
      ENNReal.ofReal (((d : ℝ) + 1) * (p - 1) ^ ((d : ℝ) / 2)) *
        eLpNorm (F : (Fin n → ℝ) → ℝ) 2 (stdGaussianFin n) := by
  set f : ℕ → Lp ℝ 2 (stdGaussianFin n) := fun k => chaosProjection n k F
    with hf_def
  have h_mem : ∀ k, f k ∈ wienerChaos n k :=
    fun k => chaosProjection_mem_wienerChaos n k F
  have h_decomp : F = ∑ k ∈ Finset.range (d + 1), f k :=
    chaosProjection_sum_eq_of_mem_wienerChaosLE n d F hF
  have h_contract : ∀ k,
      eLpNorm ((f k : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) ≤
        eLpNorm ((F : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) :=
    fun k => chaosProjection_eLpNorm_two_le n k F
  have hp_minus_1_one_le : (1 : ℝ) ≤ p - 1 := by linarith
  have h_each : ∀ k ∈ Finset.range (d + 1),
      eLpNorm ((f k : (Fin n → ℝ) → ℝ)) (ENNReal.ofReal p) (stdGaussianFin n) ≤
        ENNReal.ofReal ((p - 1) ^ ((d : ℝ) / 2)) *
          eLpNorm ((F : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) := by
    intro k hk
    have hk_le_d : (k : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h_kd : (p - 1) ^ ((k : ℝ) / 2) ≤ (p - 1) ^ ((d : ℝ) / 2) := by
      apply Real.rpow_le_rpow_of_exponent_le hp_minus_1_one_le
      linarith
    calc eLpNorm ((f k : (Fin n → ℝ) → ℝ))
            (ENNReal.ofReal p) (stdGaussianFin n)
        ≤ ENNReal.ofReal ((p - 1) ^ ((k : ℝ) / 2)) *
            eLpNorm ((f k : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) :=
          bonami_nelson_chaos n k (f k) (h_mem k) p hp
      _ ≤ ENNReal.ofReal ((p - 1) ^ ((d : ℝ) / 2)) *
            eLpNorm ((f k : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) := by gcongr
      _ ≤ ENNReal.ofReal ((p - 1) ^ ((d : ℝ) / 2)) *
            eLpNorm ((F : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) := by
            gcongr; exact h_contract k
  have h_card : (Finset.range (d + 1)).card = d + 1 := Finset.card_range _
  have h_meas : ∀ i ∈ Finset.range (d + 1),
      AEStronglyMeasurable ((f i : (Fin n → ℝ) → ℝ)) (stdGaussianFin n) :=
    fun i _ => Lp.aestronglyMeasurable _
  have hp_one : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have h_coe_sum :
      ((F : Lp ℝ 2 (stdGaussianFin n)) : (Fin n → ℝ) → ℝ)
        =ᵐ[stdGaussianFin n]
          ∑ k ∈ Finset.range (d + 1),
            ((f k : Lp ℝ 2 (stdGaussianFin n)) : (Fin n → ℝ) → ℝ) := by
    rw [h_decomp]; exact Lp.coeFn_finset_sum _ _
  rw [eLpNorm_congr_ae h_coe_sum]
  refine (eLpNorm_sum_le h_meas hp_one).trans ?_
  refine (Finset.sum_le_card_nsmul (Finset.range (d + 1))
    (fun k => eLpNorm ((f k : (Fin n → ℝ) → ℝ))
      (ENNReal.ofReal p) (stdGaussianFin n))
    (ENNReal.ofReal ((p - 1) ^ ((d : ℝ) / 2)) *
      eLpNorm ((F : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n)) h_each).trans ?_
  rw [h_card, nsmul_eq_mul, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  have h_card_cast : ((d + 1 : ℕ) : ENNReal) = ENNReal.ofReal ((d : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    push_cast; rfl
  rw [h_card_cast]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (d : ℝ) + 1)]

/-- **Polynomial Chaos Concentration (Janson Theorem 5.10).**

For centered $F \in \mathcal H^{\le d}$ with $d \ge 1$, there is a
universal constant $c_d > 0$ (depending only on $d$, not on $n$ or
the specific Gaussian vector) such that for all $\lambda > 0$,
$$
\mathbb P\bigl(|F| > \lambda \, \|F\|_{L^2}\bigr)
  \;\le\; 2 \exp\bigl(-c_d \, \lambda^{2/d}\bigr).
$$

**Reference:** Janson, *Gaussian Hilbert Spaces*, Theorem 5.10.

**Proof strategy** (Markov + optimize, three lines):
1. By Markov,
   $\mathbb P(|F| > \lambda \|F\|_2) \le \mathbb E |F|^p / (\lambda \|F\|_2)^p$.
2. By Bonami-Nelson on $\mathcal H^{\le d}$,
   $\mathbb E |F|^p \le \bigl((d+1)(p-1)^{d/2}\bigr)^p \, \|F\|_2^p$.
3. Combined: $\mathbb P(\dots) \le \bigl((d+1)(p-1)^{d/2} / \lambda\bigr)^p
   = (d+1)^p \exp\bigl(p[(d/2)\log(p-1) - \log \lambda]\bigr)$.
4. Set $p - 1 = (\lambda / ((d+1) e))^{2/d}$ to make the exponent
   $\le -d/2 \cdot (\lambda / ((d+1)e))^{2/d}$.
5. The $(d+1)^p$ prefactor is absorbed into the constant for
   $\lambda$ above a threshold $\lambda_0(d)$; below that the bound
   $\le 2$ is trivial. -/
axiom polynomial_chaos_concentration (n d : ℕ) (_hd : 1 ≤ d) :
    ∃ c_d : ℝ, 0 < c_d ∧
      ∀ (F : Lp ℝ 2 (stdGaussianFin n)),
        F ∈ wienerChaosLE n d →
        ∀ (lam : ℝ), 0 < lam →
          (stdGaussianFin n) {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|} ≤
            2 * ENNReal.ofReal (Real.exp (-c_d * lam ^ ((2 : ℝ) / d)))

end MarkovSemigroups.Gaussian
