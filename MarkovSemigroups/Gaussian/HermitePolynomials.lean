/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multivariate Hermite Polynomials

Defines multivariate (probabilist's) Hermite polynomials on
`Fin n → ℝ` and proves their orthogonality under the standard
multivariate Gaussian measure. Multivariate Hermite is the
tensor product of the 1D Hermite polynomials already in Mathlib
(`Mathlib.RingTheory.Polynomial.Hermite.Basic`).

## Main definitions

- `hermiteMulti α` — multivariate Hermite for multi-index
  `α : Fin n → ℕ`.
- `hermiteMultiEval α x` — its evaluation at `x : Fin n → ℝ`.
- `MultiIndex.totalDegree α` — `∑ i, α i`.

## Main theorems

- `hermiteMulti_orthogonality` — under the standard Gaussian on
  `Fin n → ℝ`, distinct multivariate Hermites are orthogonal,
  and `‖H_α‖² = ∏ᵢ αᵢ!`.

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), §3.1
  (Hermite polynomials) and Theorem 3.21 (orthogonality).
- D. Nualart, *The Malliavin Calculus and Related Topics*, Springer
  (2006), §1.1.

## Status

API + axiom skeleton (2026-05-08). Definitions are concrete; the
orthogonality theorem is axiomatized with a textbook citation and
proof-strategy docstring (Fubini on the tensor product + 1D
orthogonality from Mathlib's `Polynomial.hermite_orthogonality`
chain). Awaiting downstream consumer (`WienerChaos.lean`).
-/

import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import SchwartzNuclear.HermiteWick
import GaussianField.WickMultivariate

noncomputable section

open MeasureTheory GaussianField

namespace MarkovSemigroups.Gaussian

/-- Total degree of a multi-index. -/
def MultiIndex.totalDegree {n : ℕ} (α : Fin n → ℕ) : ℕ := ∑ i, α i

/-- Evaluation of the 1D probabilist's Hermite polynomial of degree `k`
at a real point. Wrapper around Mathlib's `Polynomial.hermite`. -/
noncomputable def hermiteEval (k : ℕ) (x : ℝ) : ℝ :=
  ((Polynomial.hermite k).map (Int.castRingHom ℝ)).eval x

/-- Multivariate (probabilist's) Hermite polynomial evaluated at
`x : Fin n → ℝ`: `H_α(x) = ∏ᵢ H_{αᵢ}(xᵢ)`. -/
noncomputable def hermiteMultiEval {n : ℕ} (α : Fin n → ℕ)
    (x : Fin n → ℝ) : ℝ :=
  ∏ i, hermiteEval (α i) (x i)

/-- The standard multivariate Gaussian measure on `Fin n → ℝ`: product
of `n` copies of the standard 1D Gaussian. -/
noncomputable def stdGaussianFin (n : ℕ) :
    MeasureTheory.Measure (Fin n → ℝ) :=
  MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)

/-- The 1D probabilist's Hermite polynomial evaluated at `x` equals
the unit-variance Wick monomial, via gaussian-field's `wick_eq_hermiteR`. -/
private lemma hermiteEval_eq_wickMonomial_one (k : ℕ) (x : ℝ) :
    hermiteEval k x = wickMonomial k 1 x := by
  unfold hermiteEval
  rw [wick_eq_hermiteR k 1 (by norm_num : (0:ℝ) < 1)]
  show _ = Real.sqrt 1 ^ k * _
  rw [Real.sqrt_one, one_pow, one_mul, div_one]

/-- **Orthogonality of multivariate Hermite polynomials** under the
standard multivariate Gaussian.

  `∫ H_α(x) · H_β(x) dγ(x) = δ_{αβ} · ∏ᵢ αᵢ!`

**Reference:** Janson, *Gaussian Hilbert Spaces*, Theorem 3.21.

**Proof:** Identify the 1D Hermite evaluation with gaussian-field's
unit-variance Wick monomial (`hermiteEval_eq_wickMonomial_one`),
combine the two products into one product of pairs, apply Fubini on
the pi measure (`integral_fintype_prod_eq_prod`), and reduce each
factor to the 1D Wick orthogonality
`wickMonomial_inner_gaussianReal_one`. -/
theorem hermiteMulti_orthogonality {n : ℕ} (α β : Fin n → ℕ) :
    ∫ x : Fin n → ℝ,
      hermiteMultiEval α x * hermiteMultiEval β x ∂(stdGaussianFin n) =
    if α = β then ((∏ i, (α i).factorial : ℕ) : ℝ) else 0 := by
  -- Step 1: combine the two products into one product of pairs and
  -- replace `hermiteEval` by `wickMonomial _ 1`.
  have h_eq : ∀ x : Fin n → ℝ,
      hermiteMultiEval α x * hermiteMultiEval β x =
      ∏ i, wickMonomial (α i) 1 (x i) * wickMonomial (β i) 1 (x i) := by
    intro x
    unfold hermiteMultiEval
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro i _
    rw [hermiteEval_eq_wickMonomial_one, hermiteEval_eq_wickMonomial_one]
  simp_rw [h_eq]
  -- Step 2: Fubini on the pi measure splits the integral as a product.
  unfold stdGaussianFin
  rw [integral_fintype_prod_eq_prod
    (f := fun i (x : ℝ) => wickMonomial (α i) 1 x * wickMonomial (β i) 1 x)]
  -- Step 3: each factor is the 1D Wick orthogonality.
  simp_rw [wickMonomial_inner_gaussianReal_one]
  -- Step 4: combine the per-coordinate indicators into the multi-index indicator.
  by_cases hαβ : α = β
  · rw [if_pos hαβ]
    rw [show (∏ i : Fin n,
        if α i = β i then (((α i).factorial : ℕ) : ℝ) else 0) =
        ∏ i : Fin n, ((α i).factorial : ℝ) from by
      refine Finset.prod_congr rfl ?_
      intro i _
      rw [if_pos (by rw [hαβ] : α i = β i)]]
    push_cast
    rfl
  · rw [if_neg hαβ]
    -- Some i has α i ≠ β i, so that factor is 0.
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
      by_contra h
      push Not at h
      exact hαβ (funext h)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [if_neg hi]

/-- **Multivariate Hermite polynomials are nonzero in L²(γ).**

Immediate corollary of the orthogonality: `‖H_α‖_{L²}² = ∏ᵢ αᵢ! ≥ 1 > 0`. -/
theorem hermiteMulti_l2_pos {n : ℕ} (α : Fin n → ℕ) :
    0 < ∫ x : Fin n → ℝ,
      hermiteMultiEval α x * hermiteMultiEval α x ∂(stdGaussianFin n) := by
  rw [hermiteMulti_orthogonality, if_pos rfl]
  exact_mod_cast Finset.prod_pos (fun i _ => Nat.factorial_pos (α i))

/-- **Density of multivariate Hermite polynomials in L²(γ).**

The polynomial subalgebra generated by the coordinate functions
$\{x_i\}$ is dense in $L^2(\gamma)$ for $\gamma$ a non-degenerate
finite-dimensional Gaussian. By Gram-Schmidt on the multivariate
Hermite family (which is graded-orthogonal by total degree under
the standard Gaussian), the Hermite family forms a complete
orthogonal system.

**Reference:** Janson, *Gaussian Hilbert Spaces*, Theorem 2.6 +
Theorem 3.21. -/
axiom hermiteMulti_dense {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (_hf : MeasureTheory.MemLp f 2 (stdGaussianFin n))
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℝ),
      (∫ x, |f x - ∑ α ∈ s, c α * hermiteMultiEval α x| ^ 2 ∂(stdGaussianFin n)) < ε

end MarkovSemigroups.Gaussian
