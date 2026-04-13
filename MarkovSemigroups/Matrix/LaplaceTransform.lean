/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Laplace Transform Representation of the Resolvent

For a positive definite matrix M, the resolvent (inverse) is the
Laplace transform of the semigroup:

  M⁻¹ = ∫₀^∞ exp(-tM) dt

These are Steps 1 of the semigroup proof of the diamagnetic
inequality (§11 of mass-gap-v3.tex).

## References

- Simon, Functional Integration and Quantum Physics (1979), Ch. 22
-/

import MarkovSemigroups.Matrix.HeatKernel

noncomputable section

open Matrix BigOperators

namespace MatrixSemigroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Positive definite matrices -/

/-- A real symmetric matrix is positive definite: all eigenvalues > 0.
We use the concrete characterization: x^T M x > 0 for all x ≠ 0. -/
def IsPosDef (M : Matrix n n ℝ) : Prop :=
  M.IsHermitian ∧ ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ M.mulVec x

/-! ## Laplace transform representations

These axioms state that M⁻¹ and (M+iV)⁻¹ are entrywise equal to
the Laplace transforms of their respective semigroups. The integral
formulation is left abstract since the precise Lean statement involves
`MeasureTheory.integral` over `Set.Ioi 0`, which requires careful
instance management.

The key consequence used downstream is: if exp(-tM) ≥ 0 entrywise
for all t ≥ 0, then M⁻¹ ≥ 0 entrywise (M-matrix theory). -/

/-- **M-matrix inverse is entrywise nonneg.**

If M is PD with nonpositive off-diagonal (a Stieltjes/M-matrix),
then M⁻¹ ≥ 0 entrywise.

Proof: M⁻¹ = ∫₀^∞ exp(-tM) dt (Laplace), and exp(-tM) ≥ 0
(heat kernel positivity for Z-matrices). Integral of nonneg
functions is nonneg.

This is a standard result in M-matrix theory
(Berman-Plemmons, Ch. 6). -/
axiom m_matrix_inverse_nonneg (M : Matrix n n ℝ)
    (hPD : IsPosDef M) (hZ : IsZMatrix M) :
    IsEntryNonneg M⁻¹

end MatrixSemigroup

end
