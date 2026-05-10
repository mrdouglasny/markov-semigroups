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
import SpectralPositivity.Matrix.MMatrixInverse

noncomputable section

open Matrix BigOperators

namespace MatrixSemigroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Positive definite matrices -/

/-- A real symmetric matrix is positive definite: all eigenvalues > 0.
We use the concrete characterization: x^T M x > 0 for all x ≠ 0. -/
def IsPosDef (M : Matrix n n ℝ) : Prop :=
  M.IsHermitian ∧ ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ M.mulVec x

omit [DecidableEq n] in
/-- Bridge from the local `IsPosDef` (using `n → ℝ` quantification) to
Mathlib's `Matrix.PosDef` (using `n →₀ ℝ`).

For real matrices these are equivalent via
`Matrix.posDef_iff_dotProduct_mulVec` (which converts the Finsupp form
to the dotProduct form), and `star x = x` for `x : n → ℝ`. -/
theorem IsPosDef.toMathlib {M : Matrix n n ℝ} (hM : IsPosDef M) : M.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hM.1 ?_
  intro x hx
  have h := hM.2 x hx
  -- Goal: 0 < star x ⬝ᵥ (M *ᵥ x)  vs  h : 0 < x ⬝ᵥ M.mulVec x
  -- For real x, star x = x (entrywise); M.mulVec = M *ᵥ.
  have hstar : (star x : n → ℝ) = x := by
    funext i; exact star_trivial _
  rw [hstar]; exact h

/-! ## Laplace transform representations

These results state that `M⁻¹` is entrywise equal to the Laplace
transform of the semigroup, and as a consequence `M⁻¹` is entrywise
non-negative when `M` is a Stieltjes/M-matrix. The proofs live in
`spectral-positivity` (`SpectralPositivity/Matrix/MMatrixInverse.lean`)
where the spectral-decomposition Laplace identity and the Metzler
exponential nonnegativity are assembled. We re-export here under the
historical `m_matrix_inverse_nonneg` name. -/

/-- **M-matrix inverse is entrywise nonneg.**

If M is PD with nonpositive off-diagonal (a Stieltjes/M-matrix),
then M⁻¹ ≥ 0 entrywise.

Proof (now discharged): `M⁻¹ = ∫₀^∞ exp(-tM) dt`
(`SpectralPositivity.laplace_transform_inverse_real`, via spectral
diagonalization), and `exp(-tM) ≥ 0` entrywise for `t ≥ 0`
(`SpectralPositivity.metzler_exp_nonneg` applied to `-M`, no
irreducibility needed). Integral of nonneg functions is nonneg.

Re-export of `SpectralPositivity.Matrix.MMatrix.inverse_nonneg`
(originally axiomatized in markov-semigroups before spectral-positivity
was wired in 2026-05-02).

Reference: Berman-Plemmons, *Nonnegative Matrices in the Mathematical
Sciences*, Ch. 6, Thm 4.16. -/
theorem m_matrix_inverse_nonneg (M : Matrix n n ℝ)
    (hPD : IsPosDef M) (hZ : IsZMatrix M) :
    IsEntryNonneg M⁻¹ :=
  fun x y =>
    SpectralPositivity.Matrix.MMatrix.inverse_nonneg M hPD.toMathlib hZ x y

end MatrixSemigroup

end
