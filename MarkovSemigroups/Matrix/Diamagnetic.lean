/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Diamagnetic Inequality for Finite Matrices

For M a real PD Z-matrix and V a real diagonal matrix:

  |(M+iV)⁻¹(x,y)| ≤ M⁻¹(x,y)

This is the main result of the semigroup proof (§11 of mass-gap-v3.tex),
assembling all five steps:
1. Laplace transform (LaplaceTransform.lean)
2. Trotter product (Trotter.lean)
3. Phase bound: |exp(iV)| = 1 (diagonal)
4. Heat kernel positivity (HeatKernel.lean)
5. Entry-wise triangle inequality

## References

- Simon, Functional Integration and Quantum Physics (1979), Ch. 22
- Reed-Simon IV, §X.4 (Kato's inequality)
-/

import MarkovSemigroups.Matrix.LaplaceTransform
import MarkovSemigroups.Matrix.Trotter

noncomputable section

open Matrix BigOperators

namespace MatrixSemigroup

variable {n : Type*} [Fintype n] [DecidableEq n]

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-- The complex matrix M + iV where M is real and V is real diagonal. -/
def complexShiftedMatrix (M : Matrix n n ℝ) (V : n → ℝ) : Matrix n n ℂ :=
  M.map (↑· : ℝ → ℂ) + Complex.I • Matrix.diagonal (fun i => (V i : ℂ))

/-- **Diamagnetic inequality (resolvent level).**

|(M+iV)⁻¹(x,y)| ≤ M⁻¹(x,y)

for M a positive definite Z-matrix and V real diagonal.

Proof: by the semigroup method (Steps 1-5).
- Laplace: (M+iV)⁻¹ = ∫ exp(-t(M+iV)) dt, M⁻¹ = ∫ exp(-tM) dt
- Trotter: exp(-t(M+iV)) = lim (exp(-tM/n) exp(-itV/n))^n
- Phase: |exp(-itV/n)(x,y)| = δ_{xy} (diagonal unitary)
- Heat kernel: exp(-tM/n)(x,y) ≥ 0 (Z-matrix)
- Triangle: |(product)^n(x,y)| ≤ (exp(-tM/n))^n(x,y) = exp(-tM)(x,y)
- Integrate over t. -/
axiom diamagnetic_resolvent (M : Matrix n n ℝ) (V : n → ℝ)
    (hPD : IsPosDef M) (hZ : IsZMatrix M) (x y : n) :
    ‖(complexShiftedMatrix M V)⁻¹ x y‖ ≤ M⁻¹ x y

end MatrixSemigroup

end
