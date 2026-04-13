/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lie-Trotter Product Formula for Finite Matrices

The Lie-Trotter product formula:

  exp(A + B) = lim_{n→∞} (exp(A/n) · exp(B/n))^n

for finite matrices A, B. This is Step 2 of the semigroup proof
of the diamagnetic inequality (§11 of mass-gap-v3.tex).

## Proof sketch

For finite matrices, this follows from Baker-Campbell-Hausdorff:
  exp(A/n) exp(B/n) = exp((A+B)/n + [A,B]/(2n²) + ...)
  = exp((A+B)/n + O(1/n²))

So (exp(A/n) exp(B/n))^n = exp(A+B + O(1/n)) → exp(A+B).

Mathlib has `NormedSpace.exp_add_of_commute` for the commuting case.
The general (non-commuting) case requires norm estimates on the
BCH remainder.

## References

- Trotter, Proc. Amer. Math. Soc. 10 (1959), 545-551
- Reed-Simon I, §VIII.8
-/

import MarkovSemigroups.Matrix.HeatKernel

noncomputable section

open Matrix BigOperators

namespace MatrixSemigroup

variable {n : Type*} [Fintype n] [DecidableEq n]

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-- **Lie-Trotter product formula for finite matrices.**

exp(A + B) = lim_{n→∞} (exp(A/n) · exp(B/n))^n

The convergence is in the operator norm. For finite matrices
this follows from BCH (Baker-Campbell-Hausdorff):
exp(X)exp(Y) = exp(X + Y + [X,Y]/2 + ...) and the remainder
is O(‖X‖·‖Y‖) when ‖X‖, ‖Y‖ are small. -/
axiom trotter_product_formula (A B : Matrix n n ℂ) :
    Filter.Tendsto
      (fun k : ℕ => ((NormedSpace.exp ((1 / (k : ℂ)) • A)) *
                      (NormedSpace.exp ((1 / (k : ℂ)) • B))) ^ k)
      Filter.atTop
      (nhds (NormedSpace.exp (A + B)))

end MatrixSemigroup

end
