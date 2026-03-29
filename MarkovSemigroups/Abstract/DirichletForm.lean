/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dirichlet Forms and Markov Generators

A symmetric Dirichlet form on a probability space (X, μ) is a closed
symmetric bilinear form E : D(E) × D(E) → ℝ satisfying the Markov
property: if f ∈ D(E), then (f ∧ 1) ∨ 0 ∈ D(E) and
E((f ∧ 1) ∨ 0) ≤ E(f).

The associated generator L is the unique self-adjoint operator with
E(f, g) = -⟨f, Lg⟩_{L²(μ)} for f ∈ D(E), g ∈ D(L).

This provides the abstract foundation for all functional inequalities
(Poincaré, log-Sobolev, etc.) without reference to any geometry.

## Main definitions

- `DirichletForm` — symmetric Dirichlet form on a measure space
- `DirichletForm.generator` — associated self-adjoint generator
- `DirichletForm.semigroup` — associated Markov semigroup P_t = e^{tL}

## References

- Fukushima, Oshima, and Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, de Gruyter, 2011
- Ma and Röckner, *Introduction to the Theory of (Non-Symmetric)
  Dirichlet Forms*, Springer, 1992
- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 1
-/
