/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Ornstein-Uhlenbeck Process on Finite-Dimensional Spaces

The OU process on ℝⁿ with drift matrix A and diffusion √2:
  dX_t = -A X_t dt + √2 dW_t

The OU semigroup (Mehler's formula):
  P_t f(x) = ∫ f(e^{-tA} x + √(1 - e^{-2tA}) y) dγ(y)

where γ is the standard Gaussian on ℝⁿ.

## Main results

- `ouSemigroup` — the OU semigroup as a C₀-semigroup on L²(γ)
- `ouSemigroup_mehler` — Mehler's formula
- `ouSemigroup_invariant` — γ is the unique invariant measure

## References

- Nelson, "The free Markoff field," J. Funct. Anal. 12 (1973), 211–227
- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 1
-/
