/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Ornstein-Uhlenbeck on Euclidean Space ℝⁿ

Instance of the abstract OU semigroup (`Diffusion/OrnsteinUhlenbeck.lean`)
for M = ℝⁿ with the standard Gaussian measure γ = N(0, I).

The OU semigroup (Mehler's formula):
  P_t f(x) = ∫ f(e^{-t} x + √(1 - e^{-2t}) y) dγ(y)

Provides:
- `euclideanOUSemigroup` — instance of `OUSemigroup` for ℝⁿ
- `euclideanOU_bakryEmery` — Bakry-Émery curvature ρ = 1
- `euclidean_gaussian_logSobolev` — standard Gaussian satisfies LSI(1)

This is the classical setting of Gross's original 1975 theorem.

## References

- Gross, "Logarithmic Sobolev inequalities," Amer. J. Math. 97 (1975),
  1061–1083
- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 2
-/
