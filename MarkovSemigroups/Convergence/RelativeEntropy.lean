/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Relative Entropy and Convergence to Equilibrium

The relative entropy (Kullback-Leibler divergence) of μ with respect
to the invariant measure μ_∞ decays exponentially under the semigroup:

  H(P_t^* μ | μ_∞) ≤ e^{-2ρt} H(μ | μ_∞)

when μ_∞ satisfies the log-Sobolev inequality with constant ρ. This is
the strongest form of convergence to equilibrium: it implies convergence
in total variation (Pinsker) and in Wasserstein distance (transport
inequalities).

## Main results

- `relativeEntropy_decay` — exponential decay of H under the semigroup
- `totalVariation_decay` — Pinsker: ‖P_t^* μ - μ_∞‖_TV ≤ √(2 H(μ | μ_∞))
- `convergence_rate` — explicit rate from LSI constant

## References

- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 5
-/
