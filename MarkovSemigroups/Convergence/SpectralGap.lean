/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Spectral Gap and Exponential Mixing

The spectral gap λ₁ of the generator L gives exponential decay of
correlations:

  |⟨f, P_t g⟩ - μ(f)μ(g)| ≤ e^{-λ₁ t} · ‖f‖_2 · ‖g‖_2

This is the Markov semigroup version of the mass gap in QFT: the
spectral gap of the generator equals the physical mass gap, and
exponential mixing equals clustering (OS4).

## Main results

- `spectralGap_mixing` — spectral gap implies exponential mixing
- `spectralGap_variance_decay` — Var(P_t f) ≤ e^{-2λ₁t} Var(f)
- `spectralGap_of_poincare` — Poincaré constant = spectral gap

## References

- Reed and Simon, *Methods of Modern Mathematical Physics*, Vol. IV, 1978
- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 4
-/
