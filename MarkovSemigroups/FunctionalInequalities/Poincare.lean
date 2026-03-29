/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Poincaré Inequality and Spectral Gap

A probability measure μ satisfies a Poincaré inequality with constant
ρ > 0 if:
  Var_μ(f) ≤ (1/ρ) ∫ |∇f|² dμ

for all sufficiently regular f. The optimal constant ρ equals the
spectral gap of the generator L of the associated Markov semigroup:
  ρ = inf { -⟨f, Lf⟩ / ⟨f, f⟩ : f ⊥ constants }

Consequences:
- Exponential decay of variance: Var_μ(P_t f) ≤ e^{-2ρt} Var_μ(f)
- Exponential mixing in L²

## Main results

- `PoincareInequality` — the Poincaré inequality as a predicate on measures
- `poincare_of_spectralGap` — spectral gap implies Poincaré
- `variance_exponential_decay` — Poincaré implies exponential variance decay

## References

- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 4
-/
