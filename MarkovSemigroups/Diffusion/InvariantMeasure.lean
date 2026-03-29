/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Invariant Measures of Diffusion Semigroups

General theory of invariant measures for Markov diffusion semigroups.

A probability measure μ is invariant for a semigroup P_t if
  ∫ P_t f dμ = ∫ f dμ  for all f and all t ≥ 0.

Equivalently, ∫ Lf dμ = 0 for all f in the domain of the generator L.

For the OU semigroup with generator L = Δ - ∇U · ∇, the invariant
measure is the Gibbs measure μ ∝ e^{-U} dx (when it exists and is
normalizable).

## Main results

- `invariantMeasure_of_generator` — μ invariant iff ∫ Lf dμ = 0
- `ouInvariantMeasure_isGaussian` — OU invariant measure is Gaussian
- `invariantMeasure_unique_of_spectralGap` — spectral gap implies
  uniqueness of invariant measure

## References

- Da Prato and Zabczyk, *Stochastic Equations in Infinite Dimensions*,
  Cambridge, 2014, Ch. 11
- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 4
-/
