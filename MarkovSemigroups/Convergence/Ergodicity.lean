/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Ergodicity of Markov Semigroups

A Markov semigroup with spectral gap is ergodic: the invariant measure
is unique and time averages converge to space averages:

  (1/T) ∫₀ᵀ f(X_t) dt → μ(f)   as T → ∞

This is the Markov semigroup version of ergodicity (OS4) in QFT.

## Main results

- `ergodic_of_spectralGap` — spectral gap implies ergodicity
- `timeAverage_converges` — convergence of time averages
- `invariantMeasure_unique` — uniqueness from spectral gap

## References

- Da Prato and Zabczyk, *Stochastic Equations in Infinite Dimensions*,
  Cambridge, 2014, Ch. 11
-/
