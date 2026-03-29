/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Invariant Measure of the OU Process

The unique invariant measure of the OU process on T^d with generator
Δ - m² is the Gaussian measure with covariance (-Δ + m²)⁻¹/2.

In Fourier modes: the invariant distribution of z_k is N(0, 1/(2λ_k)),
so the covariance of the invariant measure is:
  E[Φ(f) Φ(g)] = (1/2) ⟨f, (-Δ + m²)⁻¹ g⟩

## Main results

- `torusOU_invariantMeasure` — the invariant measure exists and is Gaussian
- `torusOU_invariantMeasure_unique` — uniqueness (from ergodicity of OU)
- `torusOU_invariantMeasure_covariance` — covariance = (1/2)(-Δ + m²)⁻¹

## References

- Da Prato and Zabczyk, *Stochastic Equations in Infinite Dimensions*,
  Cambridge, 2014, Ch. 11
-/
