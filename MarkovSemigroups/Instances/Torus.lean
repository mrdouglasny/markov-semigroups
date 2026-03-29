/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Ornstein-Uhlenbeck on the Torus T^d_L

Instance of the abstract OU semigroup (`Diffusion/OrnsteinUhlenbeck.lean`)
for M = T^d_L = (ℝ/Lℤ)^d with the massive Laplacian Δ - m².

The OU process decomposes into independent 1D OU processes on each
Fourier mode:
  dz_k = -λ_k z_k dt + √2 dβ_k

where λ_k = 4π²|k|²/L² + m² are the eigenvalues of -Δ + m² on T^d
and β_k are independent standard Brownian motions.

Provides:
- `torusHeatSemigroup` — e^{t(Δ - m²)} as a C₀-semigroup
  (instance of `StronglyContinuousSemigroup` from hille-yosida)
- `torusOUSemigroup` — the OU semigroup on L²(T^d)
- `torusOU_spectralGap` — gap = m² + 4π²/L² (first nonzero eigenvalue)
- `torusOU_bakryEmery` — Bakry-Émery curvature ρ = m²
- `torusGaussian_logSobolev` — GFF on T^d satisfies LSI(m² + 4π²/L²)

## References

- Da Prato and Zabczyk, *Stochastic Equations in Infinite Dimensions*,
  Cambridge, 2014, Ch. 5
-/
