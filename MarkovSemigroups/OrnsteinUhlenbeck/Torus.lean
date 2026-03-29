/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Ornstein-Uhlenbeck Process on the Torus T^d_L

The OU process on T^d with generator Δ - m² decomposes into independent
1D OU processes on each Fourier mode:

  dz_k = -λ_k z_k dt + √2 dβ_k

where λ_k = 4π²|k|²/L² + m² are the eigenvalues of -Δ + m² on T^d
and β_k are independent standard Brownian motions.

The stationary solution is:
  z_k(t) = √2 ∫_{-∞}^t e^{-λ_k(t-s)} dβ_k(s)

with variance E[|z_k|²] = 1/λ_k.

## Main results

- `torusOUSemigroup` — the OU semigroup on L²(T^d) via Fourier modes
- `torusOUSemigroup_stronglyContinuous` — instance as C₀-semigroup
- `torusOU_spectralGap` — spectral gap = m² + 4π²/L² (first nonzero eigenvalue)

## References

- Da Prato and Zabczyk, *Stochastic Equations in Infinite Dimensions*,
  Cambridge, 2014, Ch. 5
-/
