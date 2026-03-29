/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Identification: OU Invariant Measure = Gaussian Free Field

The invariant measure of the OU process on T^d equals the Gaussian free
field measure constructed in the gaussian-field library.

Both are centered Gaussian measures with covariance (-Δ + m²)⁻¹ (up to
the factor of 1/2 from the normalization convention). By uniqueness of
Gaussian measures with given covariance (`gaussian_measure_unique_of_covariance`
from gaussian-field), they are equal.

This is the free-field case (P = 0) of stochastic quantization:
the Langevin dynamics for the free action ½⟨φ, (-Δ + m²)φ⟩ has the
GFF as its equilibrium distribution.

## Main results

- `torusOU_invariantMeasure_eq_gff` — the OU invariant measure on T^d
  equals the GFF measure from gaussian-field

## References

- Nelson, "The free Markoff field," J. Funct. Anal. 12 (1973), 211–227
- Simon, *The P(φ)₂ Euclidean QFT*, Princeton, 1974, Ch. I
-/
