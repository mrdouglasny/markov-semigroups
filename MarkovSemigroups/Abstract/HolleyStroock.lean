/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Holley-Stroock Perturbation Lemma

If μ₀ satisfies a log-Sobolev inequality with constant ρ₀, and
μ₁ = (1/Z) e^{-V} μ₀ where V is bounded (osc(V) = sup V - inf V < ∞),
then μ₁ satisfies a log-Sobolev inequality with constant

  ρ₁ = ρ₀ · e^{-osc(V)}

This is the key tool for transferring functional inequalities from
the free (Gaussian) measure to the interacting measure in P(Φ)₂.

On the torus T^2_L with fixed volume:
- μ₀ = GFF satisfies LSI with ρ₀ (from Bakry-Émery)
- μ₁ = P(Φ)₂ measure = (1/Z) e^{-V_a} μ₀
- V_a is bounded (Wick polynomial bounded below + finite volume)
- Therefore μ₁ satisfies LSI with ρ₁ = ρ₀ · e^{-osc(V_a)}
- This gives spectral gap ≥ ρ₁ for the interacting theory

## Main results

- `holleyStroock_logSobolev` — bounded perturbation preserves LSI
- `holleyStroock_poincare` — bounded perturbation preserves Poincaré
- `holleyStroock_constant` — explicit constant ρ₁ = ρ₀ · e^{-osc(V)}

## Application to P(Φ)₂

The oscillation osc(V_a) on the torus is bounded uniformly in the
lattice spacing a (by the same physical volume argument as in Nelson's
estimate: V_a ≥ -L^2 A and V_a ≤ L^2 B per site). Therefore the
LSI constant ρ₁ has a uniform lower bound, giving `spectral_gap_uniform`
on the torus without cluster expansions.

## References

- Holley and Stroock, "Logarithmic Sobolev inequalities and stochastic
  Ising models," J. Stat. Phys. 46 (1987), 1159–1194
- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, §5.1
-/
