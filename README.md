# markov-semigroups

Markov semigroups, functional inequalities, and convergence to
equilibrium in Lean 4. Built on the
[hille-yosida](https://github.com/mrdouglasny/hille-yosida) C₀-semigroup
framework and [gaussian-field](https://github.com/mrdouglasny/gaussian-field)
Gaussian measure library.

## What this project proves

The central result chain:

1. The **Ornstein-Uhlenbeck semigroup** on T^d with generator Δ - m² is
   a C₀-contraction semigroup on L²(T^d). Its invariant measure is the
   **Gaussian free field** with covariance (-Δ + m²)⁻¹.

2. The Gaussian measure satisfies the **log-Sobolev inequality** with
   constant ρ = m² (via the **Bakry-Émery** curvature criterion).

3. The **Holley-Stroock perturbation lemma** transfers the LSI to the
   interacting P(Φ)₂ measure dμ = (1/Z) e^{-V} dμ_GFF with constant
   ρ₁ = ρ₀ · e^{-osc(V)}, where osc(V) is the oscillation of the
   interaction.

4. The LSI implies a **spectral gap** (Poincaré inequality), which gives
   **exponential decay of correlations** (mass gap / clustering) and
   **ergodicity** for the interacting theory.

This provides an alternative proof of the mass gap for P(Φ)₂ on the
torus, bypassing cluster expansions entirely.

## File structure

```
MarkovSemigroups/
  OrnsteinUhlenbeck/
    FiniteDimensional.lean    -- OU on ℝⁿ, Mehler formula
    Torus.lean                -- OU on T^d via Fourier modes
    InvariantMeasure.lean     -- Gaussian invariant measure
    GFFIdentification.lean    -- OU invariant measure = GFF
  FunctionalInequalities/
    Poincare.lean             -- Spectral gap → variance decay
    LogSobolev.lean           -- Gross LSI for Gaussian measures
    BakryEmery.lean           -- Γ₂ ≥ ρΓ criterion
    HolleyStroock.lean        -- Bounded perturbation of LSI
    Hypercontractivity.lean   -- LSI ↔ hypercontractivity (Gross)
  Convergence/
    RelativeEntropy.lean      -- Entropy decay under semigroup
    SpectralGap.lean          -- Exponential mixing from gap
    Ergodicity.lean           -- Uniqueness of invariant measure
```

## The Holley-Stroock path to the mass gap

The key application: on the torus T²_L, the P(Φ)₂ interacting measure

  dμ_a = (1/Z_a) exp(-V_a) dμ_GFF

is a **bounded perturbation** of the GFF (because the Wick-ordered
interaction V_a is bounded below by -L²A and the torus has finite
volume). The GFF satisfies the log-Sobolev inequality with constant
ρ₀ = m² (Bakry-Émery). By Holley-Stroock:

  ρ₁ = m² · exp(-osc(V_a)) ≥ m² · exp(-2L²A)

This gives a spectral gap (mass gap) bounded below **uniformly in the
lattice spacing a**, because A depends only on the interaction
polynomial P and the mass m (via `wickPolynomial_uniform_bounded_below`),
not on the lattice size N.

This eliminates the need for cluster expansions to prove
`spectral_gap_uniform` on the torus.

## Dependencies

- [hille-yosida](https://github.com/mrdouglasny/hille-yosida) — C₀-semigroup
  theory, generators, resolvents, Hille-Yosida bound
- [gaussian-field](https://github.com/mrdouglasny/gaussian-field) — Gaussian
  measures on nuclear spaces, hypercontractivity, tightness
- [Mathlib](https://github.com/leanprover-community/mathlib4) — Lean 4
  mathematics library

## Building

```bash
lake update
lake build
```

## References

- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014.
- Gross, "Logarithmic Sobolev inequalities," *Amer. J. Math.* 97 (1975),
  1061-1083.
- Holley and Stroock, "Logarithmic Sobolev inequalities and stochastic
  Ising models," *J. Stat. Phys.* 46 (1987), 1159-1194.
- Da Prato and Zabczyk, *Stochastic Equations in Infinite Dimensions*,
  Cambridge, 2014.
- Nelson, "The free Markoff field," *J. Funct. Anal.* 12 (1973), 211-227.

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
