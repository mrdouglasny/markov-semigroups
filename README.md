# markov-semigroups

Markov semigroups, functional inequalities, and convergence to
equilibrium in Lean 4. Built on the
[hille-yosida](https://github.com/mrdouglasny/hille-yosida) C₀-semigroup
framework and [gaussian-field](https://github.com/mrdouglasny/gaussian-field)
Gaussian measure library.

## What this project proves

The central result chain:

1. **Abstract functional inequalities** (Poincaré, log-Sobolev,
   Holley-Stroock perturbation) for general Dirichlet forms and Markov
   semigroups — no geometry required.

2. **Bakry-Émery curvature criterion** for diffusion generators on
   Riemannian manifolds: $\Gamma_2 \geq \rho \Gamma$ implies LSI($\rho$).

3. **Ornstein-Uhlenbeck semigroup** defined abstractly for any Hilbert
   space with a positive covariance operator. Mehler's formula, Gaussian
   invariant measure, hypercontractivity.

4. **Concrete instances:** R^n (standard Gaussian, Gross's theorem) and
   T^d (torus GFF, Fourier mode decomposition). Identification of the
   OU invariant measure on T^d with the Gaussian free field from
   gaussian-field.

5. **Convergence to equilibrium:** spectral gap → exponential mixing,
   LSI → entropy decay, ergodicity from spectral gap.

## File structure

```
MarkovSemigroups/
  Abstract/                     -- No geometry, just measures + Dirichlet forms
    DirichletForm.lean          -- Symmetric Dirichlet form, generator, semigroup
    Poincare.lean               -- Spectral gap ↔ variance decay
    LogSobolev.lean             -- Gross LSI, entropy decay
    HolleyStroock.lean          -- Bounded density perturbation of LSI
    Hypercontractivity.lean     -- LSI ↔ hypercontractivity (Gross)
  Diffusion/                    -- Riemannian manifold diffusions
    CarreDuChamp.lean           -- Γ and Γ₂ for diffusion generators
    BakryEmery.lean             -- Γ₂ ≥ ρΓ ⟹ LSI(ρ)
    OrnsteinUhlenbeck.lean      -- Abstract OU semigroup on Hilbert space
    InvariantMeasure.lean       -- Invariant measures of diffusion semigroups
  Instances/                    -- Concrete manifolds
    Euclidean.lean              -- ℝⁿ: standard Gaussian, Mehler, LSI(1)
    Torus.lean                  -- T^d: heat semigroup, Fourier modes, LSI(m²+4π²/L²)
    GFFIdentification.lean      -- OU invariant measure on T^d = GFF
  Convergence/                  -- Consequences (abstract)
    SpectralGap.lean            -- Exponential mixing from gap
    RelativeEntropy.lean        -- Entropy decay under semigroup
    Ergodicity.lean             -- Uniqueness of invariant measure
```

## Application to P(Phi)_2

The Gaussian results (Phases 1-3) provide the free-field infrastructure
for stochastic quantization. For the interacting theory, the simple
Holley-Stroock perturbation does not apply (the interaction V_a is
unbounded above, so osc(V) = infinity). See [docs/plan.md](docs/plan.md)
for the Gemini review and three alternative approaches for the
interacting spectral gap.

## Development plan

See [docs/plan.md](docs/plan.md) for the full development plan, timeline,
risk assessment, and Gemini review.

## Dependencies

- [hille-yosida](https://github.com/mrdouglasny/hille-yosida) — C₀-semigroup
  theory, generators, resolvents, Hille-Yosida bound
- [gaussian-field](https://github.com/mrdouglasny/gaussian-field) — Gaussian
  measures on nuclear spaces, hypercontractivity, tightness
- [stochasticpde-itocalculus](https://github.com/mrdouglasny/stochasticpde-itocalculus) —
  Ito calculus (forked from xiyin137)
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
- Fukushima, Oshima, and Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, de Gruyter, 2011.

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
