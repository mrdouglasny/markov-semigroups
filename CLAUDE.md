# CLAUDE.md

## Project Overview

Markov semigroups, functional inequalities, and convergence to
equilibrium in Lean 4. The main goal is the Holley-Stroock path
from Gaussian log-Sobolev to interacting spectral gap, providing
a mass gap proof for P(Φ)₂ on the torus without cluster expansions.

See `docs/plan.md` for the full development plan.

## Build

```bash
lake build
```

Dependencies: hille-yosida (C₀-semigroups), gaussian-field (GFF),
Mathlib.

## File Structure

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

## Critical Path

The highest-value sequence is:
1. `Torus.lean` — heat semigroup instance
2. `LogSobolev.lean` — Gross LSI for Gaussian
3. `HolleyStroock.lean` — bounded perturbation of LSI
4. `SpectralGap.lean` — spectral gap from Poincaré
5. Application in pphi2 — eliminates `spectral_gap_uniform`

## Lean 4 Working Methods

### Build-First Workflow

Always build before and after changes. Use `lake build` to check the
full project.

### Key Dependencies

- **hille-yosida**: `StronglyContinuousSemigroup`, `ContractingSemigroup`,
  `resolvent`, `hilleYosidaResolventBound`
- **gaussian-field**: `GaussianField.measure`, `gaussian_hypercontractive`,
  `gaussian_measure_unique_of_covariance`, `DyninMityaginSpace`
- **Mathlib**: L² spaces, Fourier analysis, measure theory, entropy

## References

- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014
- Gross, "Logarithmic Sobolev inequalities," Amer. J. Math. 97 (1975)
- Holley and Stroock, "Logarithmic Sobolev inequalities and stochastic
  Ising models," J. Stat. Phys. 46 (1987)
