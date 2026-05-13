# CLAUDE.md

## Project Overview

Markov semigroups, functional inequalities, and convergence to
equilibrium in Lean 4. Started as the Holley-Stroock path from
Gaussian log-Sobolev to interacting spectral gap (for P(Φ)₂ on the
torus), then grew into a general library — Dirichlet forms,
Bakry-Émery theory, Brascamp-Lieb, Doeblin mixing, TV coupling, and
Dobrushin uniqueness with distance-aware Neumann series. The
Dobrushin layer is consumed by
[lgt](https://github.com/mrdouglasny/lgt) for the lattice Yang-Mills
mass gap.

See `README.md` for the current proved-results listing and
`status.md` for the sorry/axiom audit. `docs/plan.md` is the
original development plan — kept for historical context; current
state is what README/status say.

## Plans and history

Active multi-step planning docs go in [`plans/`](plans/) — see
[`plans/README.md`](plans/README.md) for the index of currently
active plans.

When a plan completes:
1. Move the plan file to [`plans/archive/`](plans/archive/).
2. Add a structured entry to [`plans/history.md`](plans/history.md)
   with:
   * Date completed.
   * Commits delivering the work.
   * Resources used (wall-clock time, lines of code, subagents
     dispatched, Gemini vetting calls).
   * Outcome (what landed, deviations from plan if any).
   * Lessons learned — patterns worth repeating or traps to avoid.

The history log is the canonical place to look up "how long did X
take" or "what was the proof pattern for Y" when scoping a new
project.

## Build

```bash
lake build
```

Dependencies (pinned in `lakefile.toml`):
- **Mathlib** (v4.29.0)
- **hille-yosida** — C₀-semigroup framework
- **gaussian-field** — Gaussian measure library

## File Structure (actual layout)

```
MarkovSemigroups/
  Abstract/                     -- Layer 1: Dirichlet form + measure
    DirichletSpace.lean         --   Dirichlet space typeclass
    Poincare.lean               --   Poincaré inequality
    LogSobolev.lean             --   Log-Sobolev inequality
    HolleyStroock.lean          --   Bounded perturbation of LSI
    Hypercontractivity.lean     --   LSI ↔ hypercontractivity (Gross, 2 axioms)
  Diffusion/                    -- Layer 2: carré du champ
    CarreDuChamp.lean           --   Γ operator, Bakry-Émery Poincaré/LSI
    BakryEmerySpace.lean        --   Curvature typeclass
    L2Bridge.lean               --   L² connections
  Convergence/                  -- Consequences (Layer 1 is enough)
    SpectralGap.lean            --   Exponential mixing from spectral gap
    RelativeEntropy.lean        --   Entropy decay
    Ergodicity.lean             --   Unique invariant measure
    IntegralBounds.lean         --   TV-integral bound (layer cake)
    Doeblin.lean                --   Doeblin condition + n-step mixing
  Coupling/                     -- TV coupling theory
    TVCoupling.lean             --   tvDist = inf disagreement; maximal coupling
    CanonicalCoupling.lean      --   Constructive pointwise-min coupling
    DobrushinCoupling.lean      --   Iterated Dobrushin coupling (finite S)
    ProkhorovCoupling.lean      --   Compact-S version via Prokhorov
  Dobrushin/                    -- Lattice spin systems
    Specification.lean          --   Gibbs specifications
    Uniqueness.lean             --   Dobrushin uniqueness theorem
    StrongCoupling.lean         --   Strong-coupling verification
    CovarianceBound.lean        --   Single-site covariance bounds
    CondTVBridge.lean           --   Conditional TV + disintegration
    CovarianceBoundMultisite.lean -- Multi-site via condKernel (used by lgt)
    CondKernelDLR.lean          --   condKernel fiber inherits DLR
    NeumannSeries.lean          --   Neumann series / distance-aware bound
    FiniteLattice.lean          --   Finite lattice distance structure
  Instances/                    -- Concrete spaces (sorry-free)
    BrascampLieb.lean           --   Brascamp-Lieb inequality (proved)
    Torus.lean                  --   Torus heat semigroup (header)
    GFFIdentification.lean      --   OU invariant = GFF (header)
    WorkInProgress/             -- Concrete spaces with sorries (honest)
      TwoPoint.lean             --   {0,1} uniform (2 sorry's = math false)
      Euclidean.lean            --   Standard Gaussian (9 sorry's = Lean gaps)
  Matrix/                       -- Finite matrix semigroup theory
    HeatKernel.lean             --   exp(-tM) ≥ 0 for Z-matrices (proved)
    LaplaceTransform.lean       --   M⁻¹ = ∫exp(-tM) dt (1 axiom)
    Trotter.lean                --   Lie-Trotter product formula (proved)
    Diamagnetic.lean            --   |(M+iV)⁻¹| ≤ M⁻¹ entrywise (1 axiom)
```

## Lean 4 Working Methods

### Build-First Workflow

Always build before and after changes. Use `lake build` to check the
full project. `lake build MarkovSemigroups.Dobrushin.NeumannSeries`
(etc.) for targeted rebuilds.

### Key Dependencies

- **hille-yosida**: `StronglyContinuousSemigroup`, `ContractingSemigroup`,
  `resolvent`, `hilleYosidaResolventBound`.
- **gaussian-field**: `GaussianField.measure`,
  `gaussian_measure_unique_of_covariance`, hypercontractivity.
- **Mathlib**: `condKernel` disintegration, measure theory, Giry
  monad, Portmanteau / Prokhorov, entropy.

## References

- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov
  Diffusion Operators*, Springer, 2014.
- Dobrushin, "Description of a random field by means of conditional
  probabilities," *Teor. Veroyatnost. i Primenen.* 13 (1968).
- Gross, "Logarithmic Sobolev inequalities," *Amer. J. Math.* 97
  (1975).
- Holley and Stroock, "Logarithmic Sobolev inequalities and
  stochastic Ising models," *J. Stat. Phys.* 46 (1987).
- Georgii, *Gibbs Measures and Phase Transitions*, de Gruyter, 1988.
