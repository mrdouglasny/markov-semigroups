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

3. **Brascamp-Lieb inequality** for log-concave measures mu = e^{-V} dx
   with V strictly convex: Var_mu(f) <= integral of (nabla f, (Hess V)^{-1} nabla f) dmu.
   Proven from two analytical axioms (resolvent-IBP + integrated Bochner identity)
   via weighted Young's inequality. Poincare corollary when Hess V >= rho I.

4. **Ornstein-Uhlenbeck semigroup** defined abstractly for any Hilbert
   space with a positive covariance operator. Mehler's formula, Gaussian
   invariant measure, hypercontractivity.

5. **Concrete instances:** R^n (standard Gaussian, Gross's theorem) and
   T^d (torus GFF, Fourier mode decomposition). Identification of the
   OU invariant measure on T^d with the Gaussian free field from
   gaussian-field.

6. **Convergence to equilibrium:** spectral gap → exponential mixing,
   LSI → entropy decay, ergodicity from spectral gap.

7. **TV coupling characterization:** total variation distance equals
   the infimum over couplings of the disagreement probability.
   Maximal coupling construction.

8. **Dobrushin uniqueness theory:** for lattice spin systems on compact
   state spaces, Dobrushin's condition (column sums of influence matrix
   < 1) implies unique Gibbs measure with exponential correlation decay.
   Includes canonical maximal coupling, iterated Dobrushin coupling via
   Prokhorov compactness, multi-site covariance bounds via condKernel
   disintegration, and Neumann series exponential decay. Used by
   [lgt](https://github.com/mrdouglasny/lgt) for the Yang-Mills mass gap.

9. **Diamagnetic inequality** for finite matrices: |(M+iV)^{-1}(x,y)|
   ≤ M^{-1}(x,y) via heat kernel positivity for Z-matrices.

## Architecture: three layers of abstraction

The project is organized into three layers, each requiring progressively
more structure. Most results live in the most general layer possible.

### Layer 1: Abstract/ — Measure space + energy form

**Assumes:** A probability space (X, mu) and a symmetric bilinear form
E(f,g) (the Dirichlet form / energy). No gradient, no metric, no
manifold.

**Typeclass:**
```
class DirichletSpace (X : Type*) where
  mu : Measure X                          -- reference probability measure
  energy : (X -> R) -> (X -> R) -> R      -- Dirichlet form E(f,g)
  -- symmetric, positive, closed, Markov property
```

**What lives here:** Poincare inequality, log-Sobolev inequality,
Holley-Stroock perturbation, Gross equivalence (LSI <-> hypercontractivity),
spectral gap, entropy decay, ergodicity. These are all statements about
E and mu with no geometry.

### Layer 2: Diffusion/ — Abstract diffusion generator

**Assumes:** A Dirichlet space with a *carre du champ* operator
Gamma(f,g), which plays the role of |nabla f|^2 without requiring an
actual gradient or Riemannian metric.

**Typeclass:**
```
class MarkovDiffusion (X : Type*) extends DirichletSpace X where
  Gamma : (X -> R) -> (X -> R) -> (X -> R)    -- carre du champ
  -- E(f,g) = integral Gamma(f,g) d mu
```

On a Riemannian manifold, Gamma(f,g) = <nabla f, nabla g>. But the
abstract definition works for any diffusion generator. The iterated
carre du champ Gamma_2 and the Bakry-Emery curvature condition
Gamma_2 >= rho * Gamma are defined at this level. The Bochner-Weitzenbock
formula (connecting Gamma_2 to Ricci curvature) is a *theorem* for
specific instances, not part of the axioms.

**What lives here:** Bakry-Emery criterion, carre du champ, iterated
carre du champ, abstract Ornstein-Uhlenbeck semigroup, invariant measures.

### Layer 3: Instances/ — Concrete spaces

**Assumes:** A specific space with explicit structure.

- **Euclidean.lean** (R^n): Gamma(f,g) = <nabla f, nabla g> via Mathlib's
  `fderiv`. Standard Gaussian, Mehler formula, Bakry-Emery curvature = 1.
- **Torus.lean** (T^d): Fourier eigenvalues lambda_k = 4 pi^2 |k|^2 / L^2 + m^2.
  Heat semigroup as Fourier multiplier. Bakry-Emery curvature = m^2.
  No dependence on Mathlib's manifold library — the torus is handled
  entirely via its Fourier decomposition.
- **GFFIdentification.lean**: OU invariant measure on T^d equals the
  Gaussian free field from gaussian-field (by covariance uniqueness).

### Why no Riemannian manifold library?

The Bakry-Emery framework is designed to avoid needing the full
Riemannian apparatus. The carre du champ Gamma is an *abstract*
bilinear operation satisfying axioms, not necessarily <nabla f, nabla g>
on a smooth manifold. For R^n we use Mathlib's `fderiv`; for T^d we use
Fourier modes. If someone later wants to add a general Riemannian
instance (using Mathlib's `SmoothManifold`), the abstract layers are
ready for it.

## File structure

```
MarkovSemigroups/
  Abstract/                     -- Layer 1: measures + Dirichlet forms
    DirichletForm.lean          -- Symmetric Dirichlet form, variance, entropy
    Poincare.lean               -- Spectral gap <-> variance decay
    LogSobolev.lean             -- Gross LSI, entropy decay
    HolleyStroock.lean          -- Bounded density perturbation of LSI
    Hypercontractivity.lean     -- LSI <-> hypercontractivity (Gross)
  Diffusion/                    -- Layer 2: abstract diffusions (Gamma, Gamma_2)
    CarreDuChamp.lean           -- BakryEmerySpace: Gamma, semigroup, curvature
    L2Semigroup.lean            -- Bridge to hille-yosida semigroup theory
  Instances/                    -- Layer 3: concrete spaces
    Euclidean.lean              -- R: standard Gaussian, OU semigroup, rho=1
    TwoPoint.lean               -- {0,1}: simplest instance (19/21 fields proved)
    Torus.lean                  -- T^d: heat semigroup, Fourier modes (header)
    GFFIdentification.lean      -- OU invariant on T^d = GFF (header)
    BrascampLieb.lean           -- Brascamp-Lieb for log-concave measures
  Convergence/                  -- Consequences (uses Layer 1 only)
    SpectralGap.lean            -- Exponential mixing from gap
    RelativeEntropy.lean        -- Entropy decay under semigroup
    Ergodicity.lean             -- Uniqueness of invariant measure
    IntegralBounds.lean         -- TV-integral bound (layer cake)
    Doeblin.lean                -- Doeblin's condition, n-step mixing
  Coupling/                     -- Coupling theory
    TVCoupling.lean             -- TV = inf coupling disagreement, maximal coupling
    CanonicalCoupling.lean      -- Constructive pointwise-min coupling, Giry measurability
    DobrushinCoupling.lean      -- Iterated Dobrushin coupling via min-disagreement
    ProkhorovCoupling.lean      -- Prokhorov coupling for compact spin spaces (0 sorry)
  Dobrushin/                    -- Dobrushin uniqueness for lattice spin systems
    Specification.lean          -- Gibbs specifications, conditional distributions
    Uniqueness.lean             -- Uniqueness + exponential correlation decay
    StrongCoupling.lean         -- Strong-coupling verification of Dobrushin condition
    CovarianceBound.lean        -- Single-site covariance bounds
    CondTVBridge.lean           -- Conditional TV bridge, single-site disintegration
    CovarianceBoundMultisite.lean -- Multi-site covariance bounds via condKernel
    CondKernelDLR.lean          -- condKernel inherits DLR, ae bound
    NeumannSeries.lean          -- Neumann series for influence matrix
    FiniteLattice.lean          -- Finite lattice distance structure
  Matrix/                       -- Finite matrix semigroup theory
    HeatKernel.lean             -- exp(-tM) >= 0 for Z-matrices (proved)
    LaplaceTransform.lean       -- M^{-1} = integral exp(-tM) dt
    Trotter.lean                -- Lie-Trotter product formula
    Diamagnetic.lean            -- |(M+iV)^{-1}| <= M^{-1} entrywise
```

## Formalization status

**Zero sorry's in core theory** (Abstract/ + Diffusion/ + Convergence/ +
Coupling/ + Instances/BrascampLieb + Dobrushin covariance bounds).
Sorry's exist only in concrete instances (TwoPoint, Euclidean),
one unused theorem in NeumannSeries, and Matrix/.

### Fully proved (zero sorry's)

- **Bakry-Émery Poincaré** — Var(f) ≤ (1/ρ) E(f,f) from
  semigroup L² decay bound + ergodicity
- **Bakry-Émery variance decay** — Var(P_t f) ≤ e^{-2ρt} Var(f)
  from Poincaré + Grönwall's inequality
- **Bakry-Émery log-Sobolev** — Ent(f²) ≤ (2/ρ) E(f,f) from
  entropy decay bound + entropy ergodicity
- **Brascamp-Lieb inequality** and Poincaré corollary
- **Doeblin's condition** — one-step contraction, TV contraction,
  n-step mixing (by induction), correlation decay
- **TV-integral bound** via layer cake formula
- **TV coupling characterization** — maximal coupling construction
- **Heat kernel positivity** for Z-matrices (Metzler shift)
- **Hessian invertibility** — injectivity, surjectivity, continuity
- **Weighted Young's inequality** from Hessian symmetry
- **Variance nonnegativity** via Mathlib's `ProbabilityTheory.variance_nonneg`

### Postulated as textbook axioms (2 core + 2 matrix = 4 total)

| Axiom | Reference |
|-------|-----------|
| `gross_lsi_implies_hypercontractive` | Gross (1975), Theorem 1 |
| `gross_hypercontractive_implies_lsi` | Gross (1975), Theorem 2 |
| `m_matrix_inverse_nonneg` | M-matrix theory (Berman-Plemmons Ch. 6) |
| `diamagnetic_resolvent` | Diamagnetic inequality (assembles 5 steps) |

(`exp_entryNonneg_of_entryNonneg` and `trotter_product_formula` were
previously axiomatized but are now proved as theorems in
`Matrix/HeatKernel.lean` and `Matrix/Trotter.lean`.)

### Concrete instances

- **TwoPoint** ({0,1}, uniform measure): 19/21 BakryEmerySpace fields
  proved. 2 sorry's are mathematically false (Γ_leibniz fails for jump
  processes — validates that the diffusion axiom is a real constraint).
- **Gaussian1D** (ℝ, N(0,1), OU semigroup): 9/23 fields proved.
  All fields mathematically true; sorry's are Lean infrastructure gaps
  (Fubini, differentiation under integral).

### TV coupling (Coupling/)

- `tvDist_le_coupling`: TV ≤ P(σ ≠ τ) for any coupling — **proved**
- `maximal_coupling`: optimal coupling construction — **proved**
- `tvDist_eq_inf_coupling`: coupling characterization — **proved**
- `canonicalMaximalCoupling`: constructive pointwise-min coupling — **proved**
- Giry measurability of canonical coupling — **proved** (for countable S)
- `dobrushin_iterated_coupling_fintype`: min-disagreement coupling (finite S) — **proved**
- `prokhorov_coupling_theorem`: min-disagreement coupling (compact S) — **proved**
  via Prokhorov compactness + Portmanteau lsc + kernel Radon-Nikodym

### Dobrushin uniqueness (Dobrushin/)

- `GibbsSpec`, `IsGibbsMeasure`: Gibbs specifications — **defined**
- `DobrushinCondition`: influence matrix condition — **defined**
- `dobrushin_uniqueness`: Dobrushin uniqueness theorem — **proved**
- `influenceCoeff`, `influenceCoeff_le_of_cylinder_ratio_bound` — **proved**
- Single-site disintegration (`condSingleSiteMeasure`) — **proved**
- Multi-site covariance bounds via `condKernel` — **proved**
- `condKernel_ae_bound`: condKernel fiber inherits DLR — **proved**
- Neumann series exponential decay — **proved** (modulo one unused sorry)

### Matrix semigroup theory (Matrix/)

- **Heat kernel positivity** for Z-matrices: exp(-tM) ≥ 0 entrywise —
  proved via Metzler shift decomposition
- **Euler factor nonnegativity**: I - (t/n)M ≥ 0 for large n — proved
- **Entrywise-nonneg matrix algebra**: pow, mul, add, smul — proved

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
- Simon, *Functional Integration and Quantum Physics*, Academic Press,
  1979 (Ch. 22: diamagnetic inequality).
- Dobrushin, "The description of a random field by means of conditional
  probabilities," *Theor. Prob. Appl.* 13 (1968), 197–224.
- Lindvall, *Lectures on the Coupling Method*, Wiley, 1992.
- Chatterjee, *Gauge Theory Lecture Notes*, 2026.

## Author

Michael R. Douglas

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
