# markov-semigroups

Markov semigroups, functional inequalities, and convergence to
equilibrium in Lean 4. Built on the
[hille-yosida](https://github.com/mrdouglasny/hille-yosida) C₀-semigroup
framework. The downstream
[gaussian-hilbert](https://github.com/mrdouglasny/gaussian-hilbert) library
combines this repo with
[gaussian-field](https://github.com/mrdouglasny/gaussian-field) for
finite-dim Wiener chaos / polynomial-chaos concentration work.

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

10. **Dobrushin-Zegarlinski for continuous spins:** uniform local LSI
    + weak gradient coupling (Zegarlinski condition with `J/c ≤ α < 1`)
    implies a global, volume-independent log-Sobolev inequality with
    constant `c·(1-α)`. Plus the entrywise covariance corollary
    (Helffer-Sjöstrand): `|Cov(σ_x, σ_y)| ≤ α^{d(x,y)} / (c·(1-α))` for
    nearest-neighbor finite-range potentials. Built on the proved
    AbstractInfluenceMatrix Neumann theory and proved single-site
    entropy decomposition; only the textbook bridges (Otto-Reznikoff
    LSI, Helffer-Sjöstrand) are axiomatized. For pphi2N's strict
    thermodynamic-limit mass-gap route.

11. **Borell-Herbst concentration from LSI:** for any LSI measure with
    constant `c > 0`, every L-Lipschitz function is sub-Gaussian:
    `μ({F − E_μ F > t}) ≤ exp(−c·t²/(2L²))`. Proven via the Herbst MGF
    bound (textbook axiom) + Mathlib's Chernoff. Composes with the
    Zegarlinski global LSI to give Lipschitz-observable concentration
    on Gibbs measures. One/two-sided variants, `MemLp` moment bounds,
    and a Mathlib `HasSubgaussianMGF` interop are all proven.

12. **LSI ⇒ Poincaré (variance bound):** standard textbook implication
    that LSI(c) implies the Poincaré inequality with the same constant:
    `Var_μ(f) ≤ (1/c) ∫ ‖∇f‖² dμ`. For L-Lipschitz F, gives
    `Var_μ(F) ≤ L²/c`. Specialized to the Zegarlinski global LSI:
    `Var_μ_Gibbs(F) ≤ L²/(c·(1−α))`. Closes the LSI → concentration
    → variance / spectral-gap chain.

**Multivariate Hermite / Wiener chaos / OU eigenfunctions /
polynomial-chaos concentration** (Janson Theorem 5.10) live in
[gaussian-hilbert](https://github.com/mrdouglasny/gaussian-hilbert)
since 2026-05-10. They were originally drafted here in a `Gaussian/`
subdirectory, but the content is "facts about the standard Gaussian
measure" rather than "facts about abstract Markov semigroups", and
gaussian-hilbert (which sits on top of gaussian-field +
markov-semigroups + Mathlib) is the natural home. Removing the cluster
also cleanly eliminated markov-semigroups' cross-repo dependency on
gaussian-field.

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
    Hypercontractivity.lean     -- DirichletMarkovSemigroup; LSI <-> hypercontractivity (Gross + Stroock-Varopoulos axioms + the 3 hypothesis predicates)
    GrossODE.lean               -- Gross-ODE proof of LSI=>HC (FULLY PROVED, sorry-free: gross_lsi_implies_hypercontractive_of_hypotheses, via the 4 per-instance predicates incl. CoreLpL2Approx)
    Concentration.lean          -- Borell-Herbst sub-Gaussian concentration from LSI
  Diffusion/                    -- Layer 2: abstract diffusions (Gamma, Gamma_2)
    CarreDuChamp.lean           -- BakryEmerySpace: Gamma, semigroup, curvature
    StroockVaropoulos.lean      -- RpowChainRule + stroockVaropoulos_eq (S-V equality for diffusion forms)
    BakryEmery.lean             -- Bakry-Emery curvature criterion
    L2Semigroup.lean            -- Bridge to hille-yosida semigroup theory
    InvariantMeasure.lean       -- Invariant probability measures
    OrnsteinUhlenbeck.lean      -- Abstract OU semigroup on Hilbert spaces
  -- (Wiener chaos / multivariate Hermite / OU eigenfunctions /
  -- polynomial-chaos concentration moved to gaussian-hilbert as
  -- GaussianHilbert.* on 2026-05-10.)
  Instances/                    -- Layer 3: concrete spaces (sorry-free)
    Torus.lean                  -- T^d: heat semigroup, Fourier modes (header)
    GFFIdentification.lean      -- OU invariant on T^d = GFF (header)
    BrascampLieb.lean           -- Brascamp-Lieb for log-concave measures
    WorkInProgress/             -- Layer 3, in progress (honest sorries)
      Euclidean.lean            --   R: standard Gaussian, OU semigroup (2 sorry = Lean gaps; axiom-free, Mehler-kernel axioms discharged)
      TwoPoint.lean             --   {0,1}: diffusion axiom fails (2 sorry)
      EuclideanHypercontractive.lean -- R^n Gaussian: discharges the 4 Gross hypotheses + assembles stdGaussianFin_isHypercontractive (no gross_lsi_implies_hypercontractive axiom)
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
  DobrushinZegarlinski/         -- Zegarlinski's theorem for continuous spins
    AbstractInfluence.lean      -- Abstract Neumann decay (pure linear algebra, 0 axioms)
    EuclideanTransport.lean     -- GibbsSpec.toEuclideanMeasure adapter (PiLp 2 transport)
    InteractionMatrix.lean      -- Gradient interaction J_{xy} = sup |∂_y ∂_x V|
    LocalLSI.lean               -- Thin SatisfiesLSI predicate, UniformLocalLSI class
    EntropyChainRule.lean       -- Bochner DLR identity (proved), single-site decomposition (proved)
    GlobalLSI.lean              -- ZegarlinskiCondition, global_lsi_of_zegarlinski (1 axiom: zegarlinski_lsi_inequality)
    EntrywiseCovariance.lean    -- Helffer-Sjöstrand entrywise Cov bound (1 axiom: cov_entrywise_bound_of_zegarlinski)
    Concentration.lean          -- Lipschitz concentration corollaries from global LSI (composes Borell-Herbst; 0 new axioms)
  Matrix/                       -- Finite matrix semigroup theory
    HeatKernel.lean             -- exp(-tM) >= 0 for Z-matrices (proved)
    LaplaceTransform.lean       -- M^{-1} = integral exp(-tM) dt
    Trotter.lean                -- Lie-Trotter product formula
    Diamagnetic.lean            -- |(M+iV)^{-1}| <= M^{-1} entrywise
  Tools/                        -- Shared utilities
    SingleSiteDisintegration.lean -- Single-site disintegration of measures on SpinConfig
```

## Formalization status

**Zero sorry's in the main tree** (Abstract/, Diffusion/, Convergence/,
Coupling/, Dobrushin/, DobrushinZegarlinski/, Matrix/, and the three
sorry-free instances in `Instances/`: BrascampLieb, Torus,
GFFIdentification). 2 sorries remain, both in
`Instances/WorkInProgress/TwoPoint.lean` and mathematically false for
jump processes (validates that the diffusion axiom is a real
constraint). The Gaussian1D Bakry-Émery instance
(`Instances/WorkInProgress/Euclidean.lean` and supporting
`EuclideanStein.lean`, `EuclideanHermite.lean`) holds 0 sorries and
**1 remaining BGL Ch. 2 textbook axiom** (`ouSemigroup_entropy_sq_decay_bound`,
the de Bruijn entropy-derivative identity; GR-vetted via Gemini).
Eight of the originally nine were reduced to theorems: the five early
discharges (`ouSemigroup_l2_decay_bound`, `ouSemigroup_ergodic`,
`ouSemigroup_entropy_sq_ergodic`, `ouSemigroup_compose`,
`gaussian2D_orthogonal_invariance`), plus the 2026-05-12 discharges of
`ouSemigroup_gradient_decay`, `ouSemigroup_l2_sq_hasDerivWithinAt`,
`ouSemigroup_preserves_IsCore`, and `ouSemigroup_contDiff` (Path C
Hermite IBP). These WIP instances are imported by the top-level module
so that callers of `#print axioms` on any theorem that transitively
uses them will see the axiom/sorry surface honestly.

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

### Postulated as textbook axioms (2 core + 1 Stroock-Varopoulos + 1 matrix + 2 DZ + 2 concentration/Poincaré + 0 GaussianFin = 8 total)

*See [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) for the per-axiom vetting
verdicts (Standard / Likely correct / Placeholder / etc.), review
provenance (deep-think, Gemini chat, literature page-ref, self-audit),
and links to the discharge plans.*


| Axiom | Reference |
|-------|-----------|
| `gross_lsi_implies_hypercontractive` | Gross (1975), Theorem 1 (bundled `DirichletMarkovSemigroup`). **Bypassed in the concrete Gaussian chain** since 2026-05-22 — see below; retained only for the abstract `hypercontractive_of_logSobolev` / `gross_lsi_iff` wrappers |
| `gross_hypercontractive_implies_lsi` | Gross (1975), Theorem 2 (now on bundled `DirichletMarkovSemigroup`) |
| `stroock_varopoulos` | BGL Prop 1.7.1 (intermediate-step lemma for Gross; **Standard** by gemini-3.1-pro two-pass 2026-05-13). **Bypassed in the concrete Gaussian chain** since 2026-05-22 — discharged there as the *equality* `BakryEmerySpace.stroockVaropoulos_eq` (`Diffusion/StroockVaropoulos.lean`) via the diffusion `rpow` chain rule; retained for non-diffusion / abstract uses |
| `diamagnetic_resolvent` | Diamagnetic inequality (assembles 5 steps) |
| `zegarlinski_lsi_inequality` | Otto-Reznikoff (2007) J. Funct. Anal. 243 Thm 1; Zegarlinski (1996) CMP 175; BGL §5.7.5 |
| `cov_entrywise_bound_of_zegarlinski` | Helffer-Sjöstrand (1994) J. Stat. Phys. 74; Naddaf-Spencer (1997) CMP 183; BGL §4.5 |
| `herbst_mgf_bound` | BGL §5.4.1 (Herbst's lemma); Ledoux (2001) §1; Otto-Villani (2000) JFA 173 §3 |
| `poincare_of_lsi` | BGL Proposition 5.1.3 (LSI ⇒ Poincaré with same constant) |

The Gaussian1D concrete instance and the abstract
`MarkovSemigroups/General/OUEntropyDecomposition.lean` are both now
**axiom-free**: all BGL Ch. 2 and §5.5 facts for the Gaussian OU
semigroup have been discharged. As of **2026-05-19**, all multivariate
Gaussian BE axioms are discharged to axiom-free theorems: the de Bruijn
derivative `ouSemigroupFin_l2_sq_hasDerivWithinAt` (in
`Instances/WorkInProgress/EuclideanFinBE.lean`),
`ouSemigroupFin_preserves_IsCore` (Workstream N1.b, Cameron–Martin
kernel route), and `ouSemigroupFin_entropy_sq_decay_bound` (Workstream
N1.c, the 1-parameter telescoping route) — leaving **0 GaussianFin
Bakry–Émery *curvature* axioms**. (The OU *generator* subsystem in
`Instances/WorkInProgress/EuclideanGenerator*.lean`, added later for the
`GeneratorCompat` discharge, is now theorem-only: the coordinatewise Gaussian
integration by parts, pointwise endpoint heat equation, and strong-`L²`
difference quotient were all discharged on 2026-05-22. See the W-step note
below.)

**W-step — Gross axiom bypassed (2026-05-22):**
`Instances/WorkInProgress/EuclideanHypercontractive.lean` discharges all four
per-instance hypotheses of the *proved* `gross_lsi_implies_hypercontractive_of_hypotheses`
for the standard Gaussian OU bundle — `CoreSemigroupInvariant`, `GeneratorCompat`,
`StroockVaropoulos`, `CoreLpL2Approx` — and assembles
`stdGaussianFin_isHypercontractive`. Consequently `#print axioms` of that theorem
(and of the downstream gaussian-hilbert `…_isHypercontractive`) lists only
the 3 Lean built-ins `[propext, Classical.choice, Quot.sound]` — **not**
`gaussianFin_diffQuot_tendsto_Lp`, not `gaussianFin_integrationByParts`, not
`gross_lsi_implies_hypercontractive`, and (since 2026-05-22) **not**
`stroock_varopoulos`. The latter is discharged in the concrete chain as the
diffusion *equality* `BakryEmerySpace.stroockVaropoulos_eq`
(`Diffusion/StroockVaropoulos.lean`) via the `rpow` chain rule; the `StroockVaropoulos`
predicate carries `∃ε>0, ε≤u` a.e. (the chain rule needs strict positivity), supplied
at the unique abstract call site from the positive orbit. No new axioms introduced.

**Discharged 2026-05-12:**
* `ouSemigroup_fisher_info_decay` (A1, BGL Proposition 5.5.2) — the
  Fisher info gradient decay `I(P_t g) ≤ e^{-2t} I(g)`. Proved via
  Cauchy-Schwarz on the Mehler probability kernel + the Mehler
  derivative formula + γ-invariance. ~400 lines including a
  polynomial-discriminant Cauchy-Schwarz helper for γ.
* `hasDerivWithinAt_entropy_ouSemigroup_zero` (A2 at `t = 0+`) —
  derived from A2 (`t > 0` interior version) + DCT-based continuity
  of entropy and Fisher info at `s = 0+` + Mathlib's
  `hasDerivWithinAt_Ici_of_tendsto_deriv`. ~330 lines.
* `hasDerivAt_entropy_ouSemigroup` (A2 interior, BGL §5.5
  de Bruijn identity for `t > 0`) — proved via a Stein-IBP-based
  formula for `(P_t g)''` (avoiding the need for `g''`), parametric
  DCT for the entropy integral, and the bilinear Dirichlet form
  identity (`gaussian_dirichlet_form_bilinear` in
  `EuclideanStein.lean`). ~740 lines.
The previously-axiomatized `ouSemigroup_gradient_decay` (BGL Theorem
5.5.2) is now **PROVED** via the new theorem `hasDerivAt_ouSemigroup`
(Mehler derivative formula via Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) + Jensen +
γ-invariance. Additionally, **Stein's identity** for the
standard Gaussian (BGL §1.15: `∫ y · g(y) dγ = ∫ g'(y) dγ` for
bounded C¹ g) is now **PROVED** as `stein_identity_standard` via the
Gaussian-PDF ODE `pdf'(y) = -y · pdf(y)` + FTC on infinite intervals
(`integral_of_hasDerivAt_of_tendsto`) + `withDensity` bridge. The
**Gaussian Dirichlet form identity** `∫ g · L g dγ = -∫ (g')² dγ`
(`gaussian_dirichlet_form_identity`, BGL §1.6) follows from Stein
applied to `h := g · g'`. `ouSemigroup_preserves_IsCore` was
**DECOMPOSED** (2026-05-12) — the bounded parts `|P_t f|, |(P_t f)'|,
|(P_t f)''| ≤ M` are now proved (`ouSemigroup_preserves_bounds`) via a
generalized Mehler-derivative `hasDerivAt_ouSemigroup_C1` + iterated
formula `hasDerivAt_deriv_ouSemigroup` (giving `(P_t f)'' = e^{-2t}
P_t(f'')`); the `C^∞` smoothing residue (`ouSemigroup_contDiff`) was
then **FULLY DISCHARGED** via the **Hermite IBP path** (Path C):
the closed-form iterated-derivative identity
`(P_t f)^{(n)}(x) = (a/b)^n · ∫ y, H_n(y) · f(a·x + b·y) ∂γ` is proved
by induction on `n`, combining parametric integral differentiation
with the n-th-order Stein identity `∫ H_n · F' dγ = ∫ H_{n+1} · F dγ`
(`hermite_ibp_gaussian`). C^∞ conclusion via
`contDiff_of_differentiable_iteratedDeriv`. See
`Instances/WorkInProgress/EuclideanHermite.lean`. As part of this
discharge, `IsCore` was refactored from `ContDiff ℝ ⊤` (analyticity in
current Mathlib) to `ContDiff ℝ ∞` (C^∞), matching the project's
long-standing C^∞ intent. All originally-introduced
axioms were vetted in one pass via Gemini chat
(gemini-3-pro-preview), which flagged a missing `IsCore` hypothesis
on the Mehler-composition axiom — patched in both the axiom and the
upstream `BakryEmerySpace.semigroup_add` field. Five of the original
nine were **reduced to theorems** proved from the remaining four
atomic axioms plus Mathlib's Gaussian infrastructure:
`ouSemigroup_l2_decay_bound` (FTC + gradient decay),
`ouSemigroup_ergodic` (double DCT on Mehler integrand),
`ouSemigroup_entropy_sq_ergodic` (DCT for `s log s` + compactness),
`ouSemigroup_compose` (Gaussian convolution via
`gaussianReal_add_gaussianReal_of_indepFun`), and
`gaussian2D_orthogonal_invariance` (proved by Codex via
`stdGaussian_map` + `map_pi_eq_stdGaussian` through the
`EuclideanSpace ℝ (Fin 2) ≃ₗᵢ WithLp 2 (ℝ × ℝ)` isometry).

(`exp_entryNonneg_of_entryNonneg`, `trotter_product_formula`, and
`m_matrix_inverse_nonneg` were previously axiomatized but are now
proved as theorems in `Matrix/HeatKernel.lean`, `Matrix/Trotter.lean`,
and `Matrix/LaplaceTransform.lean` respectively. `hermiteMulti_dense`
was previously a free-standing axiom in `Gaussian/HermitePolynomials.lean`
but is now a theorem proved from the `polynomial_dense_L2_of_subGaussian`
axiom in gaussian-field's `GeneralResults/PolynomialDensityGaussian.lean`
(decomposed via a `Submodule.span`-based change-of-basis between
multivariate monomials and multivariate Hermite polynomials, fully
proved). An earlier free-standing `entropy_chain_rule_local` axiom was
REMOVED after external review (Gemini, gemini-3-pro-preview): the
statement was mathematically false for general Gibbs measures because
Dirac single-site conditionals at low temperature produce a vanishing
RHS while the LHS remains positive. The DZ proof does not factor
through such a separate chain rule; the iteration is interleaved
inside `zegarlinski_lsi_inequality`.)

### Which theorems actually depend on these axioms?

Verified by `#print axioms` on a fresh build. The axiom footprint
is narrow: everything outside the rows below is axiom-free (depends
only on Lean's three standard axioms `propext`, `Classical.choice`,
`Quot.sound`).

| Axiom | Transitive consumers inside this repo |
|---|---|
| `gross_lsi_implies_hypercontractive` | `DirichletMarkovSemigroup.hypercontractive_of_logSobolev`, `DirichletMarkovSemigroup.gross_equivalence` (`Abstract/Hypercontractivity.lean`); not consumed by any other module or downstream project |
| `gross_hypercontractive_implies_lsi` | `DirichletMarkovSemigroup.logSobolev_of_hypercontractive`, `DirichletMarkovSemigroup.gross_equivalence` (`Abstract/Hypercontractivity.lean`); not consumed by any other module or downstream project |
| `diamagnetic_resolvent` | None — declared for external callers; no theorem in this repo uses it |
| `zegarlinski_lsi_inequality` | `global_lsi_of_zegarlinski` (`DobrushinZegarlinski/GlobalLSI.lean`); declared for downstream consumers (pphi2N strict thermodynamic-limit route) |
| `cov_entrywise_bound_of_zegarlinski` | `cov_entrywise_decay_nn` (`DobrushinZegarlinski/EntrywiseCovariance.lean`, the proven exponential-decay corollary `\|Cov(σ_x, σ_y)\| ≤ α^{d(x,y)} / (c·(1-α))` for nearest-neighbor finite-range V); declared for pphi2N's `HSData.AdmitsThimbleLocal` |
| `herbst_mgf_bound` | `lipschitz_concentration_of_lsi` (proven theorem, `Abstract/Concentration.lean`, derived from this axiom + Mathlib's Chernoff `measure_ge_le_exp_mul_mgf`); `lipschitz_concentration_left_of_lsi` and `lipschitz_concentration_two_sided_of_lsi` (proven, by reflection / union bound); `hasSubgaussianMGF_of_lsi` (proven Mathlib `HasSubgaussianMGF` bridge); `memLp_of_lsi` (proven `L^p` moment bounds); `lipschitz_concentration_of_zegarlinski` + left-tail + two-sided + Mathlib bridge + `MemLp` (`DobrushinZegarlinski/Concentration.lean`, all composing with the global LSI from the Zegarlinski hypothesis) |
| `poincare_of_lsi` | `variance_lipschitz_le_of_lsi` (proven `Var(F) ≤ L²/c` via Mathlib's `norm_fderiv_le_of_lipschitz`); `variance_lipschitz_le_of_zegarlinski` (proven Zegarlinski composition `Var ≤ L²/(c·(1-α))`). Declared for spectral-gap-style fluctuation bounds |
| `Gaussian1D.bakryEmerySpace` consumes no atomic OU axioms | The Gaussian1D `BakryEmerySpace ℝ` instance (in `Instances/WorkInProgress/EuclideanEntropyDecay.lean`) is **axiom-free**. All originally-axiomatized BGL Ch. 2 / §5.5 Mehler-kernel-level facts have been discharged as theorems. |

**DZ-layer axiom audit (verified `#print axioms` 2026-05-01):** the
proven content of `DobrushinZegarlinski/` — `AbstractInfluenceMatrix`
theory, single-site decomposition `entropy_decomposition_single_site`,
DLR-at-Bochner-integral identity `integral_siteSmoothing`, distance-
aware Neumann bounds `iterate_dist_zero` /
`neumann_series_nn_dist_bound`, and the exponential-decay corollary
`cov_entrywise_decay_nn` — is **axiom-free** (depends only on the
three Lean built-ins). Only the two textbook axioms above are pulled
in when the LSI / Cov bridge theorems themselves are invoked.

The rest of the library is axiom-free. Specifically, the
Bakry-Émery Poincaré / LSI / variance decay / entropy decay
(`Diffusion/CarreDuChamp.lean`), Brascamp-Lieb
(`Instances/BrascampLieb.lean`), Doeblin mixing
(`Convergence/Doeblin.lean`), Dobrushin uniqueness
(`Dobrushin/Uniqueness.lean`), TV coupling
(`Coupling/TVCoupling.lean`), Neumann-series correlation decay
(`Dobrushin/NeumannSeries.lean`), the multisite covariance bound
(`Dobrushin/CovarianceBoundMultisite.lean`), and heat-kernel
positivity for Z-matrices (`Matrix/HeatKernel.lean`) all have
`#print axioms` showing only the three Lean built-ins.

One caveat to "the rest is axiom-free": `General/SchwartzConvolution.lean`
declares `contDiff_top_convolution_schwartzKernel` (Gemini-vetted
2026-05-12, **Likely correct**; registered in `AXIOM_AUDIT.md` on
2026-05-16 after the repo-wide sweep found it undocumented there). It
has **no consumers** — staged infrastructure; the OU smoothing fact
was discharged by a different route — so no theorem's `#print axioms`
is affected.

**For downstream consumers:** [lgt](https://github.com/mrdouglasny/lgt)'s
Yang-Mills mass-gap proof uses only the Dobrushin + Coupling +
Matrix/HeatKernel paths, none of which touch the eight textbook
axioms. `#print axioms ym_mass_gap_UN` on the lgt side shows only
`propext`, `Classical.choice`, `Quot.sound`. The DZ + concentration +
Poincaré axioms (added 2026-04 to 2026-05) are reserved for pphi2N's
strict thermodynamic-limit route.

### Concrete instances

- **TwoPoint** ({0,1}, uniform measure): 19/21 BakryEmerySpace fields
  proved. 2 sorry's are mathematically false (Γ_leibniz fails for jump
  processes — validates that the diffusion axiom is a real constraint).
- **Gaussian1D** (ℝ, N(0,1), OU semigroup): 0 sorries / 5 BGL Ch. 2
  textbook axioms. All structure fields filled; the five remaining
  axioms package Mehler-kernel-level facts (parametric Fubini against
  the Gaussian density, differentiation under the integral, 2D
  Gaussian rotation invariance, entropy derivative bridge) as named
  axioms with proof-strategy docstrings, all Gemini-vetted
  (gemini-3-pro-preview). Four of the originally nine were reduced
  to theorems proved from the remaining five:
  `ouSemigroup_l2_decay_bound` (FTC + gradient decay),
  `ouSemigroup_ergodic` (double DCT), `ouSemigroup_entropy_sq_ergodic`
  (DCT for `s log s` + compactness), and `ouSemigroup_compose`
  (Gaussian convolution arithmetic).

### Verification / validation tests (Instances/WorkInProgress/EuclideanTests.lean)

Test theorems exercising the `Gaussian1D` `BakryEmerySpace ℝ` instance
on concrete inputs. Zero sorries.

| Set | Theorem | Axioms |
|---|---|---|
| **A. Mehler eigenfunctions** | `ouSemigroup_const`, `ouSemigroup_id`, `ouSemigroup_hermite_two`, `ouSemigroup_hermite_three` (eigenvalues `1, e^{-t}, e^{-2t}, e^{-3t}` on `H₀, H₁, H₂, H₃`) | none (Mathlib only) |
| **A. Helpers** | `integral_sq_γ` (= 1), `integral_cube_γ` (= 0), `integrable_cube_γ` | none |
| **B. Bakry-Émery on `cos`** | `cos_isCore`, `cos_poincare` (`Var_γ(cos) ≤ ∫sin² dγ`), `cos_variance_decay` (`Var_γ(P_t cos) ≤ e^{-2t} Var_γ(cos)`) | the 3 atomic Bakry-Émery building-block axioms in `General/OUEntropyDecomposition.lean` (Fisher info decay + de Bruijn identity); the previous broad `ouSemigroup_entropy_sq_decay_bound` was discharged from these via FTC + ε-regularization. The full BGL Proposition 4.7.1 chain is now proved end-to-end (`ouSemigroup_contDiff` via Hermite IBP in `EuclideanHermite.lean`, the entropy decay via the decomposition above in `EuclideanEntropyDecay.lean`). |
| **C. Conditional BL → Gaussian Poincaré** | `brascampLieb_recovers_gaussian_poincare` (conditional on a `LogConcaveMeasure ℝ` with `μ = γ`) | none |
| **C. Gaussian `LogConcaveMeasure` — structural** | `V_gauss = x²/2`, `contDiff_V_gauss`, `hessianBilin_V_gauss` (= `v · w`), `hV_gauss_convex`, `hV_gauss_curvature` (`‖v‖² ≤ Hess V(v,v)`) | none |
| **C. Gaussian `LogConcaveMeasure` — resolvent fields** | `gaussianLogConcaveMeasure : LogConcaveMeasure ℝ` (built directly, no `Classical.choose`) | four named axioms: `gaussianResolvent`, `gaussianResolvent_ibp`, `gaussianResolvent_ibp_integrable`, `gaussianBochner_identity` (BGL §1.15-1.16: OU resolvent via Lax-Milgram + Stein IBP + Bochner-Weitzenböck) |
| **C. Unconditional BL → Gaussian Poincaré** | `gaussian_brascampLieb_poincare` (`Var_γ(f) ≤ ∫‖f'‖² dγ` for `C¹` `f`) | the four resolvent axioms above |

**Verification summary.** Set A confirms that the Mehler integral
`ouSemigroup` evaluates to the textbook eigenvalues on the first four
Hermite polynomials — operationally verifying it really is the Mehler
kernel, without invoking the remaining atomic OU axiom. Set B
confirms the abstract `satisfiesPoincare` / `variance_decay` theorems
plug correctly into the concrete instance with `ρ = 1`. Set C confirms
that the Brascamp-Lieb route to Gaussian Poincaré with `ρ = 1` agrees
with the Bakry-Émery route on the same constant. The Gaussian
`LogConcaveMeasure ℝ` is now built constructively in its structural
fields (`V = x²/2`, computed 1D Hessian, convexity, curvature ρ = 1);
only the OU-resolvent ingredients (Lax-Milgram + Stein IBP +
Bochner-Weitzenböck) remain as four named textbook axioms with
BGL §1.15-1.16 citations.

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
- Neumann series exponential decay — **proved**

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

### Discharging the Gross axiom (Route A)

The Gross LSI ⇒ hypercontractivity axiom
(`gross_lsi_implies_hypercontractive`) is being discharged as a
multi-stage program. Workstream-level roadmaps and design decisions:

- [`plans/gross-discharge.md`](plans/gross-discharge.md) — overall
  Route A roadmap (H0/G1/G2/P2/P3/W workstreams). H0, G1, G2 ✅;
  P2 Leibniz kernel ✅ (2026-05-20).
- [`plans/archive/p2-strongL2-leibniz-discharge.md`](plans/archive/p2-strongL2-leibniz-discharge.md)
  — discharge plan for the P2 Bochner-Leibniz kernel.
- [`plans/archive/grosspow-hasderivwithinAt-structural-blockers.md`](plans/archive/grosspow-hasderivwithinAt-structural-blockers.md)
  — analysis of the 4 structural blockers encountered while
  composing `grossPow_hasDerivWithinAt`; 3 of 4 discharged from
  existing structure fields (2026-05-20).
- [`plans/archive/gross-design-strictly-positive-escape.md`](plans/archive/gross-design-strictly-positive-escape.md)
  — design decision (Path A vs Path B) for the remaining Blocker 3.
  Gemini-vetted; Path A (strictly-positive escape, matching Gross
  1975's original proof structure) chosen.

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
