# markov-semigroups Development Plan

## Overview

Build the Holley-Stroock path from Gaussian log-Sobolev to interacting
spectral gap in three phases, plus a fourth connecting back to pphi2.

## Phase 1: Ornstein-Uhlenbeck on T^d (3-4 weeks)

### 1a. Heat semigroup as C₀-semigroup instance

Instantiate hille-yosida's `StronglyContinuousSemigroup` for the heat
semigroup $e^{t\Delta}$ on T^d_L.

**File:** `OrnsteinUhlenbeck/Torus.lean`

**Definitions:**
- `torusEigenvalue (k : Z^d) : R` — $\lambda_k = 4\pi^2|k|^2/L^2 + m^2$
- `torusHeatSemigroup (t : R) : L^2(T^d) ->L[R] L^2(T^d)` — Fourier
  multiplier $\hat{f}_k \mapsto e^{-\lambda_k t} \hat{f}_k$
- Instance: `StronglyContinuousSemigroup torusHeatSemigroup`
- Instance: `ContractingSemigroup torusHeatSemigroup`

**Theorems:**
- `torusHeatSemigroup_generator` — generator is $\Delta - m^2$
- `torusHeatSemigroup_contraction` — $\|e^{t(\Delta-m^2)}\| \leq e^{-m^2 t}$

**Infrastructure from pphi2:** The Fourier eigenvalues on T^2 are
already defined in `TorusPropagatorConvergence.lean`. Either import
these or redefine for general T^d.

**Infrastructure from hille-yosida:** `StronglyContinuousSemigroup`,
`ContractingSemigroup`, growth bounds, resolvent.

### 1b. OU process via Fourier modes

Define the stationary OU process on T^d as the product of independent
1D OU processes on Fourier modes.

**File:** `OrnsteinUhlenbeck/Torus.lean` (continued)

**Definitions:**
- `fourierModeOU (k : Z^d) : R -> Omega -> R` — 1D OU process
  $z_k(t)$ with drift $-\lambda_k z_k$ and stationary variance $1/(2\lambda_k)$
- `torusOUProcess : R -> Omega -> Configuration(T^d)` — the full
  process $\phi(t) = \sum_k z_k(t) e_k$

**Theorems:**
- `fourierModeOU_stationary` — each mode is stationary Gaussian
- `fourierModeOU_variance` — $E[|z_k|^2] = 1/(2\lambda_k)$
- `torusOU_spectralGap` — gap = $\lambda_1 = m^2 + 4\pi^2/L^2$

**Decision:** Whether to construct the 1D OU process from the
brownian-motion library or directly (the stationary distribution is
just $N(0, 1/(2\lambda_k))$, which can be defined without stochastic
calculus). For Phase 1, the direct approach is simpler.

### 1c. Invariant measure = GFF

**File:** `OrnsteinUhlenbeck/InvariantMeasure.lean`,
`OrnsteinUhlenbeck/GFFIdentification.lean`

**Theorems:**
- `torusOU_invariantMeasure_isGaussian` — invariant measure is Gaussian
- `torusOU_invariantMeasure_covariance` — covariance is
  $\frac{1}{2}(-\Delta + m^2)^{-1}$
- `torusOU_invariantMeasure_eq_gff` — equals the GFF measure from
  gaussian-field (by `gaussian_measure_unique_of_covariance`)

**This is the first real theorem:** free-field stochastic quantization.

### 1d. Finite-dimensional warmup (optional)

**File:** `OrnsteinUhlenbeck/FiniteDimensional.lean`

OU on R^n with Mehler's formula. This is simpler and provides intuition,
but is not strictly needed for the main results. Can be done in parallel
or deferred.

## Phase 2: Functional Inequalities (4-6 weeks)

### 2a. Poincaré inequality

**File:** `FunctionalInequalities/Poincare.lean`

**Definitions:**
- `SatisfiesPoincare (mu : Measure X) (rho : R) : Prop` —
  $\mathrm{Var}_\mu(f) \leq (1/\rho) \mathcal{E}(f,f)$ where
  $\mathcal{E}$ is the Dirichlet form

**Theorems:**
- `poincare_variance_decay` — Poincaré with constant $\rho$ implies
  $\mathrm{Var}_\mu(P_t f) \leq e^{-2\rho t} \mathrm{Var}_\mu(f)$
- `poincare_spectralGap` — Poincaré constant = spectral gap of generator

### 2b. Log-Sobolev inequality

**File:** `FunctionalInequalities/LogSobolev.lean`

**Definitions:**
- `Entropy (mu : Measure X) (f : X -> R) : R` —
  $\mathrm{Ent}_\mu(f) = \int f \log f\, d\mu - (\int f\, d\mu)\log(\int f\, d\mu)$
- `SatisfiesLogSobolev (mu : Measure X) (rho : R) : Prop` —
  $\mathrm{Ent}_\mu(f^2) \leq (2/\rho) \mathcal{E}(f,f)$

**Theorems:**
- `logSobolev_implies_poincare` — LSI($\rho$) implies Poincaré($\rho$)
  (by linearization: $\mathrm{Ent}(1 + \varepsilon g) \approx \varepsilon^2 \mathrm{Var}(g)$)
- `logSobolev_entropy_decay` — LSI implies
  $\mathrm{Ent}_\mu(P_t f) \leq e^{-2\rho t} \mathrm{Ent}_\mu(f)$

### 2c. Bakry-Émery criterion

**File:** `FunctionalInequalities/BakryEmery.lean`

**Definitions:**
- `carreDuChamp (L : Generator) (f : X -> R) : X -> R` — $\Gamma(f) = \frac{1}{2}(L(f^2) - 2f Lf)$
- `iteratedCarreDuChamp (L : Generator) (f : X -> R) : X -> R` — $\Gamma_2(f) = \frac{1}{2}(L\Gamma(f) - 2\Gamma(f, Lf))$
- `BakryEmeryCurvature (L : Generator) (rho : R) : Prop` — $\Gamma_2(f) \geq \rho \cdot \Gamma(f)$

**Theorems:**
- `bakryEmery_logSobolev` — curvature $\rho$ implies LSI($\rho$)
- `ou_curvature` — OU generator on R^n has curvature 1
- `torus_ou_curvature` — OU generator $\Delta - m^2$ on T^d has curvature $m^2$
- `gaussian_logSobolev` — Gaussian measure on T^d satisfies LSI($m^2$)

**This is the hard proof in Phase 2.** The Bakry-Émery argument uses the
semigroup interpolation method: differentiate $\Phi(t) = P_t(\Gamma(P_{T-t} f))$
and show $\Phi'(t) \geq 0$ from the curvature condition. This requires
commutation relations between the semigroup and the carré du champ.

### 2d. Holley-Stroock perturbation

**File:** `FunctionalInequalities/HolleyStroock.lean`

**Theorems:**
- `holleyStroock_logSobolev` — if $\mu_0$ satisfies LSI($\rho_0$) and
  $d\mu_1 = (1/Z) e^{-V} d\mu_0$ with $\mathrm{osc}(V) < \infty$,
  then $\mu_1$ satisfies LSI($\rho_0 \cdot e^{-\mathrm{osc}(V)}$)

**Proof:** Short. The key identity:
$\mathrm{Ent}_{\mu_1}(f^2) = \mathrm{Ent}_{\mu_0}(f^2 \cdot e^{-V}/Z_1)
\leq e^{\mathrm{osc}(V)} \mathrm{Ent}_{\mu_0}(f^2)$
plus $\mathcal{E}_{\mu_1}(f,f) = \mathcal{E}_{\mu_0}(f,f)$ (the
Dirichlet form doesn't change under density perturbation, only the
reference measure changes). Actually the proof is slightly more
involved — one uses the variational formula for entropy:
$\mathrm{Ent}_\mu(g) = \sup_h \{\int gh\, d\mu : \int e^h\, d\mu \leq 1\}$
and the density ratio bound $e^{-\mathrm{osc}(V)} \leq d\mu_1/d\mu_0 \leq e^{\mathrm{osc}(V)}$.

### 2e. Gross equivalence (optional)

**File:** `FunctionalInequalities/Hypercontractivity.lean`

LSI ↔ hypercontractivity. Nice to have for connecting to gaussian-field's
existing hypercontractivity, but not on the critical path.

## Phase 3: Convergence to Equilibrium (2-3 weeks)

### 3a. Spectral gap and mixing

**File:** `Convergence/SpectralGap.lean`

**Theorems:**
- `spectralGap_mixing` — $|\mathrm{Cov}_\mu(f, P_t g)| \leq e^{-\rho t} \|f\|_2 \|g\|_2$
- `spectralGap_of_poincare` — Poincaré constant = spectral gap

### 3b. Entropy decay and ergodicity

**Files:** `Convergence/RelativeEntropy.lean`, `Convergence/Ergodicity.lean`

**Theorems:**
- `entropy_decay_of_logSobolev` — $H(P_t^* \nu | \mu) \leq e^{-2\rho t} H(\nu | \mu)$
- `ergodic_of_spectralGap` — unique invariant measure + time averages converge
- `invariantMeasure_unique_of_spectralGap` — spectral gap implies unique invariant measure

## Phase 4: Application to pphi2 (2-3 weeks)

### 4a. Interacting spectral gap on the torus

**Where:** either in this repo (with pphi2 as dependency) or in pphi2
(with markov-semigroups as dependency). The latter is cleaner.

**Theorem (in pphi2):**
```
theorem torus_interacting_spectralGap
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (L : ℝ) (hL : 0 < L) :
    ∃ ρ : ℝ, 0 < ρ ∧
    ∀ (N : ℕ) [NeZero N],
      ρ ≤ spectralGap (torusInteractingMeasure L N P mass hmass)
```

**Proof sketch:**
1. GFF satisfies LSI with $\rho_0 = m^2$ (from `gaussian_logSobolev`)
2. Interacting measure $d\mu = (1/Z) e^{-V} d\mu_{\mathrm{GFF}}$
3. $\mathrm{osc}(V) \leq 2L^2 A$ uniformly in N
   (from `wickPolynomial_uniform_bounded_below` + physical volume identity)
4. By Holley-Stroock: LSI($m^2 e^{-2L^2 A}$)
5. LSI implies Poincaré implies spectral gap $\geq m^2 e^{-2L^2 A}$

This eliminates `spectral_gap_uniform` for Route B.

### 4b. Clustering (OS4) from spectral gap

**Where:** pphi2

The spectral gap gives exponential decay of correlations, which is OS4
(clustering). Combined with the existing torus OS0-OS3 proofs, this
completes the OS axioms for the torus.

## Dependency Flow

```
Mathlib
  |
  +-- hille-yosida (C₀-semigroups)
  |
  +-- gaussian-field (GFF, hypercontractivity)
  |
  +-- markov-semigroups [this project]
  |     |
  |     +-- Phase 1: OU on T^d, invariant measure = GFF
  |     +-- Phase 2: LSI, Bakry-Émery, Holley-Stroock
  |     +-- Phase 3: Spectral gap, mixing, ergodicity
  |
  +-- pphi2
        |
        +-- Phase 4: torus_interacting_spectralGap
```

## Estimated Timeline

| Phase | Weeks | Key difficulty |
|-------|-------|----------------|
| 1: OU + invariant measure | 3-4 | Semigroup instantiation |
| 2: Functional inequalities | 4-6 | Bakry-Émery semigroup interpolation |
| 3: Convergence | 2-3 | Routine given Phase 2 |
| 4: Application to pphi2 | 2-3 | Connecting the pieces |
| **Total** | **11-16** | |

## Priority Order

If time is limited, the highest-value path is:

1. `Torus.lean` — heat semigroup instance (foundation)
2. `LogSobolev.lean` — Gross LSI for Gaussian (the key inequality)
3. `HolleyStroock.lean` — perturbation lemma (short proof, huge payoff)
4. `SpectralGap.lean` — spectral gap from Poincaré (routine)
5. Phase 4a in pphi2 — eliminates `spectral_gap_uniform`

Steps 1-5 are the critical path. Everything else (Bakry-Émery,
finite-dimensional OU, entropy decay, Gross equivalence, ergodicity)
is valuable but not blocking.

## Risk Assessment

**Low risk:** Holley-Stroock (short proof), Poincaré (standard),
spectral gap / mixing (standard), Phase 4 connection (combines
existing pieces).

**Medium risk:** OU semigroup instantiation (needs to bridge hille-yosida
abstractions to concrete Fourier multiplier operators on T^d), Gross LSI
(well-understood but the semigroup proof requires careful functional
analysis).

**High risk:** Bakry-Émery (the semigroup interpolation argument needs
commutation of P_t with Γ, which requires regularity of the semigroup
on the domain of the generator). Can be bypassed: Gross LSI for
Gaussians can also be proved directly without Bakry-Émery, using the
tensorization property of LSI + the 1D Gaussian case.

**Fallback for Bakry-Émery:** Prove Gross LSI for the 1D Gaussian
$N(0, \sigma^2)$ directly (the Hermite polynomial proof, which connects
to gaussian-field's existing hypercontractivity), then tensorize to get
LSI for the product Gaussian on T^d (product of Fourier modes). This
avoids the $\Gamma_2$ machinery entirely.

## References

- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014. [The main reference for all of Phase 2]
- Gross, "Logarithmic Sobolev inequalities," *Amer. J. Math.* 97 (1975),
  1061-1083.
- Holley and Stroock, "Logarithmic Sobolev inequalities and stochastic
  Ising models," *J. Stat. Phys.* 46 (1987), 1159-1194.
- Guionnet and Zegarlinski, "Lectures on logarithmic Sobolev
  inequalities," Séminaire de Probabilités XXXVI, Springer LNM 1801
  (2003), 1-134. [Excellent survey with the perturbation argument]
- Ledoux, "The concentration of measure phenomenon," AMS, 2001.
