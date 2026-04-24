# markov-semigroups — Status

**4 axioms. 12 sorry's total**: 1 orphan in Dobrushin (in an unused
single-site B2 theorem, `dobrushin_covariance_iterateInfluence_bound`,
pending M1–M3 infrastructure — see its docstring; nothing downstream
depends on it), 2 in the TwoPoint instance (mathematically false for
jump processes — validates that the diffusion axiom is a real
constraint), and 9 in the Euclidean Gaussian instance (Lean
infrastructure gaps: Fubini, differentiation under the integral).
**Zero sorry's in any theorem actually consumed by downstream
projects (lgt, pphi2, etc.).**

## Project structure

| Module | Files | Sorry's | Axioms | Description |
|---|---|---|---|---|
| Abstract/ | 5 | 0 | 2 | Dirichlet forms, Poincaré, LSI, Holley-Stroock, Gross |
| Diffusion/ | 5 | 0 | 0 | BakryEmerySpace, carré du champ, L² bridge |
| Convergence/ | 5 | 0 | 0 | Doeblin, spectral gap, entropy decay, ergodicity |
| Instances/BrascampLieb | 1 | 0 | 0 | Brascamp-Lieb inequality (fully proved) |
| Instances/TwoPoint | 1 | 2 | 0 | Two-point space (2 sorry's = math false) |
| Instances/Euclidean | 1 | 9 | 0 | Standard Gaussian (sorry's = Lean infra gaps) |
| Matrix/ | 4 | 0 | 2 | Heat kernel, Trotter, diamagnetic inequality |
| Coupling/ | 1 | 0 | 0 | TV coupling characterization |
| Dobrushin/ | 5 | 1 (orphan) | 0 | Gibbs specs, uniqueness, Neumann series, B3 correlation decay |

## Axioms

### Core (Abstract/)

| Axiom | Reference | Obstacle |
|---|---|---|
| `gross_lsi_implies_hypercontractive` | Gross (1975) Thm 1 | L^p norm differentiation |
| `gross_hypercontractive_implies_lsi` | Gross (1975) Thm 2 | Linearization at t=0 |

### Matrix/

| Axiom | Reference | Obstacle |
|---|---|---|
| `m_matrix_inverse_nonneg` | Berman-Plemmons Ch. 6 | Laplace transform integral |
| `diamagnetic_resolvent` | Simon Ch. 22 | Assembles 5-step proof |

### Proved (formerly axioms, reduced 7 → 2 in core)

| Former axiom | How proved |
|---|---|
| `variance_nonneg'` | Mathlib's `ProbabilityTheory.variance_nonneg` |
| `bakryEmery_poincare` | Semigroup L² decay bound + ergodicity |
| `bakryEmery_variance_decay` | Poincaré + Grönwall (Mathlib) |
| `bakryEmery_logSobolev` | Entropy decay bound + entropy ergodicity |
| `resolvent_ibp_axiom` | Promoted to `LogConcaveMeasure` structure fields |
| `integrated_bochner_axiom` | Promoted to `LogConcaveMeasure` structure fields |

## Sorry's by location

### Instances/TwoPoint.lean (2 sorry's — mathematically false)
- `Γ_leibniz` — Leibniz/diffusion property fails for jump processes
- `semigroup_entropy_sq_decay_bound` — consequence of Leibniz failure

### Instances/Euclidean.lean (9 sorry's — hard analytic, IsCore tractable ones filled)
Tractable sorries using the `IsCore` hypothesis (smooth + bounded test
functions) were resolved in 113cb3c. Remaining:
- `IsCore_semigroup` — smoothness of `P_t f` via differentiation under integral
- `semigroup_add` — Mehler composition (Gaussian convolution via Fubini)
- `semigroup_selfAdjoint` — 2D Gaussian rotation-invariance
- `gradient_decay` — differentiation under integral + Jensen
- `semigroup_l2_decay_bound`, `semigroup_l2_sq_hasDerivWithinAt` — FTC + differentiation under integral
- `semigroup_ergodic` — L² convergence of OU semigroup
- `semigroup_entropy_sq_decay_bound`, `semigroup_entropy_sq_ergodic` — entropy analysis

### Dobrushin/ (1 orphan sorry)
Complete: Specification, Uniqueness (with bridge hypothesis for
hMargToFull), StrongCoupling, FiniteLattice, most of NeumannSeries.
One sorry in `dobrushin_covariance_iterateInfluence_bound`
(NeumannSeries.lean:779) — a single-site-local B2 theorem pending
the M1–M3 infrastructure listed in its docstring. This theorem is
not referenced by any downstream consumer; lgt's mass-gap proof
uses the multisite path in `CovarianceBoundMultisite.lean`, which
is independent.

## Proved results (highlights)

### Bakry-Émery theory (Diffusion/CarreDuChamp.lean)
- `satisfiesPoincare`: Var(f) ≤ (1/ρ) E(f,f) — **proved**
- `variance_decay`: Var(P_t f) ≤ e^{-2ρt} Var(f) — **proved** (Grönwall)
- `satisfiesLogSobolev`: Ent(f²) ≤ (2/ρ) E(f,f) — **proved**

### Brascamp-Lieb inequality (Instances/BrascampLieb.lean)
- `brascampLieb`: Var_μ(f) ≤ ∫⟨∇f, g⟩ dμ — **proved**
- `brascampLieb_poincare`: Var ≤ (1/ρ)∫‖∇f‖² — **proved**
- `hessian_injective`, `hessian_surjective`, `continuous_hessianInverse_gradient` — **proved**

### Doeblin's condition (Convergence/Doeblin.lean)
- `doeblin_one_step_contraction`, `doeblin_tv_contraction` — **proved**
- `doeblin_n_step_mixing`: |T^n(δ_x)(A)-π(A)| ≤ (1-ε)^n — **proved**
- `doeblin_correlation_decay`: |cov| ≤ 2B²(1-ε)^d — **proved**

### TV-integral bounds (Convergence/IntegralBounds.lean)
- `tv_integral_bound`: |∫f dμ - ∫f dπ| ≤ Cδ — **proved** (layer cake)

### TV coupling (Coupling/TVCoupling.lean)
- `tvDist_le_coupling` — **proved**
- `maximal_coupling` construction — **proved**

### Heat kernel positivity (Matrix/HeatKernel.lean)
- `heat_kernel_entrywise_nonneg`: exp(-tM) ≥ 0 for Z-matrices — **proved** (Metzler shift)
- `euler_factor_nonneg`, `isEntryNonneg_pow/mul/add` — **proved**

### Dobrushin correlation decay (Dobrushin/NeumannSeries.lean)
Infrastructure for lgt mass-gap proof. 0 axioms. 1 orphan sorry in
`dobrushin_covariance_iterateInfluence_bound` (not consumed
downstream); all results listed below are fully proved.
- `iterateInfluence`: n-step influence matrix `(C^n)_{xy}` — defined
- `iterateInfluence_pointwise_bound`: `(C^n)_{xy} ≤ α^n` — **proved**
- `iterateInfluence_dist_zero`: `(C^n)_{xy} = 0` for `n < d(x,y)/R` under finite-range influence — **proved**
- `iterateInfluence_row_sum_bound`: `Σ_y (C^n)_{xy} ≤ α^n` — **proved**
- `neumannSeriesCoeff γ x y := Σ_n (C^n)_{xy}` — the `(x,y)` entry of `(I-C)⁻¹` — defined
- `neumannSeriesCoeff_le`: `≤ 1/(1-α)` — **proved**
- `neumannSeriesCoeff_nn_dist_bound`: NN refinement `≤ α^{d(x,y)}/(1-α)` — **proved**
- `dobrushin_correlation_decay_nn`: B3 Neumann route, `|Cov| ≤ 2BfBg·α^d/(1-α)` from B2 bridge
- `dobrushin_correlation_decay_direct`: direct route, `|Cov| ≤ C·α^n` from iterated-coupling bridge
- `dobrushin_correlation_decay_nn_direct`: lattice specialization, `|Cov| ≤ C·α^{d(x,y)}` (no `1/(1-α)` factor) — matches the form consumed by lgt's `dobrushin_correlation_bound`

### Gaussian instance (Instances/Euclidean.lean)
- `ouSemigroup` (Mehler formula), `ouGamma`, `ouEnergy` — defined
- `energy_smul_left`, `energy_symm`, `energy_nonneg`, `energy_const` — **proved**
- `Γ_symm`, `Γ_nonneg`, `Γ_const`, `energy_eq_integral_Γ` — **proved**
- `semigroup_zero` — **proved**
- `ou_kernel_map`: (γ×γ).map φ = γ — **proved** (Gaussian convolution)
