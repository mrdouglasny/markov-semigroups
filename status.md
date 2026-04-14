# markov-semigroups — Status

**0 sorry's in core theory. 4 axioms. 20 sorry's in instances/new modules.**

## Project structure

| Module | Files | Sorry's | Axioms | Description |
|---|---|---|---|---|
| Abstract/ | 5 | 0 | 2 | Dirichlet forms, Poincaré, LSI, Holley-Stroock, Gross |
| Diffusion/ | 5 | 0 | 0 | BakryEmerySpace, carré du champ, L² bridge |
| Convergence/ | 5 | 0 | 0 | Doeblin, spectral gap, entropy decay, ergodicity |
| Instances/BrascampLieb | 1 | 0 | 0 | Brascamp-Lieb inequality (fully proved) |
| Instances/TwoPoint | 1 | 2 | 0 | Two-point space (2 sorry's = math false) |
| Instances/Euclidean | 1 | 13 | 0 | Standard Gaussian (sorry's = Lean infra gaps) |
| Matrix/ | 4 | 2 | 2 | Heat kernel, Trotter, diamagnetic inequality |
| Coupling/ | 1 | 0 | 0 | TV coupling characterization |
| Dobrushin/ | 3 | 3 | 0 | Gibbs specifications, Dobrushin uniqueness |

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

### Instances/Euclidean.lean (13 sorry's — mathematically true)
- `energy_add_left` — `deriv(f+g) ≠ deriv f + deriv g` for non-differentiable f
- `Γ_leibniz` — needs `DifferentiableAt` for `deriv_mul`
- `semigroup_mean` (2 edge cases) — non-integrable/non-measurable f
- `gradient_decay` — differentiation under integral + Jensen
- `semigroup_add` — Gaussian convolution (Fubini)
- `semigroup_contraction` — Jensen for convex x²
- `semigroup_selfAdjoint` — Fubini + Mehler kernel symmetry
- `semigroup_l2_decay_bound`, `semigroup_l2_sq_hasDerivWithinAt` — FTC + differentiation under integral
- `semigroup_ergodic` — L² convergence of OU semigroup
- `semigroup_entropy_sq_decay_bound`, `semigroup_entropy_sq_ergodic` — entropy analysis

### Matrix/Trotter.lean (2 sorry's)
- BCH remainder estimates for Lie-Trotter convergence

### Dobrushin/ (3 sorry's — work in progress)
- `StrongCoupling.lean` — measurability of influence coefficients
- `Uniqueness.lean` — contraction mapping + exponential decay

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

### Gaussian instance (Instances/Euclidean.lean)
- `ouSemigroup` (Mehler formula), `ouGamma`, `ouEnergy` — defined
- `energy_smul_left`, `energy_symm`, `energy_nonneg`, `energy_const` — **proved**
- `Γ_symm`, `Γ_nonneg`, `Γ_const`, `energy_eq_integral_Γ` — **proved**
- `semigroup_zero` — **proved**
- `ou_kernel_map`: (γ×γ).map φ = γ — **proved** (Gaussian convolution)
