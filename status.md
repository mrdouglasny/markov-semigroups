# markov-semigroups — Status

**Zero sorry's in core. 2 axioms (Gross equivalence). 4 matrix axioms. 30+ proved theorems.**

## Core axioms (Abstract/ + Diffusion/ + Instances/BrascampLieb)

Only 2 remain, both requiring L^p norm differentiation not in Mathlib:

### `gross_lsi_implies_hypercontractive` (Hypercontractivity.lean)

LSI(ρ) ⟹ hypercontractivity. Gross (1975), Theorem 1.
Needs: differentiate ‖P_t f‖_{p(t)} along p(t) = 1+(p-1)e^{2ρt}.

### `gross_hypercontractive_implies_lsi` (Hypercontractivity.lean)

Hypercontractivity ⟹ LSI(ρ). Gross (1975), Theorem 2.
Needs: linearize hypercontractive bound at t=0, p=2, q=2+ε.

### Proved (formerly axioms)

| Former axiom | How proved |
|---|---|
| `variance_nonneg'` | Mathlib's `ProbabilityTheory.variance_nonneg` |
| `bakryEmery_poincare` | Semigroup L² decay bound + ergodicity |
| `bakryEmery_variance_decay` | Poincaré + Grönwall (Mathlib) |
| `bakryEmery_logSobolev` | Entropy decay bound + entropy ergodicity |
| `resolvent_ibp_axiom` | Promoted to `LogConcaveMeasure` structure fields |
| `integrated_bochner_axiom` | Promoted to `LogConcaveMeasure` structure fields |

## Matrix semigroup module (Matrix/)

Diamagnetic inequality for finite matrices via 5-step semigroup proof
(Simon, Functional Integration Ch. 22).

| File | Proved | Axioms |
|---|---|---|
| `HeatKernel.lean` | `heat_kernel_entrywise_nonneg` (Metzler shift), `euler_factor_nonneg`, `isEntryNonneg_pow/mul/add` | 1: `exp_entryNonneg_of_entryNonneg` |
| `LaplaceTransform.lean` | `IsPosDef` definition | 1: `m_matrix_inverse_nonneg` |
| `Trotter.lean` | — | 1: `trotter_product_formula` |
| `Diamagnetic.lean` | `complexShiftedMatrix` definition | 1: `diamagnetic_resolvent` |

## Instances

| Instance | Fields proved | Sorry's | Notes |
|---|---|---|---|
| TwoPoint ({0,1}) | 19/21 | 2 (math false) | Γ_leibniz + entropy decay fail for jump processes |
| Gaussian1D (ℝ, N(0,1)) | 9/23 | 14 (math true) | All fields valid; sorry's are Lean infrastructure gaps |
| BrascampLieb (ℝⁿ, e^{-V}) | All downstream theorems proved | 0 | From structure fields |

## Proved results (highlights)

### Bakry-Émery theory (Diffusion/CarreDuChamp.lean)
- `satisfiesPoincare`: Var(f) ≤ (1/ρ) E(f,f) — **proved**
- `variance_decay`: Var(P_t f) ≤ e^{-2ρt} Var(f) — **proved** (Grönwall)
- `satisfiesLogSobolev`: Ent(f²) ≤ (2/ρ) E(f,f) — **proved**

### Brascamp-Lieb inequality (Instances/BrascampLieb.lean)
- `brascampLieb`: Var_μ(f) ≤ ∫⟨∇f, g⟩ dμ — **proved**
- `brascampLieb_poincare`: Var ≤ (1/ρ)∫‖∇f‖² when Hess V ≥ ρI — **proved**
- `hessian_injective`, `hessian_surjective`, `continuous_hessianInverse_gradient` — **proved**

### Doeblin's condition (Convergence/Doeblin.lean)
- `doeblin_one_step_contraction`, `doeblin_tv_contraction` — **proved**
- `doeblin_n_step_mixing`: |T^n(δ_x)(A)-π(A)| ≤ (1-ε)^n — **proved** (induction)
- `doeblin_correlation_decay`: |cov| ≤ 2B²(1-ε)^d — **proved**

### TV-integral bounds (Convergence/IntegralBounds.lean)
- `tv_integral_bound`: |∫f dμ - ∫f dπ| ≤ Cδ — **proved** (layer cake)
- `tv_integral_bound_abs`: same for |f| ≤ B — **proved** (shift trick)

### Heat kernel positivity (Matrix/HeatKernel.lean)
- `heat_kernel_entrywise_nonneg`: exp(-tM) ≥ 0 for Z-matrices — **proved** (Metzler shift)
- `euler_factor_nonneg`: I - (t/n)M ≥ 0 for large n — **proved**
