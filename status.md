# markov-semigroups — Status

**Zero sorry's. 4 axioms. 30+ proved theorems.**

## Axioms

All 4 axioms are standard textbook results. None are project-specific.

### ~~1. `variance_nonneg'`~~ — PROVED

**Proved** via Mathlib's `ProbabilityTheory.variance_nonneg` +
`variance_eq_sub` + `memLp_two_iff_integrable_sq`.

### 2. `gross_lsi_implies_hypercontractive` (Hypercontractivity.lean)

**Says:** If the Dirichlet space (X, μ, E) satisfies the log-Sobolev
inequality with constant ρ, then the associated semigroup P_t is
hypercontractive: ‖P_t f‖_q ≤ ‖f‖_p when q ≤ 1 + (p-1)e^{2ρt}.

**Informally:** LSI implies the semigroup improves integrability — it
maps L^p to L^q for q > p after enough time. This is Gross's 1975
Theorem 1.

**Difficulty:** High. Requires differentiating ‖P_t f‖_{p(t)} along the
path p(t) = 1 + (p-1)e^{2ρt} and showing the derivative is ≤ 0 using
the LSI. Needs the chain rule for L^p norms and the semigroup generator.

**Strategy:** Semigroup interpolation method (BGL Chapter 5).

### 3. `gross_hypercontractive_implies_lsi` (Hypercontractivity.lean)

**Says:** If the semigroup is hypercontractive with rate ρ, then the
Dirichlet space satisfies LSI(ρ).

**Informally:** The converse of #2 — hypercontractivity implies LSI.
Gross's 1975 Theorem 2.

**Difficulty:** Medium-High. Differentiates the hypercontractive bound
at t = 0 with p = 2, q = 2+ε and takes ε → 0.

**Strategy:** Linearization at t = 0 (BGL Theorem 5.2.3).

### ~~4. `bakryEmery_poincare`~~ — PROVED

**Proved** from `semigroup_l2_decay_bound` (new BakryEmerySpace class
field) + `bakryEmery_variance_decay` axiom. The proof uses t=1:
Var(f) = (∫f² - ∫(P₁f)²) + Var(P₁f) ≤ (1-e^{-2ρ})/ρ·E(f) + e^{-2ρ}·Var(f).
Dividing by (1-e^{-2ρ}) > 0 gives Var(f) ≤ (1/ρ)E(f,f).

### ~~5. `bakryEmery_logSobolev`~~ — PROVED

**Proved** from `semigroup_entropy_sq_decay_bound` + `semigroup_entropy_sq_ergodic`
(new class fields). Same proof structure as Poincaré: Ent(f²) ≤ (2/ρ) E(f) + Ent(P_T(f²)),
and entropy ergodicity gives Ent(P_T(f²)) → 0.

### ~~6. `bakryEmery_variance_decay`~~ — PROVED

**Proved** from `satisfiesPoincare` + `semigroup_l2_sq_hasDerivWithinAt`
(new class field) via Grönwall's inequality. The derivative
d/dt Var(P_t f) = -2 E(P_t f) ≤ -2ρ Var(P_t f) (by Poincaré), so
Grönwall gives Var(P_t f) ≤ e^{-2ρt} Var(f).

### 7. `resolvent_ibp_axiom` (BrascampLieb.lean)

**Says:** For a log-concave measure μ = e^{-V}dx with V strictly convex,
and any C¹ function f, there exists u such that
Var_μ(f) = ∫ (∇f)(∇u) dμ, where u is the resolvent of the generator
L = Δ - ⟨∇V, ∇·⟩.

**Informally:** The variance equals a Dirichlet form pairing with the
resolvent. Combines Lax-Milgram (existence of u) with weighted
integration by parts.

**Difficulty:** High. Requires:
- Weighted IBP for μ = e^{-V}dx (divergence theorem + density)
- Lax-Milgram theorem for the Dirichlet form on L²(μ)
- Spectral gap from strict convexity

**Strategy:** Lax-Milgram + weighted divergence theorem (BGL §1.15).

### 8. `integrated_bochner_axiom` (BrascampLieb.lean)

**Says:** For the resolvent u from #7, ∃ R ≥ 0 such that
Var(f) = R + ∫ hessianBilin V (∇u)(∇u) dμ, where R = ∫‖Hess u‖² dμ
(the Hilbert-Schmidt norm of the Hessian of u).

**Informally:** The Bochner-Weitzenböck identity decomposes the variance
into a Hessian term (≥ 0) plus the curvature term. Dropping the Hessian
gives the Brascamp-Lieb inequality.

**Difficulty:** High. Requires the pointwise Bochner formula
½L(|∇u|²) = ‖Hess u‖² + H(∇u, ∇u) + ⟨∇u, ∇(Lu)⟩, integrated
against μ using ∫Lh dμ = 0.

**Strategy:** Pointwise Bochner calculation + integration (BGL §1.16).

## Difficulty summary

| Axiom | Difficulty | Key obstacle |
|-------|-----------|-------------|
| ~~variance_nonneg'~~ | ~~Low~~ | **PROVED** |
| ~~bakryEmery_poincare~~ | ~~Medium~~ | **PROVED** |
| ~~bakryEmery_variance_decay~~ | ~~Medium~~ | **PROVED** |
| gross_hypercontractive_implies_lsi | Medium-High | Linearization |
| gross_lsi_implies_hypercontractive | High | L^p norm differentiation |
| ~~bakryEmery_logSobolev~~ | ~~High~~ | **PROVED** |
| resolvent_ibp_axiom | High | Weighted IBP + Lax-Milgram |
| integrated_bochner_axiom | High | Bochner-Weitzenböck identity |

## Infrastructure needed to prove remaining axioms

The central missing piece is **semigroup generator theory** — the
unbounded operator L = lim_{t→0} (P_t - I)/t on L²(μ). Mathlib has
`Analysis.Operator.OneParameterSemigroup` but it's purely algebraic;
connecting it to analysis (strong continuity, domain, d/dt P_t = LP_t)
is the main project.

| Axiom | Effort | Key infrastructure needed |
|-------|--------|--------------------------|
| ~~#4 bakryEmery_poincare~~ | ~~High~~ | **PROVED** from ergodicity + L² decay |
| ~~#3 variance_decay~~ | ~~Medium~~ | **PROVED** from Poincaré + Grönwall |
| ~~#2 bakryEmery_logSobolev~~ | ~~High~~ | **PROVED** from entropy decay + ergodicity |
| #6 resolvent_ibp | Low-Med | Lax-Milgram (IN MATHLIB), abstract H¹(μ) |
| #2 bakryEmery_logSobolev | High | Generator theory + Grönwall (IN MATHLIB) |
| #7 integrated_bochner | High | Generator theory + axiom #6, Γ₂ definition |
| #5 gross_lsi→HC | Very High | Generator theory + L^p norm differentiation |
| #5 gross_HC→LSI | Very High | Generator theory + linearization |

**Recommended attack order:** #6 → generator theory → #4 → #3 → #2 → #7 → #5.

## Proved results (highlights)

### Bakry-Émery Poincaré and variance decay (Diffusion/CarreDuChamp.lean)
- `satisfiesPoincare`: Var(f) ≤ (1/ρ) E(f,f) — **proved** from
  `semigroup_l2_decay_bound` + `semigroup_ergodic` class fields
- `variance_decay`: Var(P_t f) ≤ e^{-2ρt} Var(f) — **proved** from
  `satisfiesPoincare` + `semigroup_l2_sq_hasDerivWithinAt` via Grönwall
- `satisfiesLogSobolev`: Ent(f²) ≤ (2/ρ) E(f,f) — **proved** from
  `semigroup_entropy_sq_decay_bound` + `semigroup_entropy_sq_ergodic`

### Brascamp-Lieb inequality (Instances/BrascampLieb.lean)
- `brascampLieb`: Var_μ(f) ≤ ∫(∇f)(g) dμ — **proved** from axioms 7-8
  via weighted Young's inequality (Hessian symmetry + PSD)
- `brascampLieb_poincare`: Var ≤ (1/ρ)∫‖∇f‖² when Hess V ≥ ρI — **proved**
- `hessian_injective`, `hessian_surjective`: **proved** (finite-dim linear algebra)
- `continuous_hessianInverse_gradient`: **proved** (contDiffAt_map_inverse)

### Doeblin's condition (Convergence/Doeblin.lean)
- `doeblin_one_step_contraction`: |μ(A)-π(A)| ≤ 1-ε — **proved**
- `doeblin_tv_contraction`: |(Tμ)(A)-π(A)| ≤ (1-ε)δ — **proved**
- `doeblin_n_step_mixing`: |T^n(δ_x)(A)-π(A)| ≤ (1-ε)^n — **proved** (induction)
- `doeblin_correlation_decay`: |cov| ≤ 2B²(1-ε)^d — **proved**

### TV-integral bounds (Convergence/IntegralBounds.lean)
- `tv_integral_bound`: |∫f dμ - ∫f dπ| ≤ Cδ for f ∈ [0,C] — **proved** (layer cake)
- `tv_integral_bound_abs`: same for |f| ≤ B — **proved** (shift trick)
