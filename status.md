**12 axioms. 2 sorry's total**, all quarantined in
`Instances/WorkInProgress/TwoPoint.lean` (mathematically false for
jump processes — validates that the diffusion axiom is a real
constraint). The Euclidean (Gaussian1D) instance previously held 9
sorries flagging Lean-infrastructure gaps (parametric Fubini,
differentiation under the Gaussian integral, Mehler-kernel
arithmetic); these were converted to nine textbook axioms with full
BGL Ch. 2 / Gross 1975 citations after a Gemini soundness review
(gemini-3-pro-preview) which flagged one missing `IsCore` hypothesis
on the Mehler-composition axiom (now patched in both the axiom and
the corresponding `BakryEmerySpace.semigroup_add` field). Five of
the original nine were subsequently **reduced to theorems** proved
from the remaining four atomic axioms plus Mathlib's Gaussian
infrastructure: `ouSemigroup_l2_decay_bound` (FTC + gradient_decay +
l2_sq_hasDerivWithinAt), `ouSemigroup_ergodic` (double-DCT on the
Mehler integrand + `IsCore`-boundedness),
`ouSemigroup_entropy_sq_ergodic` (Mehler DCT +
`Real.continuous_mul_log` + compactness bound on `s log s`),
`ouSemigroup_compose` (Gaussian-convolution arithmetic via
`gaussianReal_add_gaussianReal_of_indepFun` and `gaussianReal_const_mul`),
and `gaussian2D_orthogonal_invariance` (proved via Codex; bridges
`γ.prod γ` to `stdGaussian (WithLp 2 (ℝ × ℝ))` through the
`EuclideanSpace ℝ (Fin 2) ≃ₗᵢ WithLp 2 (ℝ × ℝ)` isometry, then
applies Mathlib's `map_pi_eq_stdGaussian` and `stdGaussian_map` for
linear-isometric-equivalence invariance). Net: 4 atomic axioms in
Gaussian1D.
**Zero sorry's in the main tree** (Abstract/, Diffusion/,
Convergence/, Coupling/, Dobrushin/, DobrushinZegarlinski/, Matrix/,
and the three sorry-free concrete instances in `Instances/`:
BrascampLieb, Torus, GFFIdentification).

## Project structure

| Module | Files | Sorry's | Axioms | Description |
|---|---|---|---|---|
| Abstract/ | 6 | 0 | 4 | Dirichlet forms, Poincaré, LSI, Holley-Stroock, Gross, Borell-Herbst concentration, LSI⇒Poincaré |
| Diffusion/ | 5 | 0 | 0 | BakryEmerySpace, carré du champ, L² bridge |
| Convergence/ | 5 | 0 | 0 | Doeblin, spectral gap, entropy decay, ergodicity |
| Instances/BrascampLieb | 1 | 0 | 0 | Brascamp-Lieb inequality (fully proved) |
| Instances/WorkInProgress/TwoPoint | 1 | 2 | 0 | Two-point space (2 sorry's = math false) |
| Instances/WorkInProgress/Euclidean | 1 | 0 | 4 | Standard Gaussian / OU (axioms = BGL Ch. 2 textbook bridges, GR-vetted; `l2_decay_bound`, `ergodic`, `entropy_sq_ergodic`, `compose`, `gaussian2D_orthogonal_invariance` reduced to theorems from the atomic four) |
| Matrix/ | 4 | 0 | 2 | Heat kernel, Trotter, diamagnetic inequality |
| Coupling/ | 1 | 0 | 0 | TV coupling characterization |
| Dobrushin/ | 5 | 0 | 0 | Gibbs specs, uniqueness, Neumann series, B3 correlation decay |
| DobrushinZegarlinski/ | 7 | 0 | 2 | Continuous spins: gradient interaction, local LSI, global LSI (Otto-Reznikoff), entrywise covariance (Helffer-Sjöstrand) |

## Axioms

### Core (Abstract/)

| Axiom | Reference | Obstacle |
|---|---|---|
| `gross_lsi_implies_hypercontractive` | Gross (1975) Thm 1 | L^p norm differentiation |
| `gross_hypercontractive_implies_lsi` | Gross (1975) Thm 2 | Linearization at t=0 |
| `herbst_mgf_bound` | BGL §5.4.1 (Herbst's lemma); Ledoux (2001) §1; Otto-Villani (2000) JFA 173 §3 | Sub-Gaussian moment generating function bound: `mgf (F − E F) μ t ≤ exp(L²t²/(2c))` for L-Lipschitz F under LSI(c). Apply LSI to `exp(λF/2)` — bootstrap problem (requires exponential integrability we are trying to prove). Rigorous treatment uses truncation + mollification + monotone limit. **The full concentration theorem `lipschitz_concentration_of_lsi` is *proven* from this axiom + Mathlib's Chernoff bound** `measure_ge_le_exp_mul_mgf` |
| `poincare_of_lsi` | BGL Proposition 5.1.3 (LSI ⇒ Poincaré with same constant) | The Poincaré inequality `Var_μ(f) ≤ (1/c) ∫ ‖∇f‖² dμ`. Standard linearization of LSI on `f = 1 + εg` and ε → 0 limit. Equivalent (via DirichletForm bridge) to existing `logSobolev_implies_poincare_bounded`. **The Lipschitz variance bound `Var(F) ≤ L²/c` is *proven* from this + Mathlib's `norm_fderiv_le_of_lipschitz`** |

### Matrix/

| Axiom | Reference | Obstacle |
|---|---|---|
| `m_matrix_inverse_nonneg` | Berman-Plemmons Ch. 6 | Laplace transform integral |
| `diamagnetic_resolvent` | Simon Ch. 22 | Assembles 5-step proof |

### Instances/WorkInProgress/Euclidean (Gaussian1D / OU semigroup, BGL Ch. 2)

Four textbook axioms packaging the Mehler-kernel-level facts for the
standard Gaussian Bakry-Émery instance. All hypotheses use the local
`IsCore f := ContDiff ℝ ⊤ f ∧ ‖f‖, ‖f'‖, ‖f''‖ uniformly bounded`. All
nine originally introduced were vetted in one pass via Gemini chat
(gemini-3-pro-preview); verdict per axiom is recorded in the Sources
column. The single fix flagged by Gemini was the missing `IsCore`
hypothesis on `ouSemigroup_compose` (without it, Lean's
`integral`-returns-0 default on non-integrable Mehler integrals could
in principle desync the two sides of the semigroup property); this
hypothesis was added to the axiom AND to `BakryEmerySpace.semigroup_add`
upstream — and `compose` was subsequently proved as a theorem.

Five of the original nine were **reduced to theorems** proved from
the remaining four atomic axioms plus Mathlib's `stdGaussian` /
Gaussian-convolution / DCT machinery. The four remaining axioms are
genuinely atomic Mehler-kernel-level facts that would each require
substantial Mathlib infrastructure (parametric differentiation under
the Gaussian integral) currently absent at the required generality.
The remaining entropy decay axiom would not be reducible even with
full infrastructure without introducing a new atomic axiom (de Bruijn
entropy-derivative identity).

| Axiom / Theorem | Reference | Status | Sources |
|---|---|---|---|
| `gaussian2D_orthogonal_invariance` | BGL §1.10.1 (rotation invariance of 2D standard Gaussian) | **Theorem** — proved via Codex (GPT-5.4): bridges `γ.prod γ` to `stdGaussian (WithLp 2 (ℝ × ℝ))` through the `EuclideanSpace ℝ (Fin 2) ≃ₗᵢ WithLp 2 (ℝ × ℝ)` isometry, applies Mathlib's `map_pi_eq_stdGaussian` to identify pushforward of `Measure.pi γ` with `stdGaussian (EuclideanSpace ℝ (Fin 2))`, then `stdGaussian_map` for the linear-isometric-equivalence invariance, finally unwraps via `WithLp.toLp / ofLp`. | (proved) |
| `ouSemigroup_preserves_IsCore` | BGL §2.7 (OU smoothing) | **Theorem** (decomposed 2026-05-12): bounded parts proved via `ouSemigroup_preserves_bounds` + generalized Mehler-derivative `hasDerivAt_ouSemigroup_C1` + second-order formula `hasDerivAt_deriv_ouSemigroup`; only `ContDiff ⊤` residue remains as smaller atomic axiom `ouSemigroup_contDiff`. | (proved); residue `ouSemigroup_contDiff` (vetted: Standard) |
| `ouSemigroup_gradient_decay` | BGL Theorem 5.5.2 | **Theorem** — proved from new theorem `hasDerivAt_ouSemigroup` (Mehler derivative via Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`) + pointwise Jensen + Fubini/`ou_kernel_map` for γ-invariance. | (proved) |
| `ouSemigroup_l2_sq_hasDerivWithinAt` | BGL Proposition 4.7.1 | Atomic axiom (differentiation under integral against the Gaussian density). | GR (vetted: Standard) |
| `ouSemigroup_entropy_sq_decay_bound` | BGL Theorem 5.5.2 / §5.5 | Atomic axiom (would require new entropy-derivative atomic axiom — de Bruijn identity — to reduce; deferred). | GR (vetted: Standard, constant verified) |
| `ouSemigroup_compose` | BGL §2.7.1 (Mehler kernel arithmetic) | **Theorem** — proved via Gaussian-convolution arithmetic: both sides of `P_{s+t} f = P_s(P_t f)` equal `∫ f(e^{-(s+t)}x + w) dN(0, b_{s+t}²)(w)`. Uses `gaussianReal_add_gaussianReal_of_indepFun` + `gaussianReal_const_mul` + `HasLaw` + Fubini. (Patched at axiom stage: `IsCore f` hypothesis added per Gemini soundness review.) | (proved; Flagged → Patched → Standard at axiom stage) |
| `ouSemigroup_l2_decay_bound` | BGL Proposition 4.7.1 | **Theorem** — proved from `gradient_decay` + `l2_sq_hasDerivWithinAt` + FTC inequality (`integral_le_sub_of_hasDeriv_right_of_le`). | (proved) |
| `ouSemigroup_ergodic` | BGL Proposition 4.2.1 | **Theorem** — proved via double DCT on the Mehler integrand: `P_t f(x) → ∫f` for each `x` (inner DCT) → `(P_t f)² → (∫f)²` → `∫(P_t f)² → (∫f)²` (outer DCT). | (proved) |
| `ouSemigroup_entropy_sq_ergodic` | BGL Proposition 5.2.1 | **Theorem** — proved via the same Mehler DCT pattern as `ergodic` (inner DCT for `P_t(f²) → ∫f²`) plus outer DCT for `s · log s` using `Real.continuous_mul_log` + `IsCompact.bddAbove` for the uniform bound on `[0, M²]`. Mean preservation `∫P_t(f²) = ∫f²` cancels the boundary term. | (proved) |

### DobrushinZegarlinski/

| Axiom | Reference | Obstacle | Sources |
|---|---|---|---|
| `zegarlinski_lsi_inequality` | Otto–Reznikoff (2007), J. Funct. Anal. 243, Thm 1; Zegarlinski (1996), Comm. Math. Phys. 175; BGL Thm 5.7.5 | Functional inequality assembly: composes the proven `entropy_decomposition_single_site`, uniform local LSI, and Neumann series row bound on `J/c` (Schur estimate). Hypotheses include `IsGibbsSpecificationFor spec V` (links spec to potential), explicit integrability of `f²`, `f²·log f²`, `‖∇f‖²`, and the corrected `ZegarlinskiCondition` (`Σ J/c ≤ α < 1`, NOT `c·J ≤ α`) | GR (Gemini chat, gemini-3-pro-preview): rated `Likely correct` after fixes for (a) algebra direction, (b) integrability, (c) spec↔V linking |
| `cov_entrywise_bound_of_zegarlinski` | Helffer & Sjöstrand (1994) J. Stat. Phys. 74; Naddaf & Spencer (1997) Comm. Math. Phys. 183; BGL §4.5 | Entrywise covariance bound `\|Cov(σ_x, σ_y)\| ≤ (1/c) · neumannEntrywise(J/c) x y`. Helffer-Sjöstrand integral identity for Cov + Neumann expansion of inverse Hessian + log-concavity. Required hypotheses: `IsGibbsSpecificationFor spec V` (with substantive Boltzmann-density Prop), `UniformLocalLSI spec c`, `h_convex` (uniform `Hess V_xx ≥ c`, NOT implied by local LSI alone — counterexample is double-well `x⁴ - 5x² + …`), `ZegarlinskiCondition V c`, and **L²** integrability of coordinate functions | GR (Gemini chat, gemini-3-pro-preview): rated `Likely correct` after the FIVE total fixes from chat + deep-review passes: (1) missing `h_convex` (uniform strict log-concavity), (2) `IsGibbsSpecificationFor` made substantive (not `True` placeholder — closes a soundness hole), (3) integrability strengthened from L¹ to L², (4) algebra direction in `ZegarlinskiCondition` (`J/c` not `c·J`), (5) integrability of `f²`, `f² log f²`, `‖∇f‖²` for the LSI side. This is the bridge pphi2N's `HSData.AdmitsThimbleLocal` consumes for the strict-thermodynamic-limit mass-gap proof |

**DZ-layer axiom audit (`#print axioms`, verified 2026-05-01):**
The proven content of `DobrushinZegarlinski/` — `AbstractInfluenceMatrix`
theory, `entropy_decomposition_single_site` (S1),
`integral_siteSmoothing` (DLR-at-Bochner-integral),
`iterate_dist_zero` / `neumann_series_nn_dist_bound` (distance-aware
Neumann), and the exponential-decay corollary `cov_entrywise_decay_nn`
— is *axiom-free* (depends only on `propext`, `Classical.choice`,
`Quot.sound`). Only the two textbook axioms above appear in the
`#print axioms` of the LSI / Cov bridge theorems themselves.

**Removed axiom (Gemini-flagged false):** `entropy_chain_rule_local`
was previously stated as
`Ent_μ(g) ≤ Σ ∫ Ent_{γ.condDist {x} σ}(g) dμ`
without coupling-dependent constant. Counterexample: low-temperature
Ising at `T → 0` has Dirac single-site conditionals (RHS = 0) while
LHS > 0 for non-constant `g`. The cited Stroock–Zegarlinski result
is an *equivalence* between mixing and LSI, not a universal chain
rule. The actual proof of `zegarlinski_lsi_inequality` does not
factor through such a free-standing axiom; the iteration of the
proven `entropy_decomposition_single_site` against local LSI plus
Neumann decay is interleaved.

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

### Instances/WorkInProgress/TwoPoint.lean (2 sorry's — mathematically false)
- `Γ_leibniz` — Leibniz/diffusion property fails for jump processes
- `semigroup_entropy_sq_decay_bound` — consequence of Leibniz failure

### Instances/WorkInProgress/Euclidean.lean (0 sorry's, 3 axioms)
The previously-flagged 9 sorries (Lean-infrastructure gaps for
Mehler-kernel facts) were converted to nine BGL Ch. 2 textbook axioms
in one pass with Gemini vetting (see "Instances/WorkInProgress/Euclidean"
table above). Five of the original nine were **reduced to theorems**:
FTC inequality (l2_decay_bound), double-DCT on the Mehler integrand
(ergodic), Gaussian convolution arithmetic via
`gaussianReal_add_gaussianReal_of_indepFun` + `gaussianReal_const_mul`
(compose), `Real.continuous_mul_log` + compactness for `s log s`
(entropy_sq_ergodic), and Mathlib's `stdGaussian_map` /
`map_pi_eq_stdGaussian` chain via the `EuclideanSpace ℝ (Fin 2) ≃ₗᵢ
WithLp 2 (ℝ × ℝ)` isometry (gaussian2D_orthogonal_invariance, proved
by Codex). The four remaining axioms are atomic Mehler-kernel facts
(differentiation under the Gaussian integral, entropy derivative
formula); reducing them would require parametric Fubini /
differentiation-under-the-Gaussian-integral infrastructure not
currently in Mathlib at the required generality.

### Dobrushin/ (0 sorry's)
Complete: Specification, Uniqueness (with bridge hypothesis for
hMargToFull), StrongCoupling, FiniteLattice, NeumannSeries,
CovarianceBoundMultisite, CondTVBridge, CondKernelDLR. An earlier
single-site B2 stub (`dobrushin_covariance_iterateInfluence_bound`
and its corollary) was removed as subsumed by the multisite bound
in `CovarianceBoundMultisite.lean`.

### DobrushinZegarlinski/ (0 sorry's, 2 axioms)
Continuous-spin layer for Zegarlinski's theorem. 7 files:
- `AbstractInfluence.lean` — abstract Neumann decay (proven; pure linear algebra).
- `EuclideanTransport.lean` — `GibbsSpec.toEuclideanMeasure` adapter.
- `InteractionMatrix.lean` — gradient interaction `J_{xy}` via mixed `fderiv` on `EuclideanSpace ℝ Λ`; bridge `gradInteractionMatrix` (uses `J/c`) gated on `ContDiff ℝ 2 V`.
- `LocalLSI.lean` — thin `SatisfiesLSI` predicate (with integrability hypotheses) + `UniformLocalLSI` class.
- `EntropyChainRule.lean` — `entropy`, `siteSmoothing`, the *proven* DLR-at-Bochner-integral identity (`integral_siteSmoothing`) and S1 single-site decomposition. Earlier `entropy_chain_rule_local` axiom REMOVED after Gemini review (mathematically false without coupling).
- `GlobalLSI.lean` — `ZegarlinskiCondition` (`J/c ≤ α`, the Otto-Reznikoff form), `IsGibbsSpecificationFor` link class, `global_lsi_of_zegarlinski` (positivity proven, functional inequality is the textbook axiom `zegarlinski_lsi_inequality`).
- `EntrywiseCovariance.lean` — `neumannEntrywise`, `coord`, `covCoord`, and the textbook axiom `cov_entrywise_bound_of_zegarlinski` (Helffer-Sjöstrand). The bridge pphi2N consumes for the strict-thermodynamic-limit covariance bound `|Cov(σ_x, σ_y)| ≤ (1/c) · neumannEntrywise(J/c) x y`.

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
Infrastructure for lgt mass-gap proof. 0 axioms, 0 sorries.
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

### Gaussian instance (Instances/WorkInProgress/Euclidean.lean)
- `ouSemigroup` (Mehler formula), `ouGamma`, `ouEnergy` — defined
- `energy_smul_left`, `energy_symm`, `energy_nonneg`, `energy_const` — **proved**
- `Γ_symm`, `Γ_nonneg`, `Γ_const`, `energy_eq_integral_Γ` — **proved**
- `semigroup_zero` — **proved**
- `ou_kernel_map`: (γ×γ).map φ = γ — **proved** (Gaussian convolution)
