> **Note (2026-05-17):** the historical headline below predates the
> Lp-carrier / Gross-discharge work. **Current state is the
> 2026-05-17 dated section** ("Gross-discharge — G2 complete")
> further down; `AXIOM_AUDIT.md` is canonical for the registered
> axiom set. On the branch `feat/lp-carrier-stdGaussianFin-dirichletmarkov`
> there are 18 declared `.lean` axioms and 9 `sorry` decls (8 in the
> WIP `Abstract/GrossODE.lean`, 1 quarantined in `TwoPoint.lean`).

> **Update (2026-05-19, Workstream N1.c, branch
> `discharge/n1c-entropy-decay`):** the GaussianFin axiom
> `ouSemigroupFin_entropy_sq_decay_bound` (BGL Thm 5.5.2, n-dim
> entropy decay for `f²`) has been **converted from `axiom` to
> `theorem`** with the vetted telescoping route partially formalized.
> Four key supporting lemmas are **fully proved and axiom-free**
> (`Gaussian1D.boltzmannEntropy_ouSemigroup_decay_le`,
> `entropy_sub_eq_boltzmann_sub`, `boltzmannEntropyFin_ouCoord_step_le`,
> `sum_fisherInfoFinCoord_sq_add_const_le`), plus the `ouCoord`
> operator and its bridges. **2026-05-19 follow-up:** the **ε→0 DCT
> tail** is now discharged as the axiom-free lemma
> `boltzmannSubFin_le_of_perEps` (plus helper
> `ouSemigroupFin_sq_add_const`), and the **T1 factorization
> scaffolding** `setShift`/`ouCoordSet` (with `ouCoordSet_empty = id`,
> `ouCoordSet_univ = ouSemigroupFin`) is in place — all axiom-free. The
> main theorem now discharges Step 1 (entropy→Boltzmann) and Step 2
> (ε-reduction) in its body; the **one documented `sorry`** is now the
> per-ε telescoping core only (T1 composition step + T2 orthogonal
> Fisher monotonicity; T3 already proved). Full `lake build` green;
> `#print axioms ouSemigroupFin_entropy_sq_decay_bound = [propext,
> sorryAx, Classical.choice, Quot.sound]`. See `AXIOM_AUDIT.md` row.

**11 axioms. 2 sorry's total**, all quarantined in
`Instances/WorkInProgress/TwoPoint.lean` (mathematically false for
jump processes — validates that the diffusion axiom is a real
constraint). The Euclidean (Gaussian1D) instance previously held 9
sorries flagging Lean-infrastructure gaps (parametric Fubini,
differentiation under the Gaussian integral, Mehler-kernel
arithmetic); these were converted to nine textbook axioms with full
BGL Ch. 2 / Gross 1975 citations after a Gemini soundness review
(gemini-3-pro-preview) which flagged one missing `IsCore` hypothesis
on the Mehler-composition axiom (now patched in both the axiom and
the corresponding `BakryEmerySpace.semigroup_add` field). All nine
original Gaussian1D axioms have been **reduced to theorems**: the
five early discharges
(`ouSemigroup_l2_decay_bound`, `ouSemigroup_ergodic`,
`ouSemigroup_entropy_sq_ergodic`, `ouSemigroup_compose`,
`gaussian2D_orthogonal_invariance`), plus 2026-05-12 discharges of
`ouSemigroup_gradient_decay`, `ouSemigroup_l2_sq_hasDerivWithinAt`,
`ouSemigroup_preserves_IsCore` / `ouSemigroup_contDiff` (Path C
Hermite IBP in `EuclideanHermite.lean`), and
`ouSemigroup_entropy_sq_decay_bound` (A1+A2 decomposition in
`EuclideanEntropyDecay.lean`). **All three sub-axioms in
`General/OUEntropyDecomposition.lean` are now also proved**: A1 via
Cauchy-Schwarz on the Mehler probability kernel, A2 (de Bruijn for
`t > 0`) via Stein-IBP formula for `(P_t g)''` + parametric DCT +
bilinear Dirichlet form identity, and A2-boundary via A2 interior +
DCT-based continuity. The entire Gaussian1D + General/OU chain is
**axiom-free**.

**2026-05-13 / 2026-05-19: Multivariate Gaussian BE-instance landed (Stage N1 / Phase 2.5).**
The new `stdGaussianFin.bakryEmerySpace n : BakryEmerySpace (Fin n → ℝ)`
in `Instances/WorkInProgress/EuclideanFin.lean` (commit `8ed9e52`,
~2850 lines, 0 sorries) originally carried 3 textbook axioms — all
gemini-3.1-pro-preview vetted **Standard**, all tensor-lift analogues
of the proved 1D BE chain. As of **2026-05-19**, Phase 2.5 discharges
`ouSemigroupFin_l2_sq_hasDerivWithinAt` as a theorem in
`Instances/WorkInProgress/EuclideanFinBE.lean` via the existing G2
axioms `gaussianFin_diffQuot_tendsto_Lp` and
`gaussianFin_integrationByParts`, so the remaining BE axioms are:
- `ouSemigroupFin_preserves_IsCore` (BGL §2.7.1 + §3, Mehler smoothing
  preservation)
- `ouSemigroupFin_entropy_sq_decay_bound` (BGL Thm 5.5.2, entropy decay)

> **POST-MERGE RECONCILIATION (2026-05-16, commit `ba9a8de`).** The
> `feat/lp-carrier-stdGaussianFin-dirichletmarkov` branch was merged
> into `main` (Lp-carrier `stdGaussianFin` DMS + Gross H0/G1/G2).
> **Merged `main` builds green** (lib 3202 jobs + WIP generator stack
> 3110 jobs, 0 errors); downstream insulated (pphi2N/lgt pin frozen
> commits, gaussian-hilbert pins the branch). The git 3-way auto-merge
> stitched divergent doc narratives — **this line is the canonical
> count; older stitched paragraphs above/below (e.g. "11 axioms",
> "unchanged at 11") are superseded.**

Registered axiom count: **13** (9 non-WIP + 4 WIP). History: 8 → 11
at the N1 merge (commit `8ed9e52`, 2026-05-13); → 12 on 2026-05-16
(repo-wide audit registered `contDiff_top_convolution_schwartzKernel`,
`General/SchwartzConvolution`, no consumers); → **13 on 2026-05-16**
when the branch merge added the **vetted general**
`gaussianOU_heatEquation_within_zero`
(`Instances/WorkInProgress/EuclideanGeneratorLimit.lean`; BGL §2.7;
GR-vetted Standard/Likely correct; discharges the Gross-G2 blocker
`hasDerivWithinAt_t_ouSemigroupFin_zero` as a *proved* theorem). WIP
breakdown: 3 GaussianFin + 1 `gaussianOU`. A further 4 `EuclideanTests`
test-scaffolding axioms remain excluded by policy (WorkInProgress, not
consumed by the main tree). The merge also added 3 documented WIP
sorries in `Instances/WorkInProgress/EuclideanGenerator{Lp,Limit}`
(`ouGeneratorFin_ibp_integral`, `ouGeneratorFin_ibp` bridge,
`ouSemigroupFinLp_diffQuot_tendsto`) — Gross-G2 in progress.
**Zero sorry's in the main tree** (Abstract/, Diffusion/,
Convergence/, Coupling/, Dobrushin/, DobrushinZegarlinski/, Matrix/,
and the three sorry-free concrete instances in `Instances/`:
BrascampLieb, Torus, GFFIdentification).

**2026-05-15: Lp-carrier Phase 2 — concrete `DirichletMarkovSemigroup`
on `Lp ℝ 2 (γFin n)`.** `Instances/WorkInProgress/EuclideanFinLp.lean`
(branch `feat/lp-carrier-stdGaussianFin-dirichletmarkov`, commit
`6782dc7`) provides the concrete `MarkovSemigroup` and
`DirichletMarkovSemigroup` bundles for the multivariate standard
Gaussian OU semigroup on the new `Lp ℝ 2 (γFin n)` carrier. All seven
operator-valued semigroup laws (P_zero, P_semigroup, P_strong_cont,
P_contraction, P_conservation, P_positivity, P_symmetric) are proved
theorems. The bundle `GaussianFin.stdGaussianFin_dirichletMarkovSemigroup
n : DirichletMarkovSemigroup (Fin n → ℝ)` is the BE → DirichletMarkovSemigroup
bridge that the gaussian-hilbert hypercontractivity discharge plan
called "N3"; its delivery collapses the remaining
`ouSemigroupAct_eLpNorm_hypercontractive` discharge to ~1-2 days of
adapter code (E.1 + E.2 in the
[gaussian-hilbert plan](https://github.com/mrdouglasny/gaussian-hilbert/blob/main/docs/hypercontractivity-discharge-plan.md)).

The bundle's `energy_eq_deriv` field is now obtained from the proved
`ouSemigroupFin_l2_sq_hasDerivWithinAt` theorem. The dependency
surfaces through the already-counted G2 axioms rather than a dedicated
GaussianFin de Bruijn axiom, so this Phase 2.5 discharge drops the
branch-local declared axiom count by one: **19 → 18**.

**Phase 3 wire-in smoke test verified upstream** in gaussian-hilbert
(branch `phase-3-smoke-test`, commit `0f0c5eb`,
`HypercontractivityFromBE.lean`): the bundle is reachable and slots
into `gross_lsi_implies_hypercontractive` cleanly.

**2026-05-17: Gross-discharge — G2 complete; abstract Gross
relocated + scaffolded.** Branch
`feat/lp-carrier-stdGaussianFin-dirichletmarkov`, tip `9c7da37`.

*G2 done.* `GaussianFin.generatorCompat_stdGaussianFin` is
**sorry-free**. Verified `#print axioms` = `propext`,
`Classical.choice`, `Quot.sound` + exactly **two** custom axioms:
`gaussianFin_diffQuot_tendsto_Lp` and `gaussianFin_integrationByParts`
— both *general, Mathlib-native* (no project defs; operator/`fderiv`/
`Measure.pi gaussianReal`), Gemini-vetted **Standard / Likely
correct**, recorded in `AXIOM_AUDIT.md`. A third Gross-discharge
axiom, `gaussianOU_heatEquation_within_zero` (also Standard-vetted),
was subsumed by the DCT axiom and is **off** `generatorCompat`'s live
critical path (retained as reusable textbook infrastructure). These
discharged the deep `EuclideanGenerator{Lp,Limit}` cruxes (heat
equation, γ-IBP, DCT) that Codex stalled on; the prior
`ouGeneratorFin_ibp` Lp-coercion bridge is also closed.

*Abstract Gross relocated + scaffolded.*
`gross_lsi_implies_hypercontractive_of_hypotheses` moved out of
`Abstract/Hypercontractivity.lean` (the `CoreSemigroupInvariant` /
`GeneratorCompat` / `StroockVaropoulos` predicates stay there) into a
new `Abstract/GrossODE.lean`. The legacy
`gross_lsi_implies_hypercontractive` axiom is retained (non-breaking;
gaussian-hilbert keeps compiling) until P2/P3 close and the call-site
is rewired (**W**). In `GrossODE.lean`: the exponent-path calculus
(`grossExponent`, `hasDerivAt_grossExponent` = the `q'=2ρ(q-1)`
coupling), the **P2 chain-rule assembly** (`grossLogNorm_hasDerivWithinAt`
from F'/Ent via `field_simp;ring`), the **P3 `antitoneOn` closure**
(`antitoneOn_of_hasDerivWithinAt_nonpos` on `Set.Ici 0`), and the
elementary `hasDerivAt_abs_rpow_exponent` are **proved**. The P2
bottleneck is **decomposed (no axiom — that would be circular)** into
a general Mathlib-native exponent-path Leibniz lemma (its pointwise
core proved) and a general Mathlib-native Bochner–Leibniz lemma
through a strong-`L²` derivative (the reusable kernel, *to be
proved*, not axiomatized).

*Accurate inventory (this branch; supersedes the stale headline —
`AXIOM_AUDIT.md` is canonical for the registered set).* 18 declared
`.lean` axioms (incl. the 3 Gross-discharge general axioms, 2
remaining `EuclideanFin` BE tensor-lift axioms, 4 `EuclideanTests` scratch
axioms, the legacy abstract Gross/S–V trio, Dobrushin–Zegarliński,
Schwartz-convolution, diamagnetic). 9 `sorry` declarations: **8 in
`Abstract/GrossODE.lean`** (the documented P2/P3 work items —
`grossPow_pos`, `grossEntropy_eq`, the two general Leibniz lemmas,
the `grossPow_hasDerivWithinAt` glue, `grossLogNorm_deriv_nonpos`
(P3 algebra), the `antitoneOn` continuity bridge, and the final
`eLpNorm↔∫·^q` reduction) + **1 in `TwoPoint.lean`** (quarantined,
mathematically false for jump processes). Remaining Gross endgame:
P2 (the one general Leibniz kernel + thin glue) → P3 algebra → W.

## Project structure

| Module | Files | Sorry's | Axioms | Description |
|---|---|---|---|---|
| Abstract/ | 7 | 8 | 5 | Dirichlet forms, Poincaré, LSI, Holley-Stroock, Gross (3: +Stroock-Varopoulos; predicates + relocated theorem in `GrossODE.lean` — P2/P3 scaffold, 8 documented WIP sorries), Borell-Herbst concentration (2: Herbst MGF + LSI⇒Poincaré) |
| Diffusion/ | 5 | 0 | 0 | BakryEmerySpace, carré du champ, L² bridge |
| Convergence/ | 5 | 0 | 0 | Doeblin, spectral gap, entropy decay, ergodicity |
| Instances/BrascampLieb | 1 | 0 | 0 | Brascamp-Lieb inequality (fully proved) |
| Instances/WorkInProgress/TwoPoint | 1 | 2 | 0 | Two-point space (2 sorry's = math false) |
| Instances/WorkInProgress/Euclidean (+EuclideanStein, EuclideanHermite, EuclideanEntropyDecay) | 4 | 0 | 0 | Standard Gaussian / OU. Concrete instance **axiom-free**; the de Bruijn / Fisher-info entropy-decay facts are **discharged as theorems** in `General/OUEntropyDecomposition.lean` (itself axiom-free — AXIOM_AUDIT.md confirms). All 9 original Mehler-kernel axioms discharged. |
| Instances/WorkInProgress/EuclideanFin (+EuclideanFinBE, EuclideanFinLp, EuclideanGenerator{,Lp,Limit,Compat}) | 7 | 0 | 5 | Multivariate Gaussian / Lp-carrier `stdGaussianFin_dirichletMarkovSemigroup`. 2 remaining BE tensor-lift axioms (`ouSemigroupFin_preserves_IsCore`, `ouSemigroupFin_entropy_sq_decay_bound`) + 3 **Gross-discharge general Mathlib-native axioms** (`gaussianOU_heatEquation_within_zero`, `gaussianFin_integrationByParts`, `gaussianFin_diffQuot_tendsto_Lp`), all Gemini Standard-vetted. `generatorCompat_stdGaussianFin` **sorry-free**; `ouSemigroupFin_l2_sq_hasDerivWithinAt` is now a theorem in `EuclideanFinBE.lean`. |
| Instances/WorkInProgress/EuclideanTests | 1 | 0 | 4 | Scaffolding axioms (`gaussianResolvent*`, `gaussianBochner_identity`) — excluded by policy, not consumed by main tree |
| Matrix/ | 4 | 0 | 1 | Heat kernel, Trotter, diamagnetic inequality (`m_matrix_inverse_nonneg` now imported from `SpectralPositivity` as a theorem) |
| Coupling/ | 1 | 0 | 0 | TV coupling characterization |
| Dobrushin/ | 5 | 0 | 0 | Gibbs specs, uniqueness, Neumann series, B3 correlation decay |
| DobrushinZegarlinski/ | 8 | 0 | 2 | Continuous spins: gradient interaction, local LSI, global LSI (Otto-Reznikoff), entrywise covariance (Helffer-Sjöstrand), Lipschitz concentration |
| General/ | 2 | 0 | 1 | OUEntropyDecomposition (axiom-free) + SchwartzConvolution (1 axiom: `contDiff_top_convolution_schwartzKernel`, **Likely correct** — Gemini-vetted 2026-05-12, was unregistered in AXIOM_AUDIT until 2026-05-16; no consumers) |
| Tools/ | 1 | 0 | 0 | Single-site disintegration primitive (consumed by Dobrushin layer / lgt) |

## Axioms

### Core (Abstract/)

| Axiom | Reference | Obstacle |
|---|---|---|
| `gross_lsi_implies_hypercontractive` | Gross (1975) Thm 1 | L^p norm differentiation. Stated on bundled `DirichletMarkovSemigroup` (refactored 2026-05-13 after Gemini 3.1-pro vetting: right-deriv `Set.Ici 0`, `eLpNorm` avoiding the Bochner trap, conservation/positivity/symmetry as structural fields). |
| `gross_hypercontractive_implies_lsi` | Gross (1975) Thm 2 | Linearization at t=0. Same bundled-structure setup. |
| `stroock_varopoulos` | BGL Prop 1.7.1 / §1.7 (Stroock 1992, Varopoulos 1985) | First intermediate-step lemma toward a Gross discharge. `(4(p-1)/p²) · E(f^{p/2}, f^{p/2}) ≤ E(f, f^{p-1})` for nonneg `f` in core with `f^{p/2}, f^{p-1}` in core and `p ≥ 2`. Vetted **Standard** by gemini-3.1-pro-preview (two-pass 2026-05-13): original `f ≥ ε > 0` revised to `f ≥ 0` per Gemini (powers C¹ at 0 for p ≥ 2); re-vet confirmed all edge cases (`p = 2` equality, `f ≡ 0` trivially) handled correctly. No internal consumers yet. |
| `herbst_mgf_bound` | BGL §5.4.1 (Herbst's lemma); Ledoux (2001) §1; Otto-Villani (2000) JFA 173 §3 | Sub-Gaussian moment generating function bound: `mgf (F − E F) μ t ≤ exp(L²t²/(2c))` for L-Lipschitz F under LSI(c). Apply LSI to `exp(λF/2)` — bootstrap problem (requires exponential integrability we are trying to prove). Rigorous treatment uses truncation + mollification + monotone limit. **The full concentration theorem `lipschitz_concentration_of_lsi` is *proven* from this axiom + Mathlib's Chernoff bound** `measure_ge_le_exp_mul_mgf` |
| `poincare_of_lsi` | BGL Proposition 5.1.3 (LSI ⇒ Poincaré with same constant) | The Poincaré inequality `Var_μ(f) ≤ (1/c) ∫ ‖∇f‖² dμ`. Standard linearization of LSI on `f = 1 + εg` and ε → 0 limit. Equivalent (via DirichletForm bridge) to existing `logSobolev_implies_poincare_bounded`. **The Lipschitz variance bound `Var(F) ≤ L²/c` is *proven* from this + Mathlib's `norm_fderiv_le_of_lipschitz`** |

### Matrix/

`m_matrix_inverse_nonneg` (Berman-Plemmons Ch. 6) is **no longer a
local axiom**: it is imported from
`SpectralPositivity.Matrix.MMatrixInverse` and re-exported as a
*theorem* (`LaplaceTransform.lean:82`). Only one local axiom remains.

| Axiom | Reference | Obstacle |
|---|---|---|
| `diamagnetic_resolvent` | Simon Ch. 22 | Assembles 5-step proof |

### Instances/WorkInProgress/Euclidean (Gaussian1D / OU semigroup, BGL Ch. 2)

**Concrete instance is now axiom-free.** All 9 originally-axiomatized
Mehler-kernel-level facts have been discharged. Hypotheses use the
local `IsCore f := ContDiff ℝ ∞ f ∧ ‖f‖, ‖f'‖, ‖f''‖ uniformly bounded`
(refactored 2026-05-12 from `ContDiff ℝ ⊤` after recognizing that
`⊤ : WithTop ℕ∞` is analyticity in current Mathlib, not C^∞).

Discharges:
- `ouSemigroup_compose`, `ouSemigroup_l2_decay_bound`,
  `ouSemigroup_ergodic`, `ouSemigroup_entropy_sq_ergodic`,
  `gaussian2D_orthogonal_invariance` (proved 2025/early 2026).
- `ouSemigroup_gradient_decay` (2026-05-12, via `hasDerivAt_ouSemigroup`).
- `ouSemigroup_l2_sq_hasDerivWithinAt` (2026-05-12, via the heat
  equation + Gaussian Dirichlet form identity + DCT-based boundary
  discharge — see `EuclideanStein.lean`).
- `ouSemigroup_preserves_IsCore` (2026-05-12, decomposed + Path C
  Hermite IBP discharge in `EuclideanHermite.lean`).
- `ouSemigroup_contDiff` (2026-05-12, Path C — see
  `EuclideanHermite.lean`).
- `ouSemigroup_entropy_sq_decay_bound` (2026-05-12) discharged via the
  A1+A2 decomposition. A1 (`ouSemigroup_fisher_info_decay`), A2 (de
  Bruijn for `t > 0`, `hasDerivAt_entropy_ouSemigroup`), and the
  A2-boundary `t = 0+` version were all proved the same day. The
  `MarkovSemigroups/General/OUEntropyDecomposition.lean` file is now
  axiom-free. The atomic Bakry-Émery building blocks remain abstract
  and reusable for any future BakryEmerySpace instance, combined
  with ε-regularization `g_ε := f² + ε`, FTC inequality, and DCT in
  `Instances/WorkInProgress/EuclideanEntropyDecay.lean`. The
  `bakryEmerySpace` instance was relocated to that file as part of
  the discharge.

| Axiom / Theorem | Reference | Status | Sources |
|---|---|---|---|
| `gaussian2D_orthogonal_invariance` | BGL §1.10.1 (rotation invariance of 2D standard Gaussian) | **Theorem** — proved via Codex (GPT-5.4): bridges `γ.prod γ` to `stdGaussian (WithLp 2 (ℝ × ℝ))` through the `EuclideanSpace ℝ (Fin 2) ≃ₗᵢ WithLp 2 (ℝ × ℝ)` isometry, applies Mathlib's `map_pi_eq_stdGaussian` to identify pushforward of `Measure.pi γ` with `stdGaussian (EuclideanSpace ℝ (Fin 2))`, then `stdGaussian_map` for the linear-isometric-equivalence invariance, finally unwraps via `WithLp.toLp / ofLp`. | (proved) |
| `ouSemigroup_preserves_IsCore` | BGL §2.7 (OU smoothing) | **Theorem** (decomposed 2026-05-12, then fully discharged): bounded parts via `ouSemigroup_preserves_bounds` + `hasDerivAt_ouSemigroup_C1` + `hasDerivAt_deriv_ouSemigroup`; C^∞ smoothing via Path C (Hermite IBP) in `EuclideanHermite.lean` — `ouSemigroup_contDiff_bounded` proves `(P_t f)^{(n)}(x) = (a/b)^n · ∫ H_n(y) · f(a·x + b·y) dγ` by induction + `hermite_ibp_gaussian` + `contDiff_of_differentiable_iteratedDeriv`. `IsCore` refactored from `ContDiff ℝ ⊤` (analytic in current Mathlib) to `ContDiff ℝ ∞` (C^∞). Theorem and its supporting `ouSemigroup_contDiff_bounded` are in `EuclideanHermite.lean`. | (proved, axiom-free) |
| `ouSemigroup_gradient_decay` | BGL Theorem 5.5.2 | **Theorem** — proved from new theorem `hasDerivAt_ouSemigroup` (Mehler derivative via Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`) + pointwise Jensen + Fubini/`ou_kernel_map` for γ-invariance. | (proved) |
| `ouSemigroup_l2_sq_hasDerivWithinAt` | BGL Proposition 4.7.1 | **Theorem** (2026-05-12) — fully discharged in `EuclideanStein.lean` via heat equation `hasDerivAt_t_ouSemigroup` + Gaussian Dirichlet form identity (Stein-based) + `hasDerivWithinAt_Ici_of_tendsto_deriv` for the `t = 0+` boundary, with DCT-based pointwise/integral continuity. | (proved) |
| `ouSemigroup_entropy_sq_decay_bound` | BGL Theorem 5.5.2 / §5.5 | **Theorem** (2026-05-12) — discharged via A1+A2 decomposition in `EuclideanEntropyDecay.lean`. Three atomic Bakry-Émery building-block axioms (Fisher info decay `I(P_t g) ≤ e^{-2t} I(g)`, de Bruijn `(d/dt) H(P_t g) = -I(P_t g)`, and its `t = 0+` boundary version) in `General/OUEntropyDecomposition.lean` are vetted Standard by `gemini-3.1-pro-preview` and reusable for any future BakryEmerySpace instance. The proof composes them via ε-regularization `g_ε := f² + ε` + FTC + DCT for `ε → 0` limit. | (proved); 3 focused atomic sub-axioms in `General/` |
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

### Instances/WorkInProgress/Euclidean.lean + EuclideanStein.lean (0 sorry's, 2 axioms)
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
by Codex). The last remaining `ouSemigroup_entropy_sq_decay_bound`
was discharged on 2026-05-12 via the A1+A2 decomposition. All three
initial atomic Bakry-Émery sub-axioms in
`MarkovSemigroups/General/OUEntropyDecomposition.lean` (A1 Fisher info
decay, A2 de Bruijn for `t > 0`, A2-boundary at `t = 0+`) were
proved the same day. The entire Gaussian1D + General/OU chain is
axiom-free; the discharge composes the three building blocks with
ε-regularization + FTC + DCT in
`Instances/WorkInProgress/EuclideanEntropyDecay.lean`.

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
