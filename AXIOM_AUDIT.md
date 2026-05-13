# Axiom Audit

*Centralized registry of every textbook axiom in `markov-semigroups`.
Each row records the axiom's literature reference, vetting verdict,
discharge plan (if any), and downstream consumers. Last refreshed:
2026-05-10.*

## Purpose

In this project, an **axiom** is a *vetted provable theorem with a vetted
discharge plan* — not a fundamental unprovable assumption. Each axiom
listed below is:

1. A standard textbook fact, with explicit literature citation.
2. Reviewed for type correctness, hypothesis sufficiency, and
   non-vacuity (typically by a Gemini deep-think pass and/or a
   literature cross-check).
3. Accompanied by a concrete plan to discharge it into a Lean theorem
   (inline in the row, or linked to a dedicated discharge-plan doc).

We use the `axiom` keyword as a *staging point* — it lets the project
proceed to use a result before its full Lean proof is assembled, while
keeping the trust boundary explicit and discharge progress trackable.
The goal is for every entry below to eventually become a proved
theorem.

Format and conventions for this audit doc:
`~/.claude/AXIOM_AUDIT_FORMAT.md`.

## Conventions

**Vetting source codes** (per
[research-dev `AXIOM_MANAGEMENT.md`](https://github.com/mrdouglasny/research-dev/blob/main/library/lean/AXIOM_MANAGEMENT.md)):
- **DT** — Gemini deep-think (slow, high-reasoning vet pass)
- **GR** — Gemini chat review (`gemini-3-pro-preview`)
- **CX** — Codex (independent re-derivation / cross-check)
- **LP** — literature proof with explicit page reference
- **SA** — self-audit (author cross-checked against textbook by hand)
- **PR** — peer review (external mathematician)

**Rating scale:**
- **Standard** — well-established textbook fact with multiple independent references
- **Likely correct** — checked, consistent with textbook(s) but not externally vetted
- **Needs review** — placeholder; statement plausible but not yet vetted
- **Placeholder** — known to need replacement; statement may be approximate (e.g., infrastructure-stub)
- **Flagged** — concern raised; do not consume downstream until resolved

## Summary

10 axioms total. Of these:
- **2 core hypercontractivity** axioms (Gross 1975) — abstract LSI ↔ HC
- **2 concentration / Poincaré** axioms (Herbst MGF + LSI ⇒ Poincaré)
- **3 General/OU diffusion** axioms — atomic Bakry-Émery building
  blocks in `MarkovSemigroups/General/OUEntropyDecomposition.lean`:
  `ouSemigroup_fisher_info_decay` (A1: `I(P_t g) ≤ e^{-2t} I(g)`),
  `hasDerivAt_entropy_ouSemigroup` (A2: de Bruijn identity), and
  `hasDerivWithinAt_entropy_ouSemigroup_zero` (A2 at `t = 0+`).
  These replaced the former broad `ouSemigroup_entropy_sq_decay_bound`
  axiom (2026-05-12); they're abstract enough to be reusable for any
  future BakryEmerySpace instance, individually vetted (Standard verdict
  by gemini-3.1-pro-preview), and individually dischargeable. The
  Gaussian1D concrete instance is now itself **axiom-free**.
- **2 Dobrushin-Zegarlinski** axioms — Otto-Reznikoff LSI + Helffer-Sjöstrand Cov
- **1 Matrix** axiom — diamagnetic resolvent inequality

**Discharged axioms** (Gaussian1D, was 9 + 2 atomic; now 0 atomic axioms
in the concrete instance):
* All 9 original Gaussian1D axioms (`ouSemigroup_*`) — see "Reduced to
  theorems" sections below for the discharge details.
* The 2 atomic Mehler-kernel axioms (`ouSemigroup_contDiff` via Path C
  Hermite IBP, `ouSemigroup_entropy_sq_decay_bound` via Path A1+A2
  decomposition).

The Wiener-chaos / multivariate-Hermite cluster (3 OU placeholder
axioms + 1 external `polynomial_dense_L2_of_subGaussian`, plus the
proved theorems `hermiteMulti_dense`, `wienerChaos_isHilbertSum`,
`bonami_nelson_*`, `polynomial_chaos_concentration`) **moved to
[gaussian-hilbert](https://github.com/mrdouglasny/gaussian-hilbert)**
on 2026-05-10. See that repo for the current home and audit.
## Audit table

### Core: hypercontractivity / Gross duality

| Axiom | File:Line | Reference | Rating | Vetting | Strategy / Plan | Consumers |
|---|---|---|---|---|---|---|
| `gross_lsi_implies_hypercontractive` | [`Abstract/Hypercontractivity.lean:100`](../MarkovSemigroups/Abstract/Hypercontractivity.lean#L100) | Gross (1975) Amer. J. Math. 97, Theorem 1 | Standard | LP, SA | Genuine textbook duality theorem; full proof is the eigenvalue argument on `Γ`-energy + entropy. Multi-week to discharge in Lean (functional inequality calculus on abstract Markov semigroups). | `MarkovSemigroup.hypercontractive_of_logSobolev`, `MarkovSemigroup.gross_equivalence`; load-bearing for the Bonami-Nelson step in `polynomial_chaos_concentration` once OU placeholders are discharged via the BE+Gross route ([`ou-mehler-discharge-plan.md`](ou-mehler-discharge-plan.md)) |
| `gross_hypercontractive_implies_lsi` | [`Abstract/Hypercontractivity.lean:108`](../MarkovSemigroups/Abstract/Hypercontractivity.lean#L108) | Gross (1975) Amer. J. Math. 97, Theorem 2 | Standard | LP, SA | Reverse implication of Gross. Same effort estimate as the forward direction. | `MarkovSemigroup.logSobolev_of_hypercontractive`, `MarkovSemigroup.gross_equivalence` |

### Concentration / Poincaré

| Axiom | File:Line | Reference | Rating | Vetting | Strategy / Plan | Consumers |
|---|---|---|---|---|---|---|
| `herbst_mgf_bound` | [`Abstract/Concentration.lean:98`](../MarkovSemigroups/Abstract/Concentration.lean#L98) | BGL §5.4.1 (Herbst's lemma); Ledoux (2001) §1; Otto-Villani (2000) JFA 173 §3 | Standard | LP, SA | Three-line proof: differentiate `t ↦ log E[exp(tF)]` and apply LSI to the function `F + t·c`. Direct discharge would require the full LSI-derivative-of-MGF calculus on `Lp`. Estimated 1-2 weeks. | `lipschitz_concentration_of_lsi` and variants; `hasSubgaussianMGF_of_lsi` (proven Mathlib `HasSubgaussianMGF` bridge); `memLp_of_lsi`; the Zegarlinski concentration corollaries in `DobrushinZegarlinski/Concentration.lean` |
| `poincare_of_lsi` | [`Abstract/Concentration.lean:351`](../MarkovSemigroups/Abstract/Concentration.lean#L351) | BGL Proposition 5.1.3 (LSI ⇒ Poincaré with same constant) | Standard | LP, SA | Standard textbook implication: take `f = 1 + εg`, expand both sides of LSI to second order in ε. Estimated 3-5 days to formalize (Taylor expansion + careful bookkeeping). | `variance_lipschitz_le_of_lsi`, `variance_lipschitz_le_of_zegarlinski` |

### General/OU diffusion (3 atomic axioms — Bakry-Émery building blocks)

These three axioms live in
[`MarkovSemigroups/General/OUEntropyDecomposition.lean`](../MarkovSemigroups/General/OUEntropyDecomposition.lean).
Together they discharge the former `ouSemigroup_entropy_sq_decay_bound`
axiom (BGL Theorem 5.5.2) — see
`Instances/WorkInProgress/EuclideanEntropyDecay.lean` for the proof
`ouSemigroup_entropy_sq_decay_bound_proved`.

| Axiom | Reference | Rating | Vetting | Strategy / Plan | Consumers |
|---|---|---|---|---|---|
| `ouSemigroup_fisher_info_decay` | BGL Proposition 5.5.2 (`I(P_t g) ≤ e^{-2t} I(g)`); Bakry-Émery 1985 | Standard | GR (gemini-3.1-pro-preview 2026-05-12) | Cauchy-Schwarz on the Mehler probability kernel + `(P_t g)' = e^{-t} P_t g'` (already proved) + γ-invariance. Expected ~150-250 lines. | `Gaussian1D.bakryEmerySpace` (via `EuclideanEntropyDecay.lean`) |
| `hasDerivAt_entropy_ouSemigroup` | BGL §5.5 (de Bruijn identity for `t > 0`) | Standard | GR (gemini-3.1-pro-preview 2026-05-12) | Bilinear Dirichlet form identity (1D IBP from Gaussian-density ODE) + parametric differentiation. Expected ~300-500 lines. | `Gaussian1D.bakryEmerySpace` (via `EuclideanEntropyDecay.lean`) |
| `hasDerivWithinAt_entropy_ouSemigroup_zero` | BGL §5.5 (de Bruijn at `t = 0+`) | Standard | GR (gemini-3.1-pro-preview 2026-05-12) | FTC + DCT: `lim_{t↘0} I(P_t g) = I(g)`. Provable from the t > 0 version + continuity. Expected ~80-150 lines. | `Gaussian1D.bakryEmerySpace` (via `EuclideanEntropyDecay.lean`) |

### Gaussian1D BGL Ch. 2 (0 axioms — instance is axiom-free)

All originally-axiomatized Mehler-kernel-level facts are now proved.
The two atomic textbook bridges remaining (`ouSemigroup_contDiff` and
`ouSemigroup_entropy_sq_decay_bound`) have been **discharged** via
Path C (Hermite IBP) and the A1+A2 decomposition above, respectively.
See "Reduced to theorems" below.

**Six originally axiomatized 1D facts were reduced to theorems**:
- `ouSemigroup_l2_decay_bound` (FTC + gradient decay)
- `ouSemigroup_ergodic` (double DCT on Mehler integrand)
- `ouSemigroup_entropy_sq_ergodic` (DCT for `s log s` + compactness)
- `ouSemigroup_compose` (Gaussian convolution via `gaussianReal_add_gaussianReal_of_indepFun`)
- `gaussian2D_orthogonal_invariance` (proved by Codex via `stdGaussian_map` + `map_pi_eq_stdGaussian` through the `EuclideanSpace ℝ (Fin 2) ≃ₗᵢ WithLp 2 (ℝ × ℝ)` isometry)
- `ouSemigroup_gradient_decay` (2026-05-12) — proved via the new theorem
  `hasDerivAt_ouSemigroup` (Mehler-derivative formula via Mathlib's
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`) + Jensen +
  γ-invariance (Fubini + `ou_kernel_map`). Additionally,
  `stein_identity_standard` (Stein's identity for the standard Gaussian,
  BGL §1.15) is now also proved, paving the way for further discharges.
- `ouSemigroup_preserves_IsCore` (2026-05-12) — DECOMPOSED, then FULLY
  DISCHARGED. The bounded parts proved via `ouSemigroup_preserves_bounds`
  (using `hasDerivAt_ouSemigroup_C1` weakened-hypothesis Mehler-derivative
  and `hasDerivAt_deriv_ouSemigroup` second-order formula). Also proved as
  cleanup: the **Gaussian Dirichlet form identity**
  `∫ g · L g dγ = -∫ (g')² dγ` for `IsCore g`
  (`gaussian_dirichlet_form_identity`, BGL §1.6), via Stein applied to
  `h := g · g'` — bridges `BakryEmerySpace` energy and the L²(γ)
  generator inner product. The `C^∞` smoothing residue is now also
  discharged (see `ouSemigroup_contDiff` entry below).
- `ouSemigroup_l2_sq_hasDerivWithinAt` (2026-05-12) — FULLY DISCHARGED.
  The `t > 0` case proved via `hasDerivAt_l2sq_ouSemigroup_pos`
  (heat equation `hasDerivAt_t_ouSemigroup` + Mathlib's parametric
  derivative + Gaussian Dirichlet form identity via Stein). The `t = 0`
  boundary case (initially isolated as the residue axiom
  `ouSemigroup_l2sq_hasDerivWithinAt_zero`) is now also proved
  (`ouSemigroup_l2sq_hasDerivWithinAt_zero` is now a theorem in
  `EuclideanStein.lean`) via Mathlib's `hasDerivWithinAt_Ici_of_tendsto_deriv`
  combined with DCT-based pointwise/integral continuity of `P_s f` and
  `(P_s f')` at `s = 0+`. All proofs live in `EuclideanStein.lean`.
- `ouSemigroup_contDiff` (2026-05-12) — FULLY DISCHARGED via the
  **Hermite IBP path** (Path C) in
  `Instances/WorkInProgress/EuclideanHermite.lean`. The discharge
  establishes the closed-form iterated-derivative identity
  `(P_t f)^{(n)}(x) = (a/b)^n · ∫ y, H_n(y) · f(a·x + b·y) ∂γ`
  by induction on `n`, combining parametric integral differentiation
  with `hermite_ibp_gaussian` (the n-th-order Stein identity:
  `∫ H_n · F' dγ = ∫ H_{n+1} · F dγ`). The C^∞ conclusion then follows
  via `contDiff_of_differentiable_iteratedDeriv`. As part of this
  discharge, `IsCore` was refactored to use `ContDiff ℝ ∞` (C^∞)
  rather than `ContDiff ℝ ⊤` (analyticity / ω) since in current
  Mathlib `⊤ : WithTop ℕ∞ = ω`, and the project's intent throughout
  has been C^∞ smoothing. The new theorem
  `ouSemigroup_contDiff_bounded` and the relocated
  `ouSemigroup_preserves_IsCore` are in `EuclideanHermite.lean`.
- `ouSemigroup_entropy_sq_decay_bound` (2026-05-12) — FULLY DISCHARGED
  via decomposition into 3 atomic axioms in
  `MarkovSemigroups/General/OUEntropyDecomposition.lean`:
  `ouSemigroup_fisher_info_decay` (A1), `hasDerivAt_entropy_ouSemigroup`
  (A2), and `hasDerivWithinAt_entropy_ouSemigroup_zero` (A2-boundary).
  The proof (`ouSemigroup_entropy_sq_decay_bound_proved` in
  `Instances/WorkInProgress/EuclideanEntropyDecay.lean`, ~550 lines)
  composes these via the ε-regularization `g_ε := f² + ε`, FTC inequality,
  and DCT for the `ε → 0` limit. The `bakryEmerySpace` instance was
  relocated to `EuclideanEntropyDecay.lean` (from `EuclideanStein.lean`)
  so its `semigroup_entropy_sq_decay_bound` field can call the proved
  theorem directly. Net: 1 broad Gaussian1D axiom replaced by 3
  focused atomic axioms in `General/` (reusable for any future
  BakryEmerySpace instance); Gaussian1D itself is axiom-free.

### Dobrushin-Zegarlinski

| Axiom | File:Line | Reference | Rating | Vetting | Strategy / Plan | Consumers |
|---|---|---|---|---|---|---|
| `zegarlinski_lsi_inequality` | [`DobrushinZegarlinski/GlobalLSI.lean:234`](../MarkovSemigroups/DobrushinZegarlinski/GlobalLSI.lean#L234) | Otto-Reznikoff (2007) J. Funct. Anal. 243 Theorem 1; Zegarlinski (1996) CMP 175; BGL §5.7.5 | Standard | LP | Continuous-spin generalization of the Dobrushin-Stroock-Zegarlinski-Bertini-Cancrini-Cesi LSI theorem: uniform local LSI + weak gradient coupling `J/c ≤ α < 1` ⟹ global LSI with constant `c·(1-α)`. The proof in literature is multi-page entropy iteration; full Lean discharge is estimated multi-month. | `global_lsi_of_zegarlinski` (`DobrushinZegarlinski/GlobalLSI.lean`); declared for downstream consumers (pphi2N strict thermodynamic-limit route) |
| `cov_entrywise_bound_of_zegarlinski` | [`DobrushinZegarlinski/EntrywiseCovariance.lean:146`](../MarkovSemigroups/DobrushinZegarlinski/EntrywiseCovariance.lean#L146) | Helffer-Sjöstrand (1994) J. Stat. Phys. 74; Naddaf-Spencer (1997) CMP 183; BGL §4.5 | Standard | LP | Entrywise covariance bound `|Cov(σ_x, σ_y)| ≤ M⁻¹(x,y)` for `M = Hess V` under uniform local LSI + Zegarlinski. Proof: Helffer-Sjöstrand operator-positivity argument. Multi-month to formalize (requires fairly heavy machinery for the spectral decomposition of the Hessian). | `cov_entrywise_decay_nn` (`DobrushinZegarlinski/EntrywiseCovariance.lean`, the proven exponential-decay corollary `\|Cov(σ_x, σ_y)\| ≤ α^{d(x,y)} / (c·(1-α))` for nearest-neighbor finite-range `V`); declared for pphi2N's `HSData.AdmitsThimbleLocal` |

**DZ-layer audit (verified `#print axioms` 2026-05-01):** the proven
content of `DobrushinZegarlinski/` — `AbstractInfluenceMatrix` theory,
single-site decomposition `entropy_decomposition_single_site`,
DLR-at-Bochner-integral identity `integral_siteSmoothing`, distance-aware
Neumann bounds (`iterate_dist_zero`, `neumann_series_nn_dist_bound`),
and the exponential-decay corollary `cov_entrywise_decay_nn` — is
**axiom-free** (depends only on the three Lean built-ins). Only the two
textbook axioms above are pulled in when the LSI / Cov bridge theorems
themselves are invoked.

### Matrix

| Axiom | File:Line | Reference | Rating | Vetting | Strategy / Plan | Consumers |
|---|---|---|---|---|---|---|
| `diamagnetic_resolvent` | [`Matrix/Diamagnetic.lean:57`](../MarkovSemigroups/Matrix/Diamagnetic.lean#L57) | Diamagnetic inequality (Simon, *Functional Integration and Quantum Physics*, Ch. 22); assembles 5 separate steps in the literature | Standard | LP, SA | `\|(M+iV)⁻¹(x,y)\| ≤ M⁻¹(x,y)` entrywise, where `M` is a Z-matrix and `V` is real-diagonal. Five-step assembly: (i) `(M+iV)⁻¹ = ∫₀^∞ exp(-t(M+iV)) dt`, (ii) Trotter-Lie product formula for `exp(-t(M+iV))`, (iii) `\|exp(-tM_off + tD_real)\| ≤ exp(-tM_off + tD_real)` (entrywise) for diagonally-perturbed Z-matrices, (iv) bound the Trotter slices entrywise, (v) take `n → ∞`. Estimated 3-4 weeks to formalize; (ii) and (iv) are now proved (Trotter formula in `Matrix/Trotter.lean`), so 3 of 5 steps remain. | None internally — declared for external callers (lgt's mass-gap / pphi2 propagator-bound consumers) |

**Previously axiomatized but now proved as theorems:**
- `m_matrix_inverse_nonneg` (now in `Matrix/LaplaceTransform.lean`, derived from heat-kernel positivity + Laplace transform)
- `exp_entryNonneg_of_entryNonneg` (now in `Matrix/HeatKernel.lean`, via Metzler shift)
- `trotter_product_formula` (now in `Matrix/Trotter.lean`)

## Open vetting items

These haven't been independently vetted yet — would be valuable to send
through `mcp__gemini__deep_think_gemini` and/or `codex:codex-rescue`
when the budget allows:

1. **`herbst_mgf_bound`.** Literature review only (LP). A deep-think
   pass would confirm the statement matches Herbst-style assumptions
   (no hidden `IsCore`-flavored constraints).
2. **`zegarlinski_lsi_inequality`.** Multi-page proof in the literature
   with several non-trivial sufficient-condition flavors (Otto-Reznikoff
   vs original Zegarlinski). Worth a careful side-by-side check that
   the formalized statement matches the strongest published version
   (and that the sufficient-condition `J/c ≤ α < 1` is exactly the one
   we use in `LocalLSI.lean` / `InteractionMatrix.lean`).
3. **`diamagnetic_resolvent`.** The 5-step assembly is informal — a
   deep-think pass on whether the statement is the right packaging
   (vs splitting into 5 axioms or 1 cleaner statement) would help.

## Maintenance

When adding or removing an axiom:
1. Update this file (the audit table row).
2. Update `README.md`'s axiom-count line + tables in sync.
3. If the discharge plan changes, update the `docs/<plan>.md` entry and
   re-link from the row's "Strategy / Plan" column.
4. After any new vetting pass, update the row's `Vetting` column.

When *discharging* an axiom (turning it into a proved theorem):
1. Move the row to the "Previously axiomatized but now proved" list at
   the bottom of the relevant section.
2. Update README's axiom count + audit/consumers tables.
3. Update consumers' `#print axioms` in commit messages so the audit
   trail is visible.
