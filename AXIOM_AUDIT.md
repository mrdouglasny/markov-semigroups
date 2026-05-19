# Axiom Audit

*Centralized registry of every textbook axiom in `markov-semigroups`.
Each row records the axiom's literature reference, vetting verdict,
discharge plan (if any), and downstream consumers. Last refreshed:
2026-05-16.*

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

13 registered axioms total (11 → 12 on 2026-05-16 when the repo-wide
audit surfaced a previously-undocumented General axiom; → 13 same day
when the `feat/lp-carrier-stdGaussianFin-dirichletmarkov` merge
(`ba9a8de`) added the vetted general `gaussianOU_heatEquation_within_zero`
— see the "Gross-discharge: OU pointwise heat equation" section below).
Of these:
- **2 core hypercontractivity** axioms (Gross 1975) — abstract LSI ↔ HC
- **1 Stroock-Varopoulos** axiom — intermediate-step lemma for Gross,
  added 2026-05-13 as a vetted atomic textbook bridge
- **2 concentration / Poincaré** axioms (Herbst MGF + LSI ⇒ Poincaré)
- **2 Dobrushin-Zegarlinski** axioms — Otto-Reznikoff LSI + Helffer-Sjöstrand Cov
- **1 Matrix** axiom — diamagnetic resolvent inequality
  (`m_matrix_inverse_nonneg` relocated upstream to `SpectralPositivity`
  and re-exported as a theorem, so it is no longer counted here)
- **1 General/SchwartzConvolution** axiom —
  `contDiff_top_convolution_schwartzKernel` (Lieb–Loss Thm 2.16;
  Folland *Real Analysis* 2nd ed. Ch. 8 §2). Was **unregistered in
  this audit doc** until the 2026-05-16 sweep, but **is vetted** in
  its file docstring (`gemini-2.5-pro` Standard + `gemini-3.1-pro-preview`
  Likely correct, 2026-05-12, integrand revised per 3.1-pro). Rating
  **Likely correct**. No internal consumers (staged infrastructure;
  `ouSemigroup_contDiff` was discharged by a different route).
- **GaussianFin** multivariate Gaussian BE-instance primitives
  (merged to main 2026-05-13, commit `8ed9e52`), all
  gemini-3.1-pro-preview vetted **Standard**, all tensor-lift analogues
  of historical 1D primitives discharged in `Gaussian1D`:
  - `ouSemigroupFin_preserves_IsCore` (Mehler smoothing preservation,
    BGL §2.7.1 + §3) — **the one remaining declared GaussianFin axiom**.
  - `ouSemigroupFin_entropy_sq_decay_bound` (entropy decay for `f²`,
    BGL Thm 5.5.2) — **Workstream N1.c, 2026-05-19: no longer an
    axiom**; converted to a `theorem` with the telescoping route
    partially formalized. Four key supporting lemmas fully proved
    axiom-free (general 1D Boltzmann decay, macroscopic cancellation,
    per-coordinate step bound, energy bookkeeping); a single documented
    `sorry` remains for the telescoping assembly (T1 factorization +
    T2 orthogonal Fisher monotonicity + ε-limit). See the per-axiom
    row below.
  - `ouSemigroupFin_l2_sq_hasDerivWithinAt` (de Bruijn-style
    L²-derivative identity, BGL Prop 4.7.1) was **discharged
    2026-05-19** in commit `897b661` via the already-counted G2 axioms
    `gaussianFin_diffQuot_tendsto_Lp` and `gaussianFin_integrationByParts`
  Sub-stage N1 of the OU hypercontractivity discharge is complete;
  Stages N2 + N3 (gaussian-hilbert wire-in to discharge
  `ouSemigroupAct_eLpNorm_hypercontractive`) in progress.

**The entire Gaussian1D / OU chain is now axiom-free.** All BGL Ch. 2
and §5.5 facts have been discharged. The general-purpose
`MarkovSemigroups/General/OUEntropyDecomposition.lean` file is also
axiom-free. Discharges from 2026-05-12:
- **A1** (`ouSemigroup_fisher_info_decay`): Cauchy-Schwarz on the
  Mehler probability kernel.
- **A2-boundary** (`hasDerivWithinAt_entropy_ouSemigroup_zero`):
  derived from A2 interior + DCT-based continuity.
- **A2 interior** (`hasDerivAt_entropy_ouSemigroup`): proved via
  Stein-IBP-based formula for `(P_t g)''` + parametric DCT for the
  entropy integral + bilinear Dirichlet form identity
  (`gaussian_dirichlet_form_bilinear` in EuclideanStein.lean).

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

**Excluded by policy (not counted above):**
`Instances/WorkInProgress/EuclideanTests.lean` declares 4 local
scaffolding axioms (`gaussianResolvent`, `gaussianResolvent_ibp`,
`gaussianResolvent_ibp_integrable`, `gaussianBochner_identity`) used
only for a conditional in-file check. They are not textbook axioms,
are not consumed by the main tree, and live in `WorkInProgress`;
acknowledged here for exhaustiveness but deliberately not registered
as project axioms.

## Audit table

### Core: hypercontractivity / Gross duality / Stroock-Varopoulos

The three core axioms are now stated against the bundled
[`DirichletMarkovSemigroup`](MarkovSemigroups/Abstract/Hypercontractivity.lean)
structure after the 2026-05-13 **Lp-carrier refactor** documented in
[`docs/lp-carrier-refactor-design.md`](docs/lp-carrier-refactor-design.md).
This refactor changed the abstract semigroup carrier from the
mathematically flawed pointwise space `(X → ℝ) → (X → ℝ)` to bounded
operators on `L²(μ)`, `Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`, while keeping the
active axiom count unchanged at 11.

Post-refactor statement shape:
* time remains `t : ℝ` but all semigroup laws are restricted to `t ≥ 0`;
* the form-semigroup compatibility is the right-derivative statement
  `HasDerivWithinAt _ _ (Set.Ici 0) 0`;
* `IsHypercontractive` now quantifies over `f : Lp ℝ 2 μ` with an
  explicit `MemLp` hypothesis at exponent `p`;
* conservation is phrased as fixing any a.e.-constant-`1` `L²` element,
  and symmetry is the `L²` inner-product identity
  `⟪f, P_t g⟫ = ⟪P_t f, g⟫`.

| Axiom | File:Line | Reference | Rating | Vetting | Strategy / Plan | Consumers |
|---|---|---|---|---|---|---|
| `gross_lsi_implies_hypercontractive` | [`Abstract/Hypercontractivity.lean:261`](MarkovSemigroups/Abstract/Hypercontractivity.lean#L261) | Gross (1975) Amer. J. Math. 97, Theorem 1 | Standard | LP, SA, GR (gemini-3.1-pro-preview 2026-05-13: re-vet on the Lp-carrier refactor flagged a real soundness issue — the prior signature without `0 < ρ` would prove `False` because `SatisfiesLogSobolev D ρ` is trivially true for `ρ ≤ 0` while `IsHypercontractive` bakes in `0 < ρ`. Fixed in commit `78b2694` by adding `(hρ : 0 < ρ)` to the signature. Final 3.1-pro verdict on the fixed statement: **Standard / Likely correct.**) | Genuine textbook duality theorem on the Lp ℝ 2 μ →L Lp ℝ 2 μ carrier with the `0 < ρ` firewall. Full proof differentiates `‖P_t f‖_{L^{q(t)}}` along `q(t) = 1 + (p-1)e^{2ρt}` for `f : Lp ℝ 2 μ` ∩ `L^p`, applies LSI to `\|f\|^{q/2}` plus Stroock-Varopoulos. Estimated 2000-4000 lines / multi-week. **Discharge route vetted by Gemini deep-think 2026-05-16** (two analytical traps found in a naive abstract plan): recommended path is the corrected Route A — `hille-yosida` generator bridge (kills the right-derivative trap), weak-L² difference-quotient + convexity for the moving-exponent derivative (no pointwise differentiation under the integral), and **S–V as a theorem hypothesis, not proven abstractly** (it would need the Beurling–Deny representation — circular here). Full spec: [`plans/gross-discharge.md`](plans/gross-discharge.md). | **Live consumer (verified 2026-05-16, corrects earlier "no consumers"):** `gaussian-hilbert/GaussianHilbert/HypercontractivityFromBE.lean:204` applies it to a GaussianFin-built `DirichletMarkovSemigroup` to prove `ouSemigroupAct_eLpNorm_hypercontractive` (:314) → `bonami_nelson_chaos` → `polynomial_chaos_concentration` → **pphi2** `ChaosTailBridge` / `gaussian_hypercontractivity_continuum`. Also in-repo: `DirichletMarkovSemigroup.hypercontractive_of_logSobolev`, `gross_equivalence` (both now take `hρ`). Not consumed by `lgt`, `pphi2N`. |
| `gross_hypercontractive_implies_lsi` | [`Abstract/Hypercontractivity.lean:271`](MarkovSemigroups/Abstract/Hypercontractivity.lean#L271) | Gross (1975) Amer. J. Math. 97, Theorem 2 | Standard | LP, SA, GR (gemini-3.1-pro-preview 2026-05-13, re-vetted on the post-refactor `Lp ℝ 2 μ` carrier statement) | Reverse implication: differentiate the hypercontractive bound at `t = 0` with `p = 2`, `q = 2 + ε`, and pass `ε → 0`. Same effort scale as the forward direction; the refactor changes only the formal carrier, not the textbook content. | `DirichletMarkovSemigroup.logSobolev_of_hypercontractive`, `DirichletMarkovSemigroup.gross_equivalence` (same in-file-only consumer status) |
| `stroock_varopoulos` | [`Abstract/Hypercontractivity.lean:242`](MarkovSemigroups/Abstract/Hypercontractivity.lean#L242) | Stroock (1992), Varopoulos (1985); BGL Prop 1.7.1 / §1.7 | Standard | GR (gemini-3.1-pro-preview two-pass 2026-05-13: first pass `Needs Revision` flagging vacuous `f ≥ ε > 0` on infinite-measure spaces; revision to `f ≥ 0` applied; second pass `Standard`, confirming the post-refactor statement on `DirichletMarkovSemigroup`, the `p ≥ 2` power regularity at 0, the sharp constant `4(p-1)/p²`, edge cases `p = 2` and `f ≡ 0`, and the general symmetric-Markov scope) | Currently no internal consumers — added 2026-05-13 as the first intermediate-step atomic lemma toward a future Gross discharge. Discharge plan via pointwise convexity `(a-b)(a^{p-1}-b^{p-1}) ≥ (4(p-1)/p²)(a^{p/2}-b^{p/2})²`, integration against a symmetric Markov kernel, and the right-derivative compatibility field `energy_eq_deriv`. |

### Concentration / Poincaré

| Axiom | File:Line | Reference | Rating | Vetting | Strategy / Plan | Consumers |
|---|---|---|---|---|---|---|
| `herbst_mgf_bound` | [`Abstract/Concentration.lean:98`](../MarkovSemigroups/Abstract/Concentration.lean#L98) | BGL §5.4.1 (Herbst's lemma); Ledoux (2001) §1; Otto-Villani (2000) JFA 173 §3 | Standard | LP, SA | Three-line proof: differentiate `t ↦ log E[exp(tF)]` and apply LSI to the function `F + t·c`. Direct discharge would require the full LSI-derivative-of-MGF calculus on `Lp`. Estimated 1-2 weeks. | `lipschitz_concentration_of_lsi` and variants; `hasSubgaussianMGF_of_lsi` (proven Mathlib `HasSubgaussianMGF` bridge); `memLp_of_lsi`; the Zegarlinski concentration corollaries in `DobrushinZegarlinski/Concentration.lean` |
| `poincare_of_lsi` | [`Abstract/Concentration.lean:351`](../MarkovSemigroups/Abstract/Concentration.lean#L351) | BGL Proposition 5.1.3 (LSI ⇒ Poincaré with same constant) | Standard | LP, SA | Standard textbook implication: take `f = 1 + εg`, expand both sides of LSI to second order in ε. Estimated 3-5 days to formalize (Taylor expansion + careful bookkeeping). | `variance_lipschitz_le_of_lsi`, `variance_lipschitz_le_of_zegarlinski` |

### General/OU diffusion (axiom-free!)

[`MarkovSemigroups/General/OUEntropyDecomposition.lean`](../MarkovSemigroups/General/OUEntropyDecomposition.lean)
is now axiom-free. The three originally-axiomatized de Bruijn /
Fisher-decay facts have all been proved.

**Proved (2026-05-12):**
* `ouSemigroup_fisher_info_decay` (A1, BGL Proposition 5.5.2) —
  Cauchy-Schwarz on the Mehler probability kernel applied with
  `A := g'/√g, B := √g` gives `(P_t g'(x))² ≤ P_t((g')²/g)(x) · P_t g(x)`.
  Combined with the Mehler derivative formula `(P_t g)' = e^{-t} P_t g'`
  and divided by `P_t g ≥ ε > 0`, then integrated against γ +
  γ-invariance via `ou_kernel_map`. ~400 lines including a
  polynomial-discriminant Cauchy-Schwarz helper for `γ`.
* `hasDerivWithinAt_entropy_ouSemigroup_zero` (A2 at `t = 0+`) —
  derived from A2 (`t > 0` interior version) + DCT-based continuity
  of the entropy and Fisher info at `s = 0+` + Mathlib's
  `hasDerivWithinAt_Ici_of_tendsto_deriv`. ~330 lines.
* `hasDerivAt_entropy_ouSemigroup` (A2 interior, BGL §5.5
  de Bruijn identity for `t > 0`) — proved via a Stein-IBP-based
  formula for `(P_t g)''` (avoiding the need for `g''`), parametric
  DCT for the entropy integral, and the bilinear Dirichlet form
  identity (`gaussian_dirichlet_form_bilinear`). ~740 lines.

### General/SchwartzConvolution

**Unregistered in this audit doc** until the repo-wide sweep on
2026-05-16 — but **vetted in its file docstring**: `gemini-2.5-pro`
returned **Standard** and `gemini-3.1-pro-preview` returned **Likely
correct** (both 2026-05-12), the latter prompting a real revision
(integrand swapped to `K(x−y)·f y` so differentiation-under-the-
integral applies directly, since `f` is only measurable). It has no
internal consumers (staged infrastructure; the OU smoothing fact
`ouSemigroup_contDiff` was ultimately discharged by the Path-C
Hermite-IBP route, not via this axiom), so no proved theorem in the
repo transitively depends on it.

| Axiom | File:Line | Reference | Rating | Vetting | Strategy / Plan | Consumers |
|---|---|---|---|---|---|---|
| `contDiff_top_convolution_schwartzKernel` | [`General/SchwartzConvolution.lean:103`](../MarkovSemigroups/General/SchwartzConvolution.lean#L103) | Lieb–Loss *Analysis* (2nd ed.) Thm 2.16; Folland *Real Analysis* (2nd ed.) Ch. 8 §2; Reed–Simon I Thm V.4 | Likely correct | GR (gemini-2.5-pro 2026-05-12 **Standard**; gemini-3.1-pro-preview 2026-05-12 **Likely correct**, integrand revised `K(x−y)·f y` per 3.1-pro; hypotheses confirmed tight = Sobolev `W^{∞,1}×L^∞`) | For a `C^∞` kernel `K` with all iterated derivatives Lebesgue-integrable and bounded measurable `f`, `x ↦ ∫ K(x−y)·f(y) dy` is `C^∞`. Discharge (~200–400 lines): induction on differentiation order via Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, derivative falling on the smooth factor `K`. | None internal (staged; OU smoothing discharged via Path-C instead). |

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

### GaussianFin BGL Ch. 2 (multivariate Gaussian BE-instance work-in-progress)

The multivariate analogue of `Gaussian1D` on `(Fin n → ℝ, γ_n)` lives
in `Instances/WorkInProgress/EuclideanFin.lean` (merged to main
2026-05-13, commit `8ed9e52`). The complete BE-instance
`stdGaussianFin.bakryEmerySpace n : BakryEmerySpace (Fin n → ℝ)`
(EuclideanFin.lean:2814) has all 22 BE fields filled.
Before the 2026-05-19 discharge, `#print axioms
stdGaussianFin.bakryEmerySpace` closed over the three GaussianFin
axioms. The de Bruijn slot is now supplied by the proved theorem
`GaussianFin.ouSemigroupFin_l2_sq_hasDerivWithinAt`, whose verified
closure is the two G2 axioms
`gaussianFin_diffQuot_tendsto_Lp` / `gaussianFin_integrationByParts`
plus the still-active smoothing axiom
`ouSemigroupFin_preserves_IsCore` (and the standard Lean trio).

The supporting proved theorems (`ouSemigroupFin_zero/mean/contraction/
selfAdjoint/compose`, `ouSemigroupFin_gradient_decay`,
`ouSemigroupFin_ergodic`, `ouSemigroupFin_entropy_sq_ergodic`,
`ouSemigroupFin_l2_decay_bound`, `fderiv_ouSemigroupFin_eq`,
`contDiffOne_ouSemigroupFin`, kernel-pushforward infrastructure
`mixCLM/rotCLM/ou_kernel_map_fin/charFunDual_γFin`, the sectionwise
Stein identity, and the N1.4 derivative-bridge / N1.5 infrastructure)
land in the same file (~2850 lines, 0 sorries, originally 3 axioms
total; one of those is now discharged in `EuclideanFinBE.lean`).

The `IsCoreFin` definition was harmonized to `ContDiff ℝ ∞` (matching
`Gaussian1D.IsCore`) in commit `6bf390b` to enable the smoothing-axiom
vetting. The harmonization was build-stable; no upstream callers
required adaptation beyond the rename.

Phase 2 (`EuclideanFinLp.lean`, 2026-05-15) adds the concrete
`DirichletMarkovSemigroup` wrapper
`GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n` on the new
`Lp ℝ 2 (γFin n)` carrier introduced by the 2026-05-13
[Lp-carrier refactor](docs/lp-carrier-refactor-design.md). The
operator-valued semigroup laws are now proved theorems. Phase 2.5
removes the interim deviation from the Phase 2 brief: the bundle
field `energy_eq_deriv` is now obtained from the proved theorem
`ouSemigroupFin_l2_sq_hasDerivWithinAt`, and the dependency surfaces
through the already-counted G2 axioms rather than through a dedicated
GaussianFin de Bruijn axiom. This closes one active branch-local
axiom: **19 → 18**.

| Axiom | File:Line | Reference | Rating | Vetting | Strategy / Plan | Consumers |
|---|---|---|---|---|---|---|
| `ouSemigroupFin_l2_sq_hasDerivWithinAt` | [`Instances/WorkInProgress/EuclideanFinBE.lean:446`](../MarkovSemigroups/Instances/WorkInProgress/EuclideanFinBE.lean#L446) | Bakry-Gentil-Ledoux *Analysis and Geometry of Markov Diffusion Operators* (Springer 2014), Proposition 4.7.1 | **DISCHARGED 2026-05-19** | DT, GR (gemini-2.5-pro deep-think 2026-05-13 + gemini-3.1-pro-preview re-vet 2026-05-13; both passes confirmed type-correctness, hypothesis sufficiency, non-vacuity, correct strength, and discharge plan feasibility; 3.1-pro added the nuance that `IsCoreFin` closure under the semigroup is not needed for the statement because Lean integrals are total and `ouSemigroupFin_preserves_core_bounds` already gives the required integrability). Discharged by Codex in commit `897b661`. | Multivariate de Bruijn-style derivative identity `d/ds \|_{s=t} ∫ (P_s f)² dγ_n = -2 · ∫ Γ_n(P_t f, P_t f) dγ_n`. **Discharged 2026-05-19 via the G2 axioms** `gaussianFin_diffQuot_tendsto_Lp` and `gaussianFin_integrationByParts`: identify `∫ (P_s f)^2` with the `L²` pairing `⟪[f], P_{2s}[f]⟫`, differentiate the pairing using the strong-`L²` difference-quotient theorem, then convert the derivative to `-2·E(P_t f, P_t f)` via the multivariate Gaussian integration-by-parts identity. Verified `#print axioms GaussianFin.ouSemigroupFin_l2_sq_hasDerivWithinAt = [propext, Classical.choice, Quot.sound, GaussianFin.gaussianFin_diffQuot_tendsto_Lp, GaussianFin.gaussianFin_integrationByParts, GaussianFin.ouSemigroupFin_preserves_IsCore]`. | Consumed by `ouSemigroupFin_l2_decay_bound` (derived theorem), the multivariate `BakryEmerySpace (Fin n → ℝ)` wrap, and `GaussianFin.stdGaussianFin_dirichletMarkovSemigroup` via `energy_eq_deriv`. Downstream consumer in gaussian-hilbert: `ouSemigroupAct_eLpNorm_hypercontractive` discharge via Gross-LSI-implies-HC route. |
| `ouSemigroupFin_preserves_IsCore` | [`Instances/WorkInProgress/EuclideanFin.lean`](../MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean) | Bakry-Gentil-Ledoux §2.7.1 + §3 (heat-kernel smoothing); 1D analogue historically axiomatized at `Euclidean.lean:488` and proved in commit `890e022` (Path C Hermite IBP) | **DISCHARGED 2026-05-19** | GR (gemini-3.1-pro-preview 2026-05-13: **Standard** post-harmonization to `ContDiff ℝ ∞`, recommended the Cameron–Martin kernel route and confirmed no mixed-derivative control is needed). **Discharged 2026-05-19 (Workstream N1.b)** by Claude via the vetted Cameron–Martin kernel route: `cameronMartin1D` (1D Girsanov shift, no integrability hypotheses) → `gaussianFin_cameronMartin` (multivariate tensorization by induction on `n` via `integral_γFin_succAbove`) → `ouSemigroupFin_eq_cmKernel` (move all spatial dependence onto a smooth Gaussian weight) → `contDiff_laplaceFamily` (C^∞ of `x ↦ ∫ F(w)·exp(α⟨x,w⟩) dγ` by `contDiff_succ_iff_fderiv` strong induction, deliberately avoiding `iteratedFDeriv`) → `contDiff_ouSemigroupFin_of_bounded`. The `IsCoreFin` bounds reuse `ouSemigroupFin_preserves_core_bounds`; the section-wise 2nd-derivative bound is transferred via `secondPartial_eq_section_deriv_of_contDiff`. No new axioms, no sorries. Verified `#print axioms GaussianFin.ouSemigroupFin_preserves_IsCore = [propext, Classical.choice, Quot.sound]`. | The `IsCore_semigroup` field of the BE-instance wrap `stdGaussianFin.bakryEmerySpace`. Downstream: same as for the other two GaussianFin axioms — eventual gaussian-hilbert `ouSemigroupAct_eLpNorm_hypercontractive` discharge. |
| `ouSemigroupFin_entropy_sq_decay_bound` | [`Instances/WorkInProgress/EuclideanFin.lean`](../MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean) (now a `theorem`) | Bakry-Gentil-Ledoux Theorem 5.5.2 / BGL §5.5 (1D analogue was historically axiomatized at `Euclidean.lean:943` and proved in commit `1b3f797` via A1+A2 decomposition) | **DISCHARGED 2026-05-19** | GR (gemini-3.1-pro-preview 2026-05-13 statement vet **Standard**; deep-think 2026-05-19 confirmed the **telescoping route**) | **Workstream N1.c, 2026-05-19:** `axiom` converted to a fully proved `theorem` via the telescoping route. **Fully proved supporting lemmas (all axiom-free):** (a) `Gaussian1D.boltzmannEntropy_ouSemigroup_decay_le` — general 1D Boltzmann-entropy decay (FTC assembly of A1+A2), in `EuclideanEntropyDecay.lean`; (b) `entropy_sub_eq_boltzmann_sub` — macroscopic cancellation; (c) `boltzmannEntropyFin_ouCoord_step_le` — per-coordinate step bound; (d) `sum_fisherInfoFinCoord_sq_add_const_le` — energy bookkeeping. ε→0 DCT tail via `boltzmannSubFin_le_of_perEps` + `ouSemigroupFin_sq_add_const`. **T1** factorization (`ouCoordSet` induction with `ouCoordSet_empty`/`ouCoordSet_univ`/composition step via `integral_γFin_succAbove_swap`) and **T2** orthogonal Fisher monotonicity (`I_k(ouCoord j t h) ≤ I_k h` for `j≠k`, regularity via the merged N1.b Cameron–Martin C^∞ infrastructure) completed; telescoped to the main bound. No new axioms, no sorries. Verified `#print axioms GaussianFin.ouSemigroupFin_entropy_sq_decay_bound = [propext, Classical.choice, Quot.sound]`. | The `semigroup_entropy_sq_decay_bound` field of the BE-instance wrap. Downstream: same as for the other two GaussianFin axioms — eventual gaussian-hilbert `ouSemigroupAct_eLpNorm_hypercontractive` discharge. |

### Gross-discharge: OU general textbook axioms

Added 2026-05-16/17 as the strategic unblock of the Gross-discharge
G2 chain (`plans/gross-discharge.md`): the **three** deep analytic
cruxes (Codex stalled twice on the first, twice on the third) are
promoted to **general, Mathlib-native** textbook axioms — stated with
`fderiv`/`Pi.single`/`Real.exp`/`MeasureTheory.Measure.pi`/
`ProbabilityTheory.gaussianReal`/`MemLp`/`Lp` (the third
operator-parameterized over `P` with a generic Mehler a.e.
characterization), **no project definitions** — so they are reusable
and vetting-amenable. The project lemmas
(`hasDerivWithinAt_t_ouSemigroupFin_zero`,
`ouGeneratorFin_ibp_integral`, `ouSemigroupFinLp_diffQuot_tendsto`)
are **proved theorems** discharged from these axioms by unfolding the
thin project defns / instantiating `P:=ouSemigroupFinLp` (`#print
axioms` per lemma = the 3 Lean built-ins + the one relevant axiom; no
`sorryAx`, no other custom axioms). Net for the Gross chain: the
*abstract* `gross_lsi_implies_hypercontractive` axiom leaves pphi2's
live path, replaced by concrete general Standard-vetted axioms (each
with a recorded discharge route) — conscious abstract→concrete-vetted
trade, user-approved 2026-05-17.

**Live critical path (verified `#print axioms`
`GaussianFin.generatorCompat_stdGaussianFin`, 2026-05-17):** exactly
**two** custom axioms — `gaussianFin_diffQuot_tendsto_Lp` and
`gaussianFin_integrationByParts` (+ the 3 Lean built-ins; no
`sorryAx`). The DCT-upgrade axiom delivers the strong-`L²` limit
directly, so `gaussianOU_heatEquation_within_zero` (and its derived
`hasDerivWithinAt_t_ouSemigroupFin_zero`) is **no longer on
`generatorCompat`'s critical path** — it stays as vetted, reusable
textbook infrastructure (the pointwise endpoint form) but is
subsumed there by the third axiom. *(Branch summary count above is the older
branch-side narrative; the canonical reconciled count lives on `main`
post-merge `ba9a8de` — these add to it.)*

| Axiom | File:Line | Reference | Rating | Vetting | Strategy / Plan | Consumers |
|---|---|---|---|---|---|---|
| `gaussianOU_heatEquation_within_zero` | [`Instances/WorkInProgress/EuclideanGeneratorLimit.lean`](../MarkovSemigroups/Instances/WorkInProgress/EuclideanGeneratorLimit.lean) | Bakry-Gentil-Ledoux *Analysis and Geometry of Markov Diffusion Operators* (2014) §2.7 (OU/heat semigroup + generator); Mehler's formula | **Standard / Likely correct** | GR (gemini-3-pro-preview, 2026-05-16 — deep-think model unavailable, used the GR-tier model as for prior project axiom vettings). Confirmed: (a) well-formed (`fderiv`+`Pi.single`=∂ᵢ, nested=∂ᵢ², `Measure.pi gaussianReal 0 1`=std Gaussian, `HasDerivWithinAt … Ici 0`=right-deriv); (b) matches BGL §2.7 — OU SDE `dX=−X dt+√2 dW`, transition law `e^{−t}X₀+√(1−e^{−2t})Y`, generator `Δ−x·∇`; Mehler constants self-consistent with variance 1 (no rescaling); (c) non-vacuous (`sin x₁+cos x₂` etc., M=1, substantive); (d) **pure-second-partial bounds sufficient** — via Itô/Dynkin `Pₜf−f=∫₀ᵗPₛ(Lf)ds` the martingale term vanishes in expectation so only `|∇f|`,`|Δf|` bounded needed; **no mixed-partial / third-derivative / growth hypotheses required**; right-derivative endpoint form correct. No revision. | Right endpoint `t=0⁺` of the Mehler-semigroup time derivative: for `C^∞` `f` with bounded `f, ∂ᵢf, ∂ᵢ²f`, `HasDerivWithinAt (t ↦ ∫ f(e^{-t}x+√(1-e^{-2t})y) d(⊗ⁿN(0,1))) (Δf(x)-x·∇f(x)) (Ici 0) 0`. Discharge route (recorded on the project lemma docstring): parametric differentiation under the integral with the Pi-valued chain rule through the Mehler shift + the scaling identity `∂ᵢ²(Pₜf)=e^{-2t}Pₜ(∂ᵢ²f)` via `section_secondDeriv*`. | `GaussianFin.hasDerivWithinAt_t_ouSemigroupFin_zero` (proved from it). **No longer on the live `generatorCompat` critical path** (2026-05-17): the DCT-upgrade axiom `gaussianFin_diffQuot_tendsto_Lp` delivers the strong-`L²` limit directly, subsuming the pointwise endpoint here. Retained as vetted, reusable textbook infrastructure. |
| `gaussianFin_integrationByParts` | [`Instances/WorkInProgress/EuclideanGeneratorLp.lean`](../MarkovSemigroups/Instances/WorkInProgress/EuclideanGeneratorLp.lean) | Bakry-Gentil-Ledoux (2014) §1.6/§2.7 (the OU generator's Dirichlet form: `∫ g·Lf = −E(g,f)`, `E(g,f)=∫⟨∇g,∇f⟩`); Gaussian integration by parts (Stein) | **Standard / Likely correct** | GR (gemini-3-pro-preview, 2026-05-16; deep-think unavailable, GR-tier as for prior vettings). Confirmed: (a) well-formed; (b) sign/normalization **exact** — `∇φ/φ=−x` for `N(0,I)` organically yields the `−x·∇f` drift with coefficient 1, `∫ g·(Δf−x·∇f)dγ=−∫Σᵢ∂ᵢg·∂ᵢf dγ`, no factor-2/variance rescale; (c) non-vacuous (`f=g=sin x₀` ⇒ both sides `−∫cos²(x₀)dγ<0`); (d) pure-second-partial bounds + boundedness sufficient — Gaussian moments absorb the linear-growth `g·(x·∇f)` term, IBP is coordinatewise-Fubini so no mixed/third partials; `hg`'s pure-2nd-partial bound is mathematically superfluous-but-harmless (kept for core-class symmetry, safely droppable if generalized). No revision. | `GaussianFin.ouGeneratorFin_ibp_integral` (proved from it) → `ouGeneratorFin_ibp` → `GeneratorCompat` → Gross-discharge G2; also `GaussianFin.ouSemigroupFin_l2_sq_hasDerivWithinAt` (discharged 2026-05-19 via the pairing/energy route). |
| `gaussianFin_diffQuot_tendsto_Lp` | [`Instances/WorkInProgress/EuclideanGeneratorLimit.lean`](../MarkovSemigroups/Instances/WorkInProgress/EuclideanGeneratorLimit.lean) | Bakry-Gentil-Ledoux (2014) §2.7/§1.6 (OU strongly continuous on `L²(γ)`; on the smooth core `t⁻¹(Pₜf−f) → Lf` strongly in `L²`); `Lf=Δf−x·∇f` | **Standard / Likely correct** | GR (gemini-3-pro-preview, 2026-05-17; deep-think unavailable, GR-tier as for the prior two Gross-discharge axioms). Confirmed: (a) well-formed, normalization exact for variance-1 (`∇log ρ=−x`, generator `Δ−x·∇`, Mehler constants self-consistent, no factor-2/variance rescale; `𝓝[>]0`=right limit, `Lp ℝ 2 μ`=norm topology); (b) matches BGL §2.7 `L²` strong convergence on the core; (c) non-vacuous (`f=Σ sin xᵢ`; the genuine OU `Lp` semigroup satisfies `hP`, so the parametric `P`-characterization is consistent, not contradictory); (d) hypotheses **sufficient** — value+first+unmixed-second bounds give `f, Lf∈L²(μ)` (`Lf` ≤ linear growth, Gaussian integrates all polynomials) and the strong `L²` (norm) limit follows from `Pₜf−f=∫₀ᵗPₛ(Lf)ds`; **no mixed partials / third derivatives / growth hypotheses required**; one-sided `t→0⁺` form appropriate. No revision. | Operator-parameterized DCT upgrade of the pointwise heat equation: for `C^∞` `f` with bounded `f, ∂ᵢf, ∂ᵢ²f` and any `P` with the generic Mehler a.e. action `hP`, `Tendsto (t ↦ t⁻¹•(P t [f] − [f])) (𝓝[>]0) (𝓝 [Δf−x·∇f])` in `Lp ℝ 2 (⊗ⁿN(0,1))`. Discharge route (recorded on the project lemma docstring): pointwise heat equation `gaussianOU_heatEquation_within_zero` + segment-wide uniform-`L²` dominator (the precise Codex 2026-05-16 obstruction) ⇒ DCT. | `GaussianFin.ouSemigroupFinLp_diffQuot_tendsto` (proved from it, instantiating `P:=ouSemigroupFinLp`, `hP:=ouSemigroupFinLp_coeFn_ae`) → `GeneratorCompat` → Gross-discharge G2; also `GaussianFin.ouSemigroupFin_l2_sq_hasDerivWithinAt` (discharged 2026-05-19 via the pairing derivative). |

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
