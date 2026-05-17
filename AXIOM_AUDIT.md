# Axiom Audit

*Centralized registry of every textbook axiom in `markov-semigroups`.
Each row records the axiom's literature reference, vetting verdict,
discharge plan (if any), and downstream consumers. Last refreshed:
2026-05-13.*

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

11 axioms total. Of these:
- **2 core hypercontractivity** axioms (Gross 1975) — abstract LSI ↔ HC
- **1 Stroock-Varopoulos** axiom — intermediate-step lemma for Gross,
  added 2026-05-13 as a vetted atomic textbook bridge
- **2 concentration / Poincaré** axioms (Herbst MGF + LSI ⇒ Poincaré)
- **2 Dobrushin-Zegarlinski** axioms — Otto-Reznikoff LSI + Helffer-Sjöstrand Cov
- **1 Matrix** axiom — diamagnetic resolvent inequality
- **3 GaussianFin** axioms (merged to main 2026-05-13, commit `8ed9e52`)
  — multivariate Gaussian BE-instance primitives, all gemini-3.1-pro-preview
  vetted **Standard**, all tensor-lift analogues of historical 1D primitives
  that were already discharged in `Gaussian1D`:
  - `ouSemigroupFin_l2_sq_hasDerivWithinAt` (de Bruijn-style L²-derivative
    identity, BGL Prop 4.7.1)
  - `ouSemigroupFin_preserves_IsCore` (Mehler smoothing preservation,
    BGL §2.7.1 + §3)
  - `ouSemigroupFin_entropy_sq_decay_bound` (entropy decay for `f²`,
    BGL Thm 5.5.2)
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
| `gross_lsi_implies_hypercontractive` | [`Abstract/Hypercontractivity.lean:261`](MarkovSemigroups/Abstract/Hypercontractivity.lean#L261) | Gross (1975) Amer. J. Math. 97, Theorem 1 | Standard | LP, SA, GR (gemini-3.1-pro-preview 2026-05-13: re-vet on the Lp-carrier refactor flagged a real soundness issue — the prior signature without `0 < ρ` would prove `False` because `SatisfiesLogSobolev D ρ` is trivially true for `ρ ≤ 0` while `IsHypercontractive` bakes in `0 < ρ`. Fixed in commit `78b2694` by adding `(hρ : 0 < ρ)` to the signature. Final 3.1-pro verdict on the fixed statement: **Standard / Likely correct.**) | Genuine textbook duality theorem on the Lp ℝ 2 μ →L Lp ℝ 2 μ carrier with the `0 < ρ` firewall. Full proof differentiates `‖P_t f‖_{L^{q(t)}}` along `q(t) = 1 + (p-1)e^{2ρt}` for `f : Lp ℝ 2 μ` ∩ `L^p`, applies LSI to `\|f\|^{q/2}` plus Stroock-Varopoulos. Estimated 2000-4000 lines / multi-week to discharge directly. | `DirichletMarkovSemigroup.hypercontractive_of_logSobolev` (now also takes `hρ`), `DirichletMarkovSemigroup.gross_equivalence` (now also takes `hρ`). No downstream consumers in this repo or in `lgt`, `pphi2`, `pphi2N`, `gaussian-hilbert`. |
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
`#print axioms stdGaussianFin.bakryEmerySpace` shows the closure is
exactly `[propext, Classical.choice, Quot.sound,
ouSemigroupFin_l2_sq_hasDerivWithinAt, ouSemigroupFin_preserves_IsCore,
ouSemigroupFin_entropy_sq_decay_bound]` — no spurious dependencies.

The supporting proved theorems (`ouSemigroupFin_zero/mean/contraction/
selfAdjoint/compose`, `ouSemigroupFin_gradient_decay`,
`ouSemigroupFin_ergodic`, `ouSemigroupFin_entropy_sq_ergodic`,
`ouSemigroupFin_l2_decay_bound`, `fderiv_ouSemigroupFin_eq`,
`contDiffOne_ouSemigroupFin`, kernel-pushforward infrastructure
`mixCLM/rotCLM/ou_kernel_map_fin/charFunDual_γFin`, the sectionwise
Stein identity, and the N1.4 derivative-bridge / N1.5 infrastructure)
land in the same file (~2850 lines, 0 sorries, 3 axioms total).

The `IsCoreFin` definition was harmonized to `ContDiff ℝ ∞` (matching
`Gaussian1D.IsCore`) in commit `6bf390b` to enable the smoothing-axiom
vetting. The harmonization was build-stable; no upstream callers
required adaptation beyond the rename.

Phase 2 (`EuclideanFinLp.lean`, 2026-05-15) adds the concrete
`DirichletMarkovSemigroup` wrapper
`GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n` on the new
`Lp ℝ 2 (γFin n)` carrier introduced by the 2026-05-13
[Lp-carrier refactor](docs/lp-carrier-refactor-design.md). The
operator-valued semigroup laws are now proved theorems. The one
intentional interim deviation from the Phase 2 brief is that the
bundle field `energy_eq_deriv` is currently obtained by polarization
from the pre-existing multivariate axiom
`ouSemigroupFin_l2_sq_hasDerivWithinAt`, so that axiom is now
temporarily load-bearing at the public bundle boundary. Replacing that
with the direct fresh-Fubini lift of the discharged 1D boundary
derivative identity is tracked as follow-up cleanup; the active axiom
count remains **11**.

| Axiom | File:Line | Reference | Rating | Vetting | Strategy / Plan | Consumers |
|---|---|---|---|---|---|---|
| `ouSemigroupFin_l2_sq_hasDerivWithinAt` | [`Instances/WorkInProgress/EuclideanFin.lean:2643`](../MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean#L2643) | Bakry-Gentil-Ledoux *Analysis and Geometry of Markov Diffusion Operators* (Springer 2014), Proposition 4.7.1 | Standard | DT, GR (gemini-2.5-pro deep-think 2026-05-13 + gemini-3.1-pro-preview re-vet 2026-05-13; both passes confirmed type-correctness, hypothesis sufficiency, non-vacuity, correct strength, and discharge plan feasibility; 3.1-pro added the nuance that `IsCoreFin` closure under the semigroup is not needed for the statement because Lean integrals are total and `ouSemigroupFin_preserves_core_bounds` already gives the required integrability) | Multivariate de Bruijn-style derivative identity `d/ds \|_{s=t} ∫ (P_s f)² dγ_n = -2 · ∫ Γ_n(P_t f, P_t f) dγ_n`. Discharge plan: Fubini lift through `ouSemigroupFin_insertNth_eq` and `integral_γFin_succAbove`; differentiate per-coordinate via the proved 1D fact `Gaussian1D.bakryEmerySpace.semigroup_l2_sq_hasDerivWithinAt`; recombine by linearity of derivative. The strategy is the tensor lift through Fubini of the already-discharged 1D theorem (1D was historically axiomatized in `Euclidean.lean:684` and proved in commit `00cd52b` via the A2 de Bruijn decomposition + boundary `t = 0` discharge). | Consumed by `ouSemigroupFin_l2_decay_bound` (derived theorem in `EuclideanFin.lean`), the multivariate `BakryEmerySpace (Fin n → ℝ)` wrap (N1.6), and temporarily by `GaussianFin.stdGaussianFin_dirichletMarkovSemigroup` (`EuclideanFinLp.lean`) via the current polarization proof of `energy_eq_deriv`. Downstream consumer in gaussian-hilbert: `ouSemigroupAct_eLpNorm_hypercontractive` discharge via Gross-LSI-implies-HC route. |
| `ouSemigroupFin_preserves_IsCore` | [`Instances/WorkInProgress/EuclideanFin.lean:2771`](../MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean#L2771) | Bakry-Gentil-Ledoux §2.7.1 + §3 (heat-kernel smoothing); 1D analogue historically axiomatized at `Euclidean.lean:488` and proved in commit `890e022` (Path C Hermite IBP) | Standard | GR (gemini-3.1-pro-preview 2026-05-13: initial verdict **Flagged** on `ContDiff ⊤` (real-analytic) vs `ContDiff ∞` (C^∞) mismatch; codex harmonized `IsCoreFin` to `ContDiff ℝ ∞` in commit `6bf390b`, after which verdict upgrades to **Standard**. Mathematical note: codex's "missing mixed-derivative control" intuition was incorrect — pure-partial bounds suffice because the multivariate Mehler semigroup is a tensor product (`∂_i² P_t f = e^{-2t} · P_t (∂_i² f)`); mixed partials are needed for `Γ_2` later, not for `IsCoreFin` preservation.) | The OU semigroup preserves the multivariate test-function core `IsCoreFin`. Discharge route per 3.1-pro: change of variables on the Mehler integral, `(P_t f)(x) = ∫ f(z) · ρ_t(x, z) dz` with `ρ_t(x, z)` the shifted Gaussian density (C^∞ in `x`); apply `ContDiff.integral` to push derivatives onto the kernel rather than `f`. Deliberately avoids the multi-index Hermite-IBP route (which is notoriously hard in Lean4 due to `iteratedFDeriv`'s symmetric-multilinear formulation). | The `IsCore_semigroup` field of the BE-instance wrap `stdGaussianFin.bakryEmerySpace` (`EuclideanFin.lean:2824`). Downstream: same as for the other two GaussianFin axioms — eventual gaussian-hilbert `ouSemigroupAct_eLpNorm_hypercontractive` discharge. |
| `ouSemigroupFin_entropy_sq_decay_bound` | [`Instances/WorkInProgress/EuclideanFin.lean:2799`](../MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean#L2799) | Bakry-Gentil-Ledoux Theorem 5.5.2 / BGL §5.5 (1D analogue was historically axiomatized at `Euclidean.lean:943` and proved in commit `1b3f797` via A1+A2 decomposition) | Standard | GR (gemini-3.1-pro-preview 2026-05-13: statement `Ent_{γ_n}(f²) − Ent_{γ_n}(P_t(f²)) ≤ 2(1 − e^{−2t}) · ouEnergyFin f f` confirmed with correct sign and factor; the factor `2(1 − e^{−2t})` arises from integrating the Fisher-info decay `d/ds Ent(P_s f²) ≥ −4 e^{−2s} E(f, f)` from 0 to t; `IsCoreFin` sufficient because `f²` is bounded so `f² log f²` is γ_n-integrable; ε-regularization handles `f² = 0`) | Multivariate entropy decay for `f²` under the OU semigroup. **Corrected discharge plan** (3.1-pro flagged): the naive `Ent_{γ_n}(g) = E_{γ_¬i}[Ent_{γ_i}(g(·, x_¬i))]` chain rule is *not* an equality — the macroscopic term `Ent_{¬i}(E_i[g])` doesn't vanish. The correct route is a **telescoping argument**: peel one Mehler factor `P_t^{(k)}` at a time and use γ_k-invariance `E_k[P_t^{(k)} h] = E_k[h]` to make the macroscopic terms cancel across the *difference* `Ent(h) − Ent(P_t^{(k)} h)`, then telescope over k and sum the 1D bounds. Per-step uses the proved 1D `Gaussian1D.bakryEmerySpace.semigroup_entropy_sq_decay_bound`. | The `semigroup_entropy_sq_decay_bound` field of the BE-instance wrap. Downstream: same as for the other two GaussianFin axioms — eventual gaussian-hilbert `ouSemigroupAct_eLpNorm_hypercontractive` discharge. |

### Gross-discharge: OU pointwise heat equation (general)

Added 2026-05-16 as the strategic unblock of the Gross-discharge G2
chain (`plans/gross-discharge.md`): the deep parametric-PDE crux
`hasDerivWithinAt_t_ouSemigroupFin_zero` (Codex stalled on it twice)
is promoted to a **general, Mathlib-native** textbook axiom — stated
with `fderiv`/`Pi.single`/`Real.exp`/`MeasureTheory.Measure.pi`/
`ProbabilityTheory.gaussianReal`, **no project definitions** — so it
is reusable and vetting-amenable. The project lemma
`hasDerivWithinAt_t_ouSemigroupFin_zero` is now a **proved theorem**
discharged from this axiom by unfolding the thin project defns
(`#print axioms` = the 3 Lean built-ins + this axiom only; no
`sorryAx`, no other custom axioms).

| Axiom | File:Line | Reference | Rating | Vetting | Strategy / Plan | Consumers |
|---|---|---|---|---|---|---|
| `gaussianOU_heatEquation_within_zero` | [`Instances/WorkInProgress/EuclideanGeneratorLimit.lean`](../MarkovSemigroups/Instances/WorkInProgress/EuclideanGeneratorLimit.lean) | Bakry-Gentil-Ledoux *Analysis and Geometry of Markov Diffusion Operators* (2014) §2.7 (OU/heat semigroup + generator); Mehler's formula | **Needs review (NOT VERIFIED)** | — (none yet; **Gemini deep-think vetting pending** — recommended next step per the axiom protocol: type-correctness, hypothesis sufficiency, non-vacuity, BGL §2.7 strength) | Right endpoint `t=0⁺` of the Mehler-semigroup time derivative: for `C^∞` `f` with bounded `f, ∂ᵢf, ∂ᵢ²f`, `HasDerivWithinAt (t ↦ ∫ f(e^{-t}x+√(1-e^{-2t})y) d(⊗ⁿN(0,1))) (Δf(x)-x·∇f(x)) (Ici 0) 0`. Discharge route (recorded on the project lemma docstring): parametric differentiation under the integral with the Pi-valued chain rule through the Mehler shift + the scaling identity `∂ᵢ²(Pₜf)=e^{-2t}Pₜ(∂ᵢ²f)` via `section_secondDeriv*`. | `GaussianFin.hasDerivWithinAt_t_ouSemigroupFin_zero` (proved from it); transitively the planned `ouSemigroupFinLp_diffQuot_tendsto` → `GeneratorCompat` → Gross-discharge G2. |

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
