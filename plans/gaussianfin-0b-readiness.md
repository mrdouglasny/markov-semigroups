# GaussianFin readiness for Gross-discharge Phase 0b

**Status:** audit complete 2026-05-16. **Verdict: feasible, LOW RISK
— all 1D primitives are already proved; the four gaps (G1–G4) are
tensor-lift + a pointwise→strong-L² upgrade, NOT new analysis.** The
deeper grep refuted the initial worst case: the 1D `EuclideanStein`
layer already proves the linear OU heat equation **and** the Gaussian
IBP / generator↔energy identity. Gemini pass-3's "risk eliminated" is
essentially correct — for the stronger reason that the 1D linear
machinery is *proved*, not the finite-chaos hand-wave.

Audited: `MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean`
(2849 lines) + repo-wide grep.

## What GaussianFin already provides (reusable, sufficient as-is)

| Need | Status in `EuclideanFin.lean` |
|---|---|
| Measure + probability | `γFin n` (:34) + `IsProbabilityMeasure (γFin n)` instance (:37) ✓ — satisfies the `hμ` requirement |
| Semigroup (function level) | `ouSemigroupFin` (:83) |
| `S(0)=id`, semigroup law | `ouSemigroupFin_zero` (:1959), `_compose` (:1865) |
| L² contraction | `ouSemigroupFin_contraction` (:1650) |
| Symmetry | `ouSemigroupFin_selfAdjoint` (:1729) |
| Core preservation (`IsCore_semigroup`) | `ouSemigroupFin_preserves_IsCore` (:2771, axiom, Standard) ✓ |
| Dirichlet energy | `ouEnergyFin f g = ∫ ouGammaFin f g dγFin` (:968) |
| Bakry–Émery instance | `bakryEmerySpace n` (:2814) |
| Mehler **quadratic** derivative | `ouSemigroupFin_l2_sq_hasDerivWithinAt` (:2643, axiom, Standard) — `d/ds∫(P_sf)² = -2∫Γ` |

## Gaps blocking 0b (the actual deliverables)

**G1 — OU generator term: exists at 1D, lift it.** `L g = g″ − x·g′`
is **already used** at 1D in `EuclideanStein.lean` (docstrings :255,
:629, :696; consumed by `gaussian_dirichlet_form_bilinear` and
`hasDerivAt_t_ouSemigroup`) — just not exposed as a top-level `def`.
Deliverable: name it (`ouGenerator1D`) and tensor-lift to
`ouGeneratorFin` via the existing `secondPartial`/`partialDeriv`.
*Low effort.*

**G2 — Linear limit: open question RESOLVED (favorably).** The
*linear* heat equation **is proved at 1D**:
`EuclideanStein.lean:291 hasDerivAt_t_ouSemigroup` —
`HasDerivAt (fun τ => ouSemigroup τ f x) (L(P_τ f) x) t₀` for `t₀>0`
(BGL §2.7). So the earlier worst case ("only quadratic exists
anywhere") is **false**. What remains for `generator_compat`:
(i) the `t→0⁺` endpoint version (the project already has the
analogous `ouSemigroup_l2sq_hasDerivWithinAt_zero` pattern for the
quadratic case), and (ii) **pointwise → strong-L² upgrade**
(dominated convergence with the Mehler bound — a pattern the repo has
executed repeatedly for the entropy/quadratic discharges), then
tensor-lift to nD. *Genuine but routine deliverable; no novel
analysis, no finite-chaos hand-wave needed.*

**G3 — No `Lp ℝ 2 (γFin n)` CLM packaging.** `ouSemigroupFin` is
function-valued; Phase 0a needs a `ContractingSemigroup
(Lp ℝ 2 (γFin n))`. Must show it preserves `MemLp · 2 (γFin n)` and
descends to `Lp ℝ 2 (γFin n) →L[ℝ] Lp ℝ 2 (γFin n)` (transport
`_contraction`/`_compose`/`_zero` to the `Lp` quotient + strong
continuity). **Cross-repo note:** gaussian-hilbert already has
`ouSemigroupAct : … → Lp ℝ 2 (stdGaussianFin n)`, but
markov-semigroups must **not** depend on gaussian-hilbert (wrong
dependency direction) — build the packaging *here* and re-point
gaussian-hilbert's `ouSemigroupAct` at it (this is Gemini's "5-line
consumption swap" once it exists). *Moderate, plumbing-heavy.*

**G4 — Generator↔energy IBP: PROVED at 1D, lift it.** Confirmed:
`EuclideanStein.lean:703 gaussian_dirichlet_form_bilinear` +
`:566 gaussian_ibp_x_g_deriv_g` already prove the 1D Gaussian IBP /
generator↔energy identity (docstring :552 "Gaussian
integration-by-parts identity for the OU generator … energy
`E(g,g)=∫Γ dγ` into the generator-side"). Deliverable is the
**tensor-lift to nD γ-IBP**, not a fresh proof. *Routine (the project
already tensor-lifts 1D facts for the GaussianFin axioms).*

## Verdict & next step

**GaussianFin supports 0b — low risk, no novel analysis.** Every
primitive `generator_compat` needs is *already proved at 1D* in
`EuclideanStein.lean` (linear heat eqn `hasDerivAt_t_ouSemigroup`:291;
Gaussian IBP `gaussian_dirichlet_form_bilinear`:703;
`gaussian_ibp_x_g_deriv_g`:566) and the OU generator `L g = g″−x·g′`
is used there. The four deliverables are:

| Gap | Work | Effort |
|---|---|---|
| G1 generator term | name 1D `L`, tensor-lift to `ouGeneratorFin` | low |
| G2 strong-L² linear limit | `t→0⁺` endpoint + pointwise→L² (DCT, repo-standard pattern) + nD lift | moderate, routine |
| G3 `Lp ℝ 2 (γFin n)` CLM | descend function semigroup to `Lp` quotient (0a) | moderate, plumbing |
| G4 generator↔energy IBP | tensor-lift 1D `gaussian_dirichlet_form_bilinear` | moderate, routine |

None require Kato theory, spectral theory, or the finite-chaos
argument — all are tensor-lift + the well-trodden pointwise→strong-L²
DCT upgrade the repo already used for the entropy/quadratic
discharges. Estimate consistent with the Gross plan's 0b
(~150–300 lines) **plus** ~150–250 for G3/G4 lifts.

**Next:** none blocking — feed G1–G4 as the concrete 0b/0a Codex
work-items. The Gross plan's "0b make-or-break risk" is downgraded to
**low** accordingly.
