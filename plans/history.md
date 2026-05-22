# History of completed plans

Chronological log of completed substantial work in `markov-semigroups`.
Each entry records:

- **Date** completed.
- **Title / goal**.
- **Commits** delivering the work (or PR links).
- **Resources** (time, lines of code, subagents used, vetting calls).
- **Outcome** (what landed, deviations from original plan if any).
- **Lessons learned** (patterns worth repeating, traps to avoid).

When a planning doc in `plans/` is completed, also move the doc to
`plans/archive/` and add an entry here.

---

## Index

| Date | Title | Net axiom count Δ |
|---|---|---|
| 2026-05-21 | [Gross LSI ⇒ HC abstract spine — `GrossODE.lean` sorry-free](#2026-05-21-gross-lsi--hc-abstract-spine-complete) | 0 (no new axioms; +1 vetted predicate `CoreLpL2Approx`, S–V relaxed `2≤q`→`1<q`) |
| 2026-05-13 | [Lp-carrier refactor of abstract `MarkovSemigroup`](#2026-05-13-lp-carrier-refactor-of-abstract-markovsemigroup) | 0 (correctness fix; `hρ : 0 < ρ` firewall added) |
| 2026-05-13 | [Stage N1 — multivariate Gaussian BE instance merged](#2026-05-13-stage-n1--multivariate-gaussian-be-instance-merged) | +3 placeholder GaussianFin axioms (all vetted Standard) |
| 2026-05-13 | [Bundled `DirichletMarkovSemigroup` refactor + S–V axiom](#2026-05-13-bundled-dirichletmarkovsemigroup-refactor--stroockvaropoulos-axiom) | +1 (S–V axiom added, vetted Standard) |
| 2026-05-12 | [A2 (interior de Bruijn) discharge](#2026-05-12-a2-de-bruijn-interior-discharge) | −1 |
| 2026-05-12 | [A2-boundary discharge from A2 interior](#2026-05-12-a2-boundary-discharge) | −1 |
| 2026-05-12 | [A1 (Fisher info gradient decay) discharge](#2026-05-12-a1-fisher-info-gradient-decay-discharge) | −1 |
| 2026-05-12 | [`ouSemigroup_entropy_sq_decay_bound` discharge via A1+A2](#2026-05-12-ousemigroup_entropy_sq_decay_bound-discharge) | net +2 (1 broad → 3 focused, then proven over next 2 entries) |
| 2026-05-12 | [Path C Hermite IBP discharge of `ouSemigroup_contDiff`](#2026-05-12-path-c-hermite-ibp-discharge-of-ousemigroup_contdiff) | −1 |
| 2026-05-12 | [`IsCore` refactor `ContDiff ⊤ → ContDiff ∞`](#2026-05-12-iscore-refactor-contdiff--contdiff-) | 0 (correctness fix) |

---

## 2026-05-21: Gross LSI ⇒ HC abstract spine complete

**Goal:** finish the hypothesis-parameterised Gross theorem
`gross_lsi_implies_hypercontractive_of_hypotheses` in
`Abstract/GrossODE.lean` — i.e. prove P2 (`grossPow_hasDerivWithinAt`),
P3 (`grossLogNorm_deriv_nonpos`), and the general-`f` reduction to
`IsHypercontractive`, leaving only the per-instance discharge (W) for
gaussian-hilbert.

**Commits** (branch `gross-grossPow-hasDerivWithinAt-body`): helper
`af8e881` (`abs_integral_rpow_mul_log_sub_le`); `h_second` `a075063`;
energy→`orbitCoreRep` refactor `458d2f3`; `h_energy` `509773e`; P3
`92ed88a`; SV-relaxation vetting `e64a7fe`; core+positive bound
`df46789`; `CoreLpApprox` vetting `7b1b22a`; final theorem `82e1602`.

**Resources:** one extended session. ~4 deep-think vetting calls
(energy a.e.-invariance ×2, S–V `q>1` relaxation, `CoreLpL2Approx`).
Several hundred lines net in `GrossODE.lean` + `Hypercontractivity.lean`.
codex:rescue attempted on `h_second`, made no progress; done by hand.

**Outcome:**
* `GrossODE.lean` is **sorry-free**; `#print axioms
  gross_lsi_implies_hypercontractive_of_hypotheses =
  [propext, Classical.choice, Quot.sound]`.
* P2 via `h_second` (MVT-in-τ + integral-Lipschitz helper +
  `squeeze_zero_norm'`) ⊕ `h_energy` (generator pairing `P_s Af = Ag'`
  by strong-`L²` limit uniqueness).
* P3 via LSI on `u^{q/2}` + Stroock–Varopoulos (generator-paired) ⇒
  `div_nonpos_iff`.
* Final reduction: core+positive bound `eLpNorm_orbit_le_of_core_pos`
  (antitone `Λ` + `eLpNorm↔(∫·^r)^{1/r}` + `L^q ≤ L^{q(t)}`) extended to
  general `f` via the new `CoreLpL2Approx` (WLOG `f≥0`, `L²`-approx ⇒
  a.e.-orbit subsequence, Fatou).
* No new axioms. Added one per-instance hypothesis predicate
  `CoreLpL2Approx`; relaxed `StroockVaropoulos._hq` `2 ≤ q → 1 < q`.
* The four predicates `CoreSemigroupInvariant` / `GeneratorCompat` /
  `StroockVaropoulos` / `CoreLpL2Approx` are discharged per-instance (W).

**Lessons learned:**
* **The abstract `D.energy` is a carré-du-champ (gradient) form → NOT
  a.e.-invariant.** An unconditional `energy_ae_congr` field is *false*
  for gradient energies (rejected after two vettings). The fix: evaluate
  energy at a smooth core representative `orbitCoreRep` (from
  `CoreSemigroupInvariant`), never at the `Lp`-coe rep. Dropped the
  redundant `|·|` on the energy power so it matches the
  `IsCore_rpow_pos_strict` core rep exactly.
* **Vet hypothesis-relaxations before committing.** S–V holds for all
  `q > 1` (equality for diffusions); `2 ≤ q` would have forced the HC
  theorem to `p ≥ 2`. Deep-think confirmed `1 < q` is sound + necessary.
* **Decouple the semigroup from density hypotheses.** `CoreLpL2Approx`
  asks only for `L^p`+`L²` density of core (no `P_t`); the abstract glue
  recovers a.e.-orbit convergence from `L²`-contraction +
  `tendstoInMeasure_of_tendsto_Lp` (Gemini's refinement).
* **`coreToL2 hf` is not syntactically `(IsCore_memLp hf).toLp f`** —
  route a.e. facts through a folded `have hcoe : (coreToL2 hf : X→ℝ) =ᵐ f`
  before `rw`/`simp`, else pattern matching fails.

## 2026-05-13: Lp-carrier refactor of abstract `MarkovSemigroup`

**Goal:** fix a soundness flaw in the post-bundle `MarkovSemigroup` /
`DirichletMarkovSemigroup` structure in `Abstract/Hypercontractivity.lean`.
Move the abstract semigroup carrier from `(X → ℝ) → (X → ℝ)` (pointwise
functions) to bounded operators on `L²(μ)`,
`Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`.

**Commits:**
* `c133b8a` — design doc `docs/lp-carrier-refactor-design.md`.
* `65f0364` — core refactor: move carrier to `Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`,
  rewrite all `MarkovSemigroup` fields, regenerate
  `DirichletMarkovSemigroup` bundle.
* `78b2694` — add `hρ : 0 < ρ` to `gross_lsi_implies_hypercontractive`
  to firewall a `ρ ≤ 0` vacuity trap (LSI is trivially true for
  non-positive `ρ`, but `IsHypercontractive` bakes in `0 < ρ`).
* `1f81794` — audit row update recording the `hρ` fix.
* `e1e2011` — merge to `main`.

**Resources:**
* Time: ~1 day of design + execution.
* Lines: ~250 net change in `Hypercontractivity.lean`; ~250 lines new
  design doc.
* Gemini vetting: `gemini-3.1-pro-preview` two passes.
  * Pass 1: identified the Bochner junk-value flaw in the pointwise
    carrier ("if `f` is signed and non-absolutely-integrable, the
    unconditional field `P_semigroup` can fail because one side hits
    the junk value `0` while the other side conditionally converges
    to a non-zero value").
  * Pass 2 (on refactor shape): "commit to this refactor".
  * Third pass after `hρ` fix: confirmed `Standard / Likely correct`.
* No subagents needed (single-author refactor).

**Outcome:**
* `MarkovSemigroup.P` now `: ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)` — junk
  values impossible on `L²` equivalence classes.
* `P_zero`, `P_semigroup`, `P_strong_cont`, `P_contraction`,
  `P_conservation`, `P_positivity`, `P_symmetric` all reformulated
  on the Lp carrier.
* `DirichletMarkovSemigroup` gains a new field `IsCore_memLp`
  (every core function lies in `L²(μ)`), and `energy_eq_deriv` is
  reformulated using a let-binding `coreToL2 : ∀ {h : X → ℝ}, IsCore h → Lp ℝ 2 μ`.
* `gross_lsi_implies_hypercontractive` signature acquires
  `(hρ : 0 < ρ)` between `(ρ : ℝ)` and `(h_lsi : ...)`.
* Active axiom count unchanged at 11 (the refactor is a soundness
  fix, not an axiom-count fix).
* Downstream impact: zero — no other module or downstream project
  imports `Abstract/Hypercontractivity.lean`.

**Lessons learned:**
* **Lp carriers eliminate whole classes of Bochner-trap bugs.** When
  in doubt between pointwise and Lp carriers for a semigroup on a
  measure space, prefer Lp. Junk-value pathologies on non-integrable
  inputs simply don't exist on `L²` equivalence classes.
* **Vetting catches subtle vacuity traps.** The `ρ ≤ 0` firewall was
  found by Gemini on the third pass — without it, the axiom would
  have allowed deriving `False` via `IsHypercontractive` baking in
  `0 < ρ` while `SatisfiesLogSobolev` does not.
* **Design docs upfront pay off** even for "abstract structure"
  refactors. The design doc was vetted before any code was written,
  saving the cost of a second iteration after misshape detection.

---

## 2026-05-13: Stage N1 — multivariate Gaussian BE instance merged

**Goal:** build `stdGaussianFin.bakryEmerySpace n : BakryEmerySpace (Fin n → ℝ)`,
the concrete multivariate-Gaussian Bakry-Émery instance, as the
foundation for the gaussian-hilbert hypercontractivity discharge.

**Commits (Codex branch `feat/bakry-emery-multivariate-gaussian`):**
* `28962ea` — sectionwise OU derivative lemmas on `Fin` Gaussian.
* `1711914` — rebase adaptation for Section core proof.
* `b23ed6d`, `92cff22`, `ea6b35e`, `895e691`, `6bf390b`, `c71b260` —
  N1.4–N1.6 infrastructure checkpoints (kernel-pushforward, harmonized
  `IsCoreFin`, ergodic field, `ouSemigroupFin_l2_decay_bound`).
* `b97f7d9` — add N1.5/N1.6 vetted axioms and BakryEmerySpace wrap.
* `ab1f454` — audit doc for the merged N1 GaussianFin axioms.
* `6a23582` — archive Stage N detailed plan + codex N1 brief.
* `43793af`, `ed88be1` — README/status axiom-count bumps 8 → 11.
* `8ed9e52` — merge to `main`.

**Resources:**
* Time: ~7–10 active days (codex; ran concurrently with the bundled
  refactor + Lp-carrier work on `main`).
* Lines: ~2850 in
  `MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean`
  (0 sorries, 3 placeholder axioms).
* Subagent: Codex (independent worktree, with periodic checkpoints).
* Gemini vetting: `gemini-3.1-pro-preview` — `Standard` verdict on
  each of the 3 placeholder axioms (all tensor-lift analogues of
  historical 1D primitives that are now discharged in `Gaussian1D`).

**Outcome:**
* `stdGaussianFin.bakryEmerySpace n : BakryEmerySpace (Fin n → ℝ)`
  is an instance, with curvature `ρ = 1` (tensorizes from 1D).
* 3 placeholder axioms remain, all `gemini-3.1-pro-preview` vetted
  **Standard**, all tensor-lift analogues of already-proved 1D
  primitives:
  * `ouSemigroupFin_l2_sq_hasDerivWithinAt` (BGL Prop 4.7.1
    multivariate version).
  * `ouSemigroupFin_preserves_IsCore` (BGL §2.7.1 + §3 multivariate
    Mehler smoothing).
  * `ouSemigroupFin_entropy_sq_decay_bound` (BGL Thm 5.5.2
    multivariate version).
* Sub-stage N1 of the OU hypercontractivity discharge is **complete**;
  stages N2 + N3 (gaussian-hilbert wire-in to discharge
  `ouSemigroupAct_eLpNorm_hypercontractive`) are in progress.
* Project axiom count: 8 → 11.

**Lessons learned:**
* **Concrete-instance route beats generic-tensorization route for
  abstract classes lacking kernel data.** The original Stage N plan
  called for a generic `BakryEmerySpace.pi` tensorization lemma, but
  the abstract class exposes the semigroup as a bare operator with no
  kernel representation. Codex correctly identified this blocker and
  pivoted to the concrete instance.
* **Tensor-lift placeholder axioms are a clean staging strategy.** The
  3 axioms are *not* new mathematics — they are the multivariate
  versions of facts already discharged in 1D. Future N1.5/N1.6 work
  will discharge them by tensor-lift from `Gaussian1D` primitives.
  In the interim, the multivariate instance is usable downstream.
* **Long codex branches need rebases planned.** The N1 branch
  rebased onto the bundled Gross refactor twice (commits `1711794`
  and a follow-up); each rebase was ~6 lines but had to be done
  promptly to avoid drift.

---

## 2026-05-13: Bundled `DirichletMarkovSemigroup` refactor + Stroock–Varopoulos axiom

**Goal:** fix soundness issues in the abstract Gross axioms (`Abstract/Hypercontractivity.lean`) and add the Stroock–Varopoulos intermediate-step lemma toward a future Gross discharge.

**Commits:**
* `986d98a..6e4ad85` — `SemigroupGeneratesDirichletForm` side-hypothesis fix (intermediate state).
* `371780b` — Bundled `DirichletMarkovSemigroup extends MarkovSemigroup` structure refactor.
* `613c0f7` — Add `stroock_varopoulos` axiom.
* `46aaf7a` — Doc updates (8 total axioms).
* `d9b6a7a` — Upgrade S–V vetting verdict to Standard after second-pass vetting.

**Resources:**
* Time: ~1 day across the bundled refactor + S–V addition.
* Lines: ~210 (Hypercontractivity.lean refactor) + ~80 (S–V axiom & docstring).
* Gemini vetting:
  * 3.1-pro first pass on the side-hypothesis fix: identified four formal soundness issues (two-sided `HasDerivAt` causes Stone-collapse; Bochner-trap in `IsHypercontractive`; missing conservation/positivity/symmetry).
  * 3.1-pro first pass on S–V: "Needs Revision" — flagged vacuous `f ≥ ε > 0` on infinite-measure spaces.
  * 3.1-pro second pass on revised S–V: "Standard".

**Outcome:**
* `MarkovSemigroup` structure strengthened: `t ≥ 0` guards, `P_conservation`, `P_positivity`, `P_symmetric`, `eLpNorm` contraction.
* New `DirichletMarkovSemigroup` extends `MarkovSemigroup` with form data + `energy_eq_deriv` (right-derivative-at-zero compatibility).
* `IsHypercontractive` reformulated via `eLpNorm` (no Bochner trap).
* `stroock_varopoulos` axiom added (vetted Standard), with `f ≥ 0` hypothesis (revision applied per Gemini's first pass).
* Net project axioms: 7 → 8.
* Downstream impact: none (no `.lean` file outside `Hypercontractivity.lean` imports these axioms; `pphi2`, `pphi2N`, `lgt`, `gaussian-hilbert` only consume axiom-free modules).

**Lessons learned:**
* **Two-pass Gemini vetting** caught the Stone-collapse trap that I would have missed; the second pass on the revised statement is a worthwhile sanity check before commit.
* **`ContDiff ⊤` vs `ContDiff ∞` semantics** in current Mathlib (`⊤ : WithTop ℕ∞` = analyticity ω, not C^∞) is a recurring footgun.
* **Bundling related fields** (semigroup data + form data + compatibility) into a single structure removes whole classes of "forgot a hypothesis" errors.
* **Use `Set.Ici 0` for right-derivatives of semigroups** — `HasDerivAt _ _ 0` is two-sided and breaks for `ℝ`-time semigroups.

---

## 2026-05-12: A2 (de Bruijn interior) discharge

**Goal:** discharge `hasDerivAt_entropy_ouSemigroup` (de Bruijn identity for `t > 0`), the last remaining atomic axiom in `MarkovSemigroups/General/OUEntropyDecomposition.lean`.

**Commits:**
* `b6d8ac7` — scaffold + Phase 1 wrap-up (sorry-free except for 3 hard sub-lemmas).
* `00cd52b` — full discharge by subagent (~740 lines new).
* `ab36ab0` — docs updates (Gaussian1D + General/OU chain axiom-free).

**Resources:**
* Time: ~1 day.
* Lines: ~740 (proof body) on top of ~270 (scaffold).
* Subagent: `lean4-sorry-filler-deep` (1 dispatch, large scope).

**Outcome:**
* `OUEntropyDecomposition.lean` is now axiom-free.
* The discharge uses a Stein-IBP-based formula for `(P_t g)''` (avoiding the unbounded operator `L`), parametric DCT for the entropy integral, and the bilinear Dirichlet form identity from Phase 1.
* Project axioms: 8 → 7. Gaussian1D + General/OU chain is fully discharged.

**Lessons learned:**
* **Subagent batch dispatch** (Phase 1 bilinear DF + Phase 2+3+4 combined for A2) was effective when each phase had clear deliverables and prior-art templates (e.g., `gaussian_dirichlet_form_identity` as the diagonal template for the bilinear version).
* **Avoiding unbounded generators in proof statements** keeps the formalization tractable: every appearance of `L f` was rewritten via Stein-IBP into a form using only bounded operations on `f` and `P_t f`.

---

## 2026-05-12: A2-boundary discharge

**Goal:** discharge `hasDerivWithinAt_entropy_ouSemigroup_zero` (de Bruijn at `t = 0+`) from A2 interior + DCT-based continuity.

**Commits:**
* `029df4b` — `~330`-line discharge by subagent.
* `93beb77` — docs.

**Resources:**
* Time: ~3 hours.
* Lines: ~330.
* Subagent: `lean4-sorry-filler-deep`.

**Outcome:**
* `hasDerivWithinAt_entropy_ouSemigroup_zero` is now a theorem.
* Uses Mathlib's `hasDerivWithinAt_Ici_of_tendsto_deriv` + DCT-based continuity of entropy and Fisher info at `s = 0+`.
* Net axioms: 9 → 8.

**Lessons learned:**
* **`hasDerivWithinAt_Ici_of_tendsto_deriv` is the canonical boundary-at-zero pattern** — we used it twice in this session (here and for `ouSemigroup_l2sq_hasDerivWithinAt_zero`). Worth remembering as a template.
* **Inlining helpers from sibling files** (here: `tendsto_ouSemigroup_pointwise_atZero_local` cloned from `EuclideanStein.lean`) is sometimes cleaner than adding new imports — especially when the helper is private and only ~30 lines.

---

## 2026-05-12: A1 (Fisher info gradient decay) discharge

**Goal:** discharge `ouSemigroup_fisher_info_decay`: `I(P_t g) ≤ e^{-2t} I(g)`.

**Commits:**
* `6a89298` — discharge by subagent (~400 lines including Cauchy-Schwarz helper).
* `00e9e88` — docs.

**Resources:**
* Time: ~2 hours.
* Lines: ~400 (proof + a ~58-line polynomial-discriminant Cauchy-Schwarz helper for `γ`).
* Subagent: `lean4-sorry-filler-deep`.

**Outcome:**
* `ouSemigroup_fisher_info_decay` is now a theorem.
* Proof: Cauchy-Schwarz on Mehler probability kernel with `A := g'/√g, B := √g` + Mehler derivative formula + γ-invariance.
* Mathlib doesn't have integral Cauchy-Schwarz in the form needed, so a polynomial-discriminant helper was added inline.

**Lessons learned:**
* **Inline helper lemmas for "missing-from-Mathlib" facts** — adding ~60 lines to derive integral Cauchy-Schwarz from `0 ≤ ∫(A - λB)²` was faster than searching for/contributing the Mathlib version.
* **Gemini's "use Cauchy-Schwarz instead of 2D Jensen"** suggestion (from the original A1+A2 vetting) was decisive. Always ask for proof-route advice during vetting.

---

## 2026-05-12: `ouSemigroup_entropy_sq_decay_bound` discharge

**Goal:** discharge BGL Theorem 5.5.2 (`Ent(f²) − Ent(P_t f²) ≤ 2(1 − e^{−2t}) E(f, f)`) by decomposition into A1 (Fisher info decay) + A2 (de Bruijn) atomic sub-axioms.

**Commits:**
* `6317beb` — add OUEntropyDecomposition axioms A1, A2 (vetted Standard).
* `1b3f797` — discharge `ouSemigroup_entropy_sq_decay_bound` via ε-regularization + FTC + DCT (~550 lines).
* `939d3f6` — docs.

**Resources:**
* Time: ~6 hours.
* Lines: ~550 (entropy decay proof) + ~250 (OUEntropyDecomposition.lean axiom file).
* Gemini vetting: 3.1-pro returned Standard for both A1 and A2 (each).
* Subagent: `lean4-sorry-filler-deep`.

**Outcome:**
* `ouSemigroup_entropy_sq_decay_bound` is now a theorem.
* Net axioms: replaced 1 broad axiom with 3 focused ones (A1, A2, A2-boundary). All three subsequently discharged (see entries above).
* `bakryEmerySpace` instance relocated from `EuclideanStein.lean` to `EuclideanEntropyDecay.lean` to break a circular import.

**Lessons learned:**
* **Decompose-then-discharge** is the right pattern when an axiom is a composition of standard textbook facts. The +2 net axioms were temporary; all three were discharged within 24 hours.
* **ε-regularization (`g_ε := f² + ε`) + DCT for `ε → 0`** handled the `log 0` non-smoothness cleanly. Standard treatment that worked smoothly in Lean.
* **`bakryEmerySpace` instance relocation** to break circular imports: when a downstream file (here `EuclideanEntropyDecay.lean`) needs the discharged version of an axiom, the instance using that axiom must live downstream. Worth planning the import graph carefully when decomposing axioms.

---

## 2026-05-12: Path C Hermite IBP discharge of `ouSemigroup_contDiff`

**Goal:** discharge the `C^∞`-smoothing axiom for the OU semigroup via Hermite-IBP without needing the SchwartzConvolution axiom (Path B).

**Commits:**
* `e9b007a` — scaffold (9 sorries).
* `a0e0ce8` — fill 6 decay + integrability sorries (~180 lines).
* `e62e4d7` — prove `hermite_ibp_gaussian` (~135 lines).
* `2b1b49e` — prove `iteratedDeriv_ouSemigroup_pos` (~210 lines).
* `e96ac42` — prove `ouSemigroup_contDiff_pos/bounded` (~100 lines).
* `890e022` — `IsCore` refactor `ContDiff ⊤ → ContDiff ∞` and remove `ouSemigroup_contDiff` axiom.
* `7c78bc4` — docs.

**Resources:**
* Time: ~1.5 days across the chain.
* Lines: ~625 across `EuclideanHermite.lean` (sorry-free).
* Subagent: `lean4-sorry-filler-deep` (4 dispatches, each filling 1–3 sorries).
* Vetting: Gemini 3.1-pro on the Path B SchwartzConvolution axiom (later not used because Path C was preferred).

**Outcome:**
* `ouSemigroup_contDiff` axiom removed.
* `ouSemigroup_contDiff_bounded` theorem proves `C^∞` smoothing via the closed-form iterated-derivative identity `(P_t f)^{(n)}(x) = (a/b)^n · ∫ y, H_n(y) · f(a·x + b·y) ∂γ`, by induction on `n` using `hermite_ibp_gaussian`.
* The Path B SchwartzConvolution axiom remains in `General/` but is unused.

**Lessons learned:**
* **Try multiple discharge paths before committing.** Path B (general SchwartzConvolution axiom) was Gemini-vetted Standard but we ended up not needing it because Path C (Hermite IBP) was more concrete and avoided change-of-variables to Lebesgue.
* **The bundled Hermite-IBP identity** is a powerful pattern: at each induction step, we push the derivative from `f` onto the Hermite weight `H_n`, so we never need `f''` (or higher). For `g` only `C¹` + bounded, we still get the full `C^∞` chain for `P_t g`.

---

## 2026-05-12: `IsCore` refactor `ContDiff ⊤ → ContDiff ∞`

**Goal:** fix a long-standing inconsistency where the project's `IsCore` typeclass used `ContDiff ℝ ⊤` (which in current Mathlib is analyticity / `ω`), but the project's prose and proofs intended `C^∞` (`ContDiff ℝ ∞`).

**Commits:**
* `890e022` — refactor + remove `ouSemigroup_contDiff` axiom (which can only be proved at C^∞, not analyticity).

**Resources:**
* Time: ~1 hour.
* Lines: ~70 net change across `Euclidean.lean`, `EuclideanStein.lean`, `EuclideanHermite.lean`.

**Outcome:**
* Project-wide replacement `ContDiff ℝ ⊤` → `ContDiff ℝ ∞` in Gaussian1D and related files.
* `IsCore` definition updated; consumers (Stein identity, l2sq derivative, etc.) updated to match.
* `open scoped ContDiff` added where needed.

**Lessons learned:**
* **Check Mathlib semantics of `⊤` for typeclass-like enumerations.** In `WithTop ℕ∞`, `⊤` = ω = analyticity, `∞` = C^∞. Easy to confuse.
* **A semantic refactor like this should be done before attempting hard proofs.** If we had tried to prove `ouSemigroup_contDiff` at the analyticity level, the proof wouldn't have closed (Mehler kernel preserves C^∞, not analyticity, in general).
