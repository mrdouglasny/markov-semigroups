# `MarkovSemigroups/General/` — generic analytic bridges for the OU entropy-decay program

Small support directory holding the **atomic textbook bridges** that
discharge the broad Ornstein–Uhlenbeck entropy-decay axiom, plus the
Schwartz-class smoothing lemma their Mehler-kernel application needs.
Both modules are *generic*: stated in Mathlib style and reusable by any
future `BakryEmerySpace` instance, not tied to the concrete Euclidean
Gaussian construction (that consumer lives in
`Instances/WorkInProgress/EuclideanEntropyDecay.lean`).

| Module | Role | Canonical source | Status |
|--------|------|------------------|--------|
| `OUEntropyDecomposition.lean` | Splits the broad axiom `ouSemigroup_entropy_sq_decay_bound` into atomic Bakry–Émery bridges for the OU semigroup on `ℝ`: **A1** Fisher-information gradient decay `I(P_t g) ≤ e^{-2t} I(g)`, **A2** de Bruijn identity `(d/dt) H(P_t g) = −I(P_t g)` for `t > 0`, and the `t = 0⁺` boundary version. The `ε`-regularized assembly (`g_ε := f² + ε`, FTC + DCT for `ε → 0`) and a partial deep-pass proof of the de Bruijn `HasDerivAt` statement also live here. | Bakry–Gentil–Ledoux 2014, **§5.5, Theorem 5.5.2** (de Bruijn identity + Fisher-information decay + entropy decay under Bakry–Émery curvature); Bakry–Émery 1985 §I. OU is the `CD(1,∞)` model — cross-checked against Ledoux-2000 survey §1 (Def. 1.2, OU generator `CD(1,∞)`, eq. 1.9). | 3 atomic axioms, vetted **Standard** (Gemini 3.1-pro, 2026-05-12); the broad parent axiom is thereby a **theorem**. 1 `sorry` remains in the partial deep-pass proof of the de Bruijn `HasDerivAt` lemma (line ~620; four sub-lemmas; strategy fully documented inline). |
| `SchwartzConvolution.lean` | States the smoothing-by-Schwartz theorem: convolution of a bounded measurable `f` against a `C^∞` kernel with integrable iterated derivatives is `C^∞`. Applied to the Mehler kernel to give `ouSemigroup_contDiff` as a one-line corollary. | Analytic **utility** — only a soft textbook locus: Reed–Simon, *Methods of Modern Mathematical Physics I*, **Theorem V.4** (Schwartz space closed under convolution, `C^∞`); Folland, *Real Analysis*, **§8.2**. Generalizes Mathlib's compact-support `HasCompactSupport.contDiff_convolution_right`. | 1 axiom `contDiff_top_convolution_schwartzKernel` (vetting-required textbook bridge; no Schwartz-class version in Mathlib at time of writing). |

## Cross-refs

- Downstream consumer: `Instances/WorkInProgress/Euclidean.lean`
  (`ouSemigroup_contDiff`) and
  `Instances/WorkInProgress/EuclideanEntropyDecay.lean` (discharge of
  `ouSemigroup_entropy_sq_decay_bound` via the A1+A2 decomposition).
- Curvature framework: `Diffusion/CarreDuChamp.lean`,
  `Diffusion/BakryEmerySpace.lean` (the `BakryEmerySpace` instances the
  atomic axioms are designed to be reused by).
- Parallels already-proved analogs in `Euclidean.lean`:
  `ouSemigroup_gradient_decay` (mirrors A1) and
  `hasDerivAt_l2sq_ouSemigroup_pos` (mirrors A2).
- Status / axiom audit: repo-root `status.md` (entries for
  `ouSemigroup_entropy_sq_decay_bound`, A1/A2, and
  `ouSemigroupFin_entropy_sq_decay_bound`).
- Summaries: `refs/summaries/BGL-2014/`, `refs/summaries/Ledoux-2000/`
  (start at `refs/summaries/README.md`).
