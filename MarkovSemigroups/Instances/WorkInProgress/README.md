# `MarkovSemigroups/Instances/WorkInProgress/` — concordance (VIEW-ONLY)

**Honest-sorry concrete instances** (per project `CLAUDE.md`): these
modules carry their incompleteness openly rather than hiding behind
optimistic stubs. Two distinct kinds of incompleteness appear here and
are distinguished below:

- **Lean gap** — a standard textbook fact whose only obstacle is
  missing Mathlib infrastructure (parametric integration, generator
  theory). True, just not yet formalized.
- **Mathematically false** — the abstract field genuinely *does not
  hold* for this instance (e.g. the diffusion/Leibniz property fails
  for a jump process). The sorry records a real obstruction, not a
  TODO.

This file is a navigation aid only; it edits no `.lean`. Status is
cross-checked against the repo-root [`status.md`](../../../status.md)
(canonical sorry/axiom audit). Note: `grep -c "axiom"` over-counts —
the word appears in docstrings; the figures below are *declaration*
counts confirmed against `status.md`.

| Module | Role | Canonical source | Status |
|--------|------|------------------|--------|
| `Euclidean.lean` | Standard Gaussian `γ = N(0,1)` on ℝ with the OU/Mehler semigroup `P_t f(x)=∫f(e^{-t}x+√(1−e^{-2t})y)dγ(y)`, `Γ(f,g)=f'g'`, curvature `ρ=1`. Gross's original 1975 setting; the canonical `BakryEmerySpace` instance. | Gross, *Amer. J. Math.* 97 (1975); BGL-2014 Ch. 2 (OU semigroup, Mehler kernel). Analytic spine: Ledoux-2000 §1 (OU = `CD(1,∞)`, Gaussian extremal). van Handel Ch. 3 (Gaussian LSI / Herbst). | **2 sorry, 0 axiom.** Per `status.md`: the original 9 Mehler-kernel sorries (Lean-infrastructure gaps) were discharged; concrete instance is now **axiom-free**. Remaining 2 sorries are **Lean gaps** (standard textbook results; obstacle = parametric-integration infra), per the module's own "## Status" docstring. |
| `EuclideanStein.lean` | Stein-identity discharges for the Gaussian1D instance: Gaussian IBP `∫y·g dγ=∫g' dγ` (BGL §1.15), Dirichlet-form identity `∫g·Lg dγ=−∫(g')² dγ` (BGL §1.6), heat equation `∂_τ P_τ f=L P_t f` (BGL §2.7), L²-norm derivative (BGL Prop 4.7.1). | BGL-2014 §1.6, §1.15, §2.7, Prop 4.7.1. Stein/Gaussian-IBP background: van Handel Ch. 2–3. | **0 sorry, 0 axiom.** Discharge layer; the legacy `ouSemigroup_l2_sq_hasDerivWithinAt` is now a **theorem** here (status.md). |
| `EuclideanHermite.lean` | C^∞ smoothing of OU via Hermite IBP: `(P_t f)^{(n)}(x)=(a/b)^n∫H_n(y)f(ax+by)dγ`, `a=e^{-t}`, `b=√(1−e^{-2t})`, induction + `hermite_ibp_gaussian`. Discharges `ouSemigroup_contDiff`. | BGL-2014 §2.7.1 (Mehler kernel); Mathlib `Polynomial.hermite`, `deriv_gaussian_eq_hermite_mul_gaussian`. Ledoux-2000 §1 (Hermite/OU spectral structure). | **0 sorry, 0 axiom.** `ouSemigroup_preserves_IsCore` proved axiom-free here (status.md). |
| `EuclideanEntropyDecay.lean` | Derives the dynamic entropy decay bound `Ent(f²)−Ent(P_t f²) ≤ 2(1−e^{-2t})E(f,f)` (BGL Thm 5.5.2) from the two atomic axioms A1 (Fisher-info decay) + A2 (de Bruijn), via ε-regularization + FTC + DCT. | BGL-2014 Theorem 5.5.2 / §5.5. The two atomic axioms live in `MarkovSemigroups/General/OUEntropyDecomposition.lean` (vetted Standard), **not** in this directory. | **0 sorry, 0 axiom in-file.** The result is a *theorem*; its 3 atomic sub-axioms are in `General/` (status.md). |
| `EuclideanFin.lean` | Multivariate Gaussian: standard product Gaussian `γFin n = Measure.pi γ` on `Fin n → ℝ`, finite-dim Bakry–Émery data for the Stage-N1 construction. | BGL-2014 Ch. 2 (tensorized OU); Ledoux-2000 §1 (LSI/Poincaré tensorize, (1.23)–(1.24)). | **0 sorry, 3 axioms.** Real `axiom` decls (verified): `ouSemigroupFin_l2_sq_hasDerivWithinAt`, `ouSemigroupFin_preserves_IsCore`, `ouSemigroupFin_entropy_sq_decay_bound` — the multivariate lifts of the 1D facts already discharged in the scalar files; **Lean-gap axioms** (true, awaiting the `Measure.pi` parametric-integration lift). |
| `EuclideanStein.lean` / above | (see above) | — | — |
| `EuclideanTests.lean` | Validation/exercise theorems: Mehler kernel on first three Hermite polynomials gives eigenvalues `1, e^{-t}, e^{-2t}`; `cos ∈ IsCore` with `ρ=1`; a conditional Brascamp–Lieb ↔ Bakry–Émery coherence check for `V(x)=x²/2`. | BGL-2014 Ch. 2 (Mehler/OU eigenfunctions), §4.9 (Brascamp–Lieb). Eigenfunction structure: Ledoux-2000 §1. | **0 sorry, 4 local test axioms** (`gaussianResolvent`, `gaussianResolvent_ibp`, `gaussianResolvent_ibp_integrable`, `gaussianBochner_identity`) — scaffolding for the *conditional* coherence check (part C), not load-bearing for the production instances. |
| `TwoPoint.lean` | Two-point space `{0,1}`, uniform `μ=½(δ₀+δ₁)`, jump chain `P_t f(i)=½(1+e^{-2αt})f(i)+½(1−e^{-2αt})f(1−i)`, `ρ=2α`. Simplest would-be `BakryEmerySpace` instance — and a deliberate counterexample probe. | Elementary discrete two-point Markov chain (folklore / Ledoux-2000 §1 discrete-Γ remarks; Diaconis-style two-state continuous-time chain). | **5 sorry (status.md headline: 2), 0 axiom.** Per `status.md`, the 2 *headline* sorries are **mathematically false** for this instance: `Γ_leibniz` (Leibniz/diffusion property fails for a jump process — there is no chain rule) and `semigroup_entropy_sq_decay_bound` (a consequence of that failure). The remaining sorries are downstream of the same genuine obstruction. This instance exists to show *which* `BakryEmerySpace` fields are non-trivial / fail off the diffusion setting. |

## Gaps

- **Lean gaps (true, infra-bound):** `Euclidean.lean` (2 sorries —
  parametric integration against continuous measures, per its own
  "## Status" docstring) and the 3 `EuclideanFin.lean` axioms
  (multivariate lifts of already-discharged 1D facts).
- **Mathematically false (genuine obstruction, not TODO):**
  `TwoPoint.lean` `Γ_leibniz` and `semigroup_entropy_sq_decay_bound`
  — the diffusion/Leibniz axiom does **not** hold for a two-point
  jump process; `status.md` labels these explicitly "math false."
  This is the intended honest-sorry per `CLAUDE.md`.
- `EuclideanStein/Hermite/EntropyDecay.lean` are **sorry-free,
  free-axiom-free** discharge layers; they exist to convert the old
  `Euclidean.lean` Mehler-kernel axioms into theorems (all 9 original
  axioms discharged per `status.md`).
- Local "test axioms" in `EuclideanTests.lean` are scaffolding for a
  conditional coherence check and do not feed the production
  `Instances/` modules.

## Cross-refs

- Gaussian / OU / Mehler analytic spine:
  [`refs/summaries/Ledoux-2000/01-geometric-aspects-of-diffusion-generators.md`](../../../refs/summaries/Ledoux-2000/01-geometric-aspects-of-diffusion-generators.md)
  (OU `CD(1,∞)`, Hermite/Gaussian extremality),
  [`refs/summaries/Ledoux-2000/04-sobolev-inequalities-and-heat-kernel-bounds.md`](../../../refs/summaries/Ledoux-2000/04-sobolev-inequalities-and-heat-kernel-bounds.md)
  (Gross equivalence).
- Gaussian LSI / Stein / Herbst (van Handel):
  [`refs/summaries/vanHandel/02-variance-poincare.md`](../../../refs/summaries/vanHandel/02-variance-poincare.md),
  [`refs/summaries/vanHandel/03-subgaussian-logsobolev.md`](../../../refs/summaries/vanHandel/03-subgaussian-logsobolev.md),
  [`refs/summaries/vanHandel/08-sharp-transitions-hypercontractivity.md`](../../../refs/summaries/vanHandel/08-sharp-transitions-hypercontractivity.md).
- BGL Ch. 2 / §4.9 / §5.5 headings only (local PDF is a truncated
  teaser — flagged unreliable, use Ledoux-2000 for substance):
  [`refs/summaries/BGL-2014/00-index.md`](../../../refs/summaries/BGL-2014/00-index.md).
- Repo-root audit: [`status.md`](../../../status.md).
