# MarkovSemigroups/Dobrushin

**View-only concordance.** This directory formalizes the
specification / DLR / Dobrushin-uniqueness layer for lattice spin
systems: Gibbsian specifications, the influence (interdependence)
matrix, Dobrushin's uniqueness criterion, the Neumann-series
comparison bound, and the single-site / multi-site disintegration
machinery that propagates influence through `condKernel` fibers.

The canonical reference is **Friedli & Velenik, *Statistical
Mechanics of Lattice Systems*, Cambridge, 2017, Chapter 6
(Infinite-Volume Gibbs Measures, pp. 245–320)** — the project's
free substitute for Georgii, *Gibbs Measures and Phase Transitions*.
The strong-coupling / sweeping-out analytic side is cross-referenced
to **Guionnet & Zegarliński 2002, Chapter 5 (LSI for spin systems on
a lattice, pp. 50–73)**.

This is the layer consumed downstream by
[`lgt`](https://github.com/mrdouglasny/lgt) (lattice Yang–Mills mass
gap): the distance-aware Dobrushin comparison bound and its
exponential correlation-decay corollary feed `lgt`'s
`dobrushin_correlation_bound` for the Wilson-plaquette use case.

This file is documentation only. It does not move, rename, or modify
any `.lean` source.

## Modules

| Module | Role | Canonical source | Status |
|--------|------|------------------|--------|
| `Specification.lean` | `SpinConfig`, `GibbsSpec` (conditional distributions given boundary), `IsGibbsMeasure` consistency — the specification formalism | Friedli–Velenik Ch. 6 §6.3, esp. §6.3.1 (kernels vs conditional probs, p. 257) and §6.3.2 (Gibbsian specifications from an interaction, p. 258); G–Z §5.1 (local Gibbs specification, DLR eq. 5.1.4) | 0 sorry, 0 axiom |
| `Uniqueness.lean` | `influenceCoeff` C(x,y) (TV influence matrix), `DobrushinCondition` (sup over columns < 1), `dobrushin_uniqueness`, `dobrushin_correlation_decay` | **Friedli–Velenik Ch. 6 §6.5.2, p. 268 (Dobrushin's Uniqueness Theorem)**; influence matrix $c_{ij}=\sup\|\pi_{\{i\}}(\cdot|\omega)-\pi_{\{i\}}(\cdot|\omega')\|_{TV}$, condition $\sup_i\sum_j c_{ij}<1\Rightarrow|\mathscr G(\pi)|=1$ | 0 sorry, 0 axiom (uses a bridge hypothesis `hMargToFull`; depends on `TVCoupling.exists_maximal_coupling`) |
| `NeumannSeries.lean` | `iterateInfluence` ($C^n$), `neumannSeriesCoeff` ($(I-C)^{-1}_{xy}$), bounds $(C^n)_{xy}\le\alpha^n$, $\sum_n\le 1/(1-\alpha)$, and the nearest-neighbor refinement $\le\alpha^{d(x,y)}/(1-\alpha)$ | Friedli–Velenik §6.5.2–6.5.4 (the geometric/Neumann series in $(c_{ij})$ in the uniqueness proof and its distance-aware high-temperature refinement, §6.5.3 p. 271) | 0 sorry, 0 axiom |
| `StrongCoupling.lean` | `dobrushin_nearest_neighbor`, `strong_coupling_dobrushin` — verifies Dobrushin's condition explicitly when the coupling is weak (column sum ≤ 2d·C_max < 1) | Friedli–Velenik §6.5.3 (sufficient temperature/interaction smallness ⇒ Dobrushin condition, p. 271); G–Z §5.2 strong-mixing strategy (Ciii) | 0 sorry, 0 axiom |
| `FiniteLattice.lean` | `condDist_univ_const` and uniqueness on a finite lattice: for `[Fintype I]`, DLR at Λ = univ forces a unique Gibbs measure with no Dobrushin condition | Friedli–Velenik §6.2.1 (DLR equations, p. 252) specialized to finite Λ; covers the finite-torus `lgt` use case | 0 sorry, 0 axiom |
| `CovarianceBound.lean` | Building-block lemmas (`abs_integral_le_bound`, conditional-measure support) for the Dobrushin covariance bound via single-site disintegration (M1) | Friedli–Velenik §6.5.2 TV-contraction; G–Z §5.1 conditional-expectation $E_\Lambda^\omega$ / DLR | 0 sorry, 0 axiom |
| `CondTVBridge.lean` | `hCondTV` bridge: single-site disintegration ⊕ Dobrushin influence propagation ⇒ conditional-expectation difference ≤ `2·Bg·neumannSeriesCoeff γ x y`; the joint-coupling formulation of Dobrushin uniqueness (counterexample-checked, see Gaps) | Friedli–Velenik §6.5.2 (TV-contraction iterated over single-site updates, p. 268); G–Z §5.1 ($E_\Lambda^\omega$, disintegration) | 0 sorry, 0 axiom (joint-coupling lemma stated with proof; design rationale vetted by Gemini Deep Think 2026-04-16) |
| `CovarianceBoundMultisite.lean` | Generalizes the covariance bound from single-site- to neighborhood-local observables: `condFiniteSupportMeasure`, multi-site fibers, DLR preservation at z ∉ N_f, multi-source Neumann iteration, textbook $\alpha^{d}/(1-\alpha)$ wiring; the bridge `lgt`'s Wilson plaquette consumes | Friedli–Velenik §6.5.2–6.5.4 (multi-site Neumann iteration / distance-aware bound); G–Z §5.1 `condKernel` fibers, §5.3 Lemma 5.3 local-block estimates | 0 sorry, 0 axiom |
| `CondKernelDLR.lean` | The `condKernel` fiber of a Gibbs measure (disintegrated via `piEquivPiSubtypeProd`) inherits the DLR equation at sites z ∉ N_f for a.e. fiber value; closes the disintegration → a.e.-bound chain | Friedli–Velenik §6.2.1 (DLR, p. 252) and §6.3.1 (kernels vs conditional probabilities, p. 257); G–Z §5.1 (`E_Λ^ω`, disintegration) | 0 sorry, 0 axiom (DLR-through-disintegration discharged via `fiberMeasure_dlr_ae`) |

**Status note.** `status.md` records the directory as **0 sorry, 0
axiom** (lines 59, 193–199). Verified directly: no `sorry` tactic
terms and no `axiom` declarations occur in any of the nine `.lean`
files. The strings "sorry"/"axiom" appear only inside docstrings —
historical strategy notes (`CondKernelDLR`), a **stale** forward
reference in `Uniqueness.lean`'s docstring describing
`TVCoupling.exists_maximal_coupling` as still `sorry` (verified
2026-05-16: it is in fact a fully proved theorem at
`TVCoupling.lean:352` via an explicit Hahn-decomposition
construction; `Coupling/` is entirely sorry-/axiom-free, so the
`lgt` mass-gap path is **not** blocked here — the `.lean` docstring
is left uncorrected under the view-only constraint), and the design
discussion explaining why
`CondTVBridge`'s joint-coupling lemma is stated in joint- rather than
marginal-TV form (a marginal-TV version is provably false; the
joint-coupling version is the classical, correct statement and is
proved here, not axiomatized).

## Gaps

Scope is the Dobrushin-uniqueness *criterion* and its quantitative
(Neumann / distance-aware) consequences — not the full
infinite-volume Gibbs theory of Friedli–Velenik Ch. 6:

- **Existence of an infinite-volume Gibbs measure** for a quasilocal
  specification (Friedli–Velenik §6.4, pp. 261–266) is not
  formalized — only uniqueness/comparison is.
- **Full Georgii-style specification theory** is not reproduced:
  extremal decomposition / Choquet simplex of $\mathscr G(\pi)$
  (§6.8), the variational principle (§6.9), and the non-uniqueness
  criterion (§6.11, p. 308) are out of scope. The
  boundary-condition-sensitivity / non-uniqueness side surfaces only
  as the honest "math is false" sorries in
  `Instances/WorkInProgress/` (outside this directory).
- **Capacity / quasi-regularity** (the Fukushima–Oshima–Takeda Ch. 2
  wall) is **not needed here**: this layer is measure-theoretic
  (kernels, DLR, TV, `condKernel`), not potential-theoretic.
- **Cluster-expansion uniqueness** (§6.5.4, p. 274) and the explicit
  high-temperature interaction → coefficient derivation are covered
  in the sibling `DobrushinZegarlinski/` layer
  (`InteractionMatrix.lean`), not here.
- `Uniqueness.lean` carries a bridge hypothesis `hMargToFull` and
  ultimately depends on `TVCoupling.exists_maximal_coupling`, which
  is still `sorry` in `Coupling/TVCoupling.lean` (upstream, not in
  this directory).

## Cross-refs

- Friedli–Velenik Ch. 6 (the master reference for this directory):
  [`refs/summaries/Friedli-Velenik/06-infinite-volume-gibbs.md`](../../refs/summaries/Friedli-Velenik/06-infinite-volume-gibbs.md)
  — §6.2.1 DLR (p. 252), §6.3 specifications (pp. 257–258),
  **§6.5.2 Dobrushin's Uniqueness Theorem (p. 268)**, §6.5.3–6.5.4
  high-temperature / cluster-expansion uniqueness (pp. 271–274).
- Guionnet–Zegarliński Ch. 5 (local specification, DLR,
  strong-mixing / sweeping-out analytic side):
  [`refs/summaries/Guionnet-Zegarlinski/05-lsi-spin-systems-lattice.md`](../../refs/summaries/Guionnet-Zegarlinski/05-lsi-spin-systems-lattice.md)
  — §5.1 DLR eq. 5.1.4 and $E_\Lambda^\omega$, §5.2 strategy
  conditions (Ci)–(Civ), §5.3 Lemma 5.3 local-block / sweeping-out
  estimates.
- Summaries index:
  [`refs/summaries/README.md`](../../refs/summaries/README.md).
- Downstream consumer:
  [`lgt`](https://github.com/mrdouglasny/lgt) — `lgt`'s
  `dobrushin_correlation_bound` is fed by the distance-aware bound and
  exponential-decay corollary built from `NeumannSeries.lean` /
  `CovarianceBoundMultisite.lean`.

*Fidelity:* citations are limited to what the two summary files
state; section/page anchors (notably §6.5.2 p. 268) are taken
verbatim from the Friedli–Velenik summary. The anchor hints in the
task brief were verified against the summaries and are correct as
given.
