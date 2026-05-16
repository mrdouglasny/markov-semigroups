# MarkovSemigroups/Coupling

Total-variation coupling theory: the coupling characterization of TV
distance, an explicit (choice-free) maximal coupling for countable
spaces, and the iterated Dobrushin coupling that drives the
spin-system uniqueness / correlation-decay layer. This directory is
the probabilistic backbone consumed by `Dobrushin/*`,
`DobrushinZegarlinski/*`, and (transitively) `lgt`'s mass-gap proof.

Mathlib (as of April 2026) has no coupling theory; the TV
characterization and maximal-coupling existence here are a genuine
gap-fill.

| Module | Role | Canonical source | Status |
|--------|------|------------------|--------|
| `TVCoupling.lean` | `IsCoupling`; lower bound `tvDist ≤ P(σ≠τ)` for any coupling; maximal-coupling construction; `tvDist_eq_inf_coupling` | Levin–Peres–Wilmer Ch. 4 §4.2, **Prop. 4.7** (coupling characterization + optimal/maximal coupling), pp. 47–59; Lindvall, *Lectures on the Coupling Method* (1992); Villani, *Optimal Transport* (2009) Ch. 1 | Proved — 0 sorry, 0 axiom (`tvDist_le_coupling`, `maximal_coupling` proved per `status.md`) |
| `CanonicalCoupling.lean` | Explicit maximal coupling on countable `S` via `P = (μ⊓ν)∘diag + c⁻¹·(μ−μ⊓ν)⊗(ν−μ⊓ν)` — no Axiom of Choice, with Giry-parametric measurability; plus Dobrushin iterated-coupling **existence** wrapper | Levin–Peres–Wilmer Ch. 5 §5.4 (grand / common-part / maximal couplings), pp. 60–74; Dobrushin (1968) Lemma 2; Georgii (1988) **Prop. 8.7**; Lindvall (1992) | Proved — 0 sorry, 0 axiom |
| `DobrushinCoupling.lean` | Per-site coupled kernel (`coupledSingleSiteKernel`), `updateCoupling`, iterated `dobrushinCoupling`; local contraction `tvDist_marginal_le_influenceCoeff_sum`; main `dobrushin_iterated_coupling_fintype` | Levin–Peres–Wilmer Ch. 14 (transportation metric + path/edge contraction), pp. 201–214; Dobrushin (1968) Lemma 2; Georgii (1988) Prop. 8.7; Guionnet–Zegarliński (2002) spin-system coupling (Ch. 5) | Proved — 0 sorry, 0 axiom (header "Sorry inventory" lists all sub-lemmas CLOSED) |
| `ProkhorovCoupling.lean` | Compact-spin version: coupling set is a closed subset of the compact `ProbabilityMeasure(Ω×Ω)`, disagreement lsc by Portmanteau ⟹ minimizer exists and contracts. Proves former `dobrushin_coupling_axiom_compact` as a **theorem** (now a backward-compat alias) | Prokhorov (1956); Dobrushin (1968) Lemma 2; Georgii (1988) Prop. 8.7; Mathlib Portmanteau / Prokhorov; Levin–Peres–Wilmer Ch. 4–5 (tightness in the TV/coupling layer) | Proved — 0 sorry, 0 axiom (eliminates the last custom axiom on the mass-gap path) |

## Gaps

- **None outstanding in `Coupling/`.** `status.md` records the
  directory as 0 sorry / 0 axiom. The previously custom
  `dobrushin_coupling_axiom` (formerly in `DobrushinCoupling.lean`)
  is now discharged as a theorem in `ProkhorovCoupling.lean` and kept
  only as a backward-compatibility alias (line ~1075).
- **Anchor-fidelity caveat (inherited):** Levin–Peres–Wilmer
  proposition/theorem *numbers* (Prop. 4.7, etc.) are knowledge-based
  — only the PDF table of contents was machine-read; chapter
  titles/page ranges are from the TOC and are reliable, the inline
  `Prop. N.M` labels are hedged. Treat the Ch./§/pp. citations as
  authoritative and the bare numbers as indicative.
- The `CanonicalCoupling.lean` "Part 2" Dobrushin-existence statement
  cites Dobrushin (1968) Lemma 2 / Georgii (1988) Prop. 8.7; these
  are *not* in the local summary corpus (Georgii substitute is
  Friedli–Velenik Ch. 6 §6.5.2 p. 268 — uniqueness, not the coupling
  lemma per se), so that anchor is taken from the source docstring,
  not cross-validated against `refs/summaries/`.

## Cross-refs

- TV distance + coupling characterization + maximal coupling:
  [`refs/summaries/Levin-Peres-Wilmer/04-introduction-mixing.md`](../../refs/summaries/Levin-Peres-Wilmer/04-introduction-mixing.md)
  (§4.1–4.2, Prop. 4.7) — explicitly flagged there as the discrete
  model for `Coupling/TVCoupling.lean`.
- Maximal / common-part / grand couplings + coupling inequality:
  [`refs/summaries/Levin-Peres-Wilmer/05-coupling.md`](../../refs/summaries/Levin-Peres-Wilmer/05-coupling.md)
  (§5.1, §5.4) — flagged there as matching
  `Coupling/CanonicalCoupling.lean`.
- Transportation metric + path/edge contraction (Bubley–Dyer),
  model for the Dobrushin contraction estimate:
  [`refs/summaries/Levin-Peres-Wilmer/14-transportation-metric-path-coupling.md`](../../refs/summaries/Levin-Peres-Wilmer/14-transportation-metric-path-coupling.md)
  (§14.1–14.2).
- Spin-system / lattice coupling context (Dobrushin–Zegarliński
  programme):
  [`refs/summaries/Guionnet-Zegarlinski/05-lsi-spin-systems-lattice.md`](../../refs/summaries/Guionnet-Zegarlinski/05-lsi-spin-systems-lattice.md).
- Dobrushin uniqueness target consuming this coupling layer (Georgii
  substitute):
  [`refs/summaries/Friedli-Velenik/06-*.md`](../../refs/summaries/Friedli-Velenik/00-index.md)
  (Ch. 6 §6.5.2, p. 268).
