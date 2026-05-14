# Plans

Active planning documents for substantial, multi-step work in
`markov-semigroups`. Completed plans go to [`archive/`](archive/).

Each plan should:
- State the **goal** (what theorem/structure ends up proved/built).
- Sketch the **dependency chain** and break work into phases.
- Give **line/effort estimates** per phase.
- Flag **risks** and dependencies on other repos
  (`gaussian-hilbert`, `pphi2`, `pphi2N`, `lgt`, Codex branches).
- Track **status** at the top of the doc.

When a plan is complete, move it to `archive/`, update its status
header, and add a structured entry to [`history.md`](history.md)
recording resources used (time, lines, subagents, vetting calls) and
lessons learned.

## Active plans

* [`gaussian-ou-hypercontractivity.md`](gaussian-ou-hypercontractivity.md) —
  Full chain from `stroock_varopoulos` to pphi2's
  `gaussian_hypercontractivity_continuum`, via Gaussian1D + multivariate
  OU Gross discharge. 6 phases internal to
  `markov-semigroups`/`gaussian-hilbert`, ~1900–3200 lines, 6–9 weeks.
  Phase 2 + Phase 4 delivery is now happening multivariate-first via
  Stage N (see codex briefs below); see the doc's 2026-05-14 status
  update for details.

### Codex briefs (in [`../docs/`](../docs/), cross-referenced here)

Historical reason: these existed in `docs/` before the `plans/`
convention was set up. They are *active* plans and belong in this index.

* [`docs/stage-n-detailed-plan.md`](../docs/stage-n-detailed-plan.md) —
  Detailed N1/N2/N3 plan for the multivariate Gaussian
  Bakry-Émery instance, with progress dates from 2026-05-12/13. N1 has
  merged (`stdGaussianFin.bakryEmerySpace n` + 3 placeholder
  axioms); N2/N3 (gaussian-hilbert wire-in to discharge
  `ouSemigroupAct_eLpNorm_hypercontractive`) are in progress.
* [`docs/stage-n-phase-2-codex-brief.md`](../docs/stage-n-phase-2-codex-brief.md)
  — **Currently open codex hand-off** (2026-05-13, commit `7ccef48`):
  builds the concrete `DirichletMarkovSemigroup (Fin n → ℝ)` instance
  using the new Lp-carrier framework. ~3-5 active days, no new
  axioms.
* [`docs/lp-carrier-refactor-design.md`](../docs/lp-carrier-refactor-design.md)
  — Technical design doc for the 2026-05-13 Lp-carrier refactor (now
  largely historical; merged at `e1e2011`). Kept for reference on
  why the abstract carrier shape changed.

## History

[`history.md`](history.md) — chronological log of completed
substantial work, with commits, resources, outcomes, and lessons
learned. Includes back-filled entries for major 2026-05-12 / 13
discharges (Path C Hermite IBP, entropy decay decomposition,
A1/A2/A2-boundary, bundled Gross refactor, S–V axiom).
