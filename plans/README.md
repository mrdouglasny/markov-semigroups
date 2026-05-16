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
* [`beurling-deny.md`](beurling-deny.md) — Formulate Beurling–Deny
  decomposition; prove finite-state case sorry-free, axiomatize general
  case (one vetted axiom), finite certified as instance of the shared
  predicate. New `Abstract/BeurlingDeny.lean`, ~250–400 lines, 3–6 days.
  Criteria/spectral strand decoupled (consumes quantumlib later).

## History

[`history.md`](history.md) — chronological log of completed
substantial work, with commits, resources, outcomes, and lessons
learned. Includes back-filled entries for major 2026-05-12 / 13
discharges (Path C Hermite IBP, entropy decay decomposition,
A1/A2/A2-boundary, bundled Gross refactor, S–V axiom).
