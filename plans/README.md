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

* [`gross-discharge.md`](gross-discharge.md) — **Route A**: discharge
  the abstract `gross_lsi_implies_hypercontractive` (+ `stroock_varopoulos`)
  on the `DirichletMarkovSemigroup` carrier. This is the binding axiom
  on the live pphi2 chain (verified 2026-05-16). Structure-augmentation
  + 5 phases, ~1700–3000 lines, multi-week.
* [`gaussian-ou-hypercontractivity.md`](gaussian-ou-hypercontractivity.md) —
  **SUPERSEDED** as the pphi2-unblocking path (reconciled 2026-05-16);
  retained as the Route-B concrete-Gaussian alternative + reusable
  techniques. See its reconciliation note; prefer `gross-discharge.md`.
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
