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

When a plan is complete, move it to `archive/` and update its status
header. Add a one-line note in `archive/README.md` (create if needed)
linking back to the relevant commits.

## Active plans

* [`gaussian-ou-hypercontractivity.md`](gaussian-ou-hypercontractivity.md) —
  Full chain from `stroock_varopoulos` to pphi2's
  `gaussian_hypercontractivity_continuum`, via Gaussian1D + multivariate
  OU Gross discharge. 6 phases internal to
  `markov-semigroups`/`gaussian-hilbert`, ~1900–3200 lines, 6–9 weeks.
