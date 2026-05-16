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

* [`gross-discharge.md`](gross-discharge.md) — **RECOMMENDED (most
  general feasible).** Corrected Route A after Gemini deep-think
  vetting (2026-05-16): discharge the abstract
  `gross_lsi_implies_hypercontractive` on `DirichletMarkovSemigroup`
  via a `hille-yosida` generator bridge, with `stroock_varopoulos` as
  a theorem hypothesis (S–V unprovable abstractly — needs
  Beurling–Deny). Yields the general BGL §5.2 theorem *and* unblocks
  pphi2 (GaussianFin discharges the S–V hypothesis concretely).
  ~1350–2450 lines, multi-week.
* [`gaussian-ou-hypercontractivity.md`](gaussian-ou-hypercontractivity.md) —
  **FALLBACK only** (Route B, concrete Gaussian). Sound but yields no
  general result; reconciled 2026-05-16. Retained for its reusable
  Stroock–Varopoulos / Mehler-kernel techniques.
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
