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

* [`gross-discharge.md`](gross-discharge.md) — **RECOMMENDED; in
  progress** on branch `feat/lp-carrier-stdGaussianFin-dirichletmarkov`
  (tip `aa9cc47`; the rev gaussian-hilbert pins). **As of 2026-05-17:
  H0 ✅, G1 ✅, G2 ✅ (sorry-free, 2 general Gemini-vetted axioms),
  G4 ✅; abstract Gross relocated to `Abstract/GrossODE.lean`; P3
  scaffolded + P2 decomposed.** Remaining: one general Mathlib-native
  Bochner–Leibniz kernel (`hasDerivWithinAt_integral_of_strongL2Deriv`,
  to be proved — *not* axiomatized) + thin glue, the P3 cancellation
  algebra, and **W** (rewire gaussian-hilbert). 8 documented `sorry`s
  in `GrossODE.lean`; gaussian-hilbert unaffected.
* [`gaussian-ou-hypercontractivity.md`](gaussian-ou-hypercontractivity.md) —
  **FALLBACK only** (Route B, concrete Gaussian). Sound but yields no
  general result; reconciled 2026-05-16. Retained for its reusable
  Stroock–Varopoulos / Mehler-kernel techniques.
* [`beurling-deny.md`](beurling-deny.md) — Formulate Beurling–Deny
  decomposition; prove finite-state case sorry-free, axiomatize general
  case (one vetted axiom), finite certified as instance of the shared
  predicate. New `Abstract/BeurlingDeny.lean`, ~250–400 lines, 3–6 days.
  Criteria/spectral strand decoupled (consumes quantumlib later).

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
  — Builds the concrete `DirichletMarkovSemigroup (Fin n → ℝ)`
  instance on the Lp-carrier. **DELIVERED** — landed as
  `EuclideanFinLp.lean`'s `stdGaussianFin_dirichletMarkovSemigroup`,
  now on `main` via the Lp-carrier merge `ba9a8de` (2026-05-16); the
  brief itself is historical.
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
