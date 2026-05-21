# Archived plans

Completed plans move here from `plans/`. Each entry should record:

- **Plan file** (moved here from `plans/`).
- **Date completed**.
- **Commits delivering the work** (or PR links).
- **Outcome** (one-line summary; deviations from the plan if any).

## Index

### Gross LSI ⇒ hypercontractivity (abstract spine — all completed 2026-05-21)

The hypothesis-parameterised theorem
`gross_lsi_implies_hypercontractive_of_hypotheses` is fully proved and
`Abstract/GrossODE.lean` is sorry-free; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`. See
[`../history.md`](../history.md) for the consolidated entry.

* [`p2-strongL2-leibniz-discharge.md`](p2-strongL2-leibniz-discharge.md) —
  P2 Leibniz kernel `hasDerivWithinAt_integral_of_strongL2Deriv`, proved
  axiom-free (2026-05-20). The reusable strong-`L²` parametric-derivative
  bridge under `grossPow_hasDerivWithinAt`.
* [`grosspow-hasderivwithinAt-structural-blockers.md`](grosspow-hasderivwithinAt-structural-blockers.md)
  — the 4 structural blockers for `grossPow_hasDerivWithinAt`; all
  resolved (Path A strict-positivity + the two `IsCore_*` fields).
* [`gross-design-strictly-positive-escape.md`](gross-design-strictly-positive-escape.md)
  — Path A design (`hf_pos : ∃ ε > 0, ε ≤ f` + `IsCore_rpow_pos_strict`):
  on `[ε,∞)`, `x ↦ x^{q-1}` is `C^∞`. Implemented.
* [`codex-prompt-h_second.md`](codex-prompt-h_second.md) — brief for the
  off-diagonal chain-rule half (`h_second`); discharged by hand
  (MVT-in-τ + `abs_integral_rpow_mul_log_sub_le` + `squeeze_zero_norm'`).
* [`codex-prompt-h_energy.md`](codex-prompt-h_energy.md) — brief for the
  energy identification (`h_energy`); discharged via the generator
  pairing (`P_s Af = Ag'` by strong-`L²` limit uniqueness). Surfaced the
  carré-du-champ a.e.-invariance issue → `orbitCoreRep` refactor.
* [`sv-q-relaxation-vetting.md`](sv-q-relaxation-vetting.md) — deep-think
  vetting (verdict: APPROVED, rating Standard) of relaxing
  `StroockVaropoulos._hq` from `2 ≤ q` to `1 < q`.
* [`corelpapprox-vetting.md`](corelpapprox-vetting.md) — deep-think
  vetting (verdict: APPROVED with the `P_t`-decoupling refinement) of the
  4th per-instance predicate `CoreLpL2Approx` + the final general-`f`
  reduction glue.

**Commits (markov-semigroups, branch `gross-grossPow-hasDerivWithinAt-body`):**
helper `af8e881`; `h_second` `a075063`; energy→`orbitCoreRep` refactor
`458d2f3`; `h_energy` `509773e`; P3 `92ed88a`; core+positive bound
`df46789`; final theorem `82e1602`.
