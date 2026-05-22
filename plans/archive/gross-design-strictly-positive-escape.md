> **📦 ARCHIVED 2026-05-21 — work complete (GrossODE.lean is sorry-free). Retained for provenance; see [`../history.md`](../history.md).**

# Gross discharge: the strictly-positive escape (Path A)

**Date:** 2026-05-20
**Status:** Chosen design route for completing
[`grossPow_hasDerivWithinAt`](../MarkovSemigroups/Abstract/GrossODE.lean).
**Replaces:** the "bundle the 4 structural blockers" question raised in
[`plans/grosspow-hasderivwithinAt-structural-blockers.md`](grosspow-hasderivwithinAt-structural-blockers.md)
— after Blockers 1, 2, 4 were proved from the existing fields, only
Blocker 3 (core-membership of `|u_s|^{q-1}`) remained, and Gemini
deep-think identified a textbook escape that sidesteps the structural
refactor.

**Vetting:** Gemini deep-think (`gemini-3.1-pro-preview`, 2026-05-20,
28s) on the 4-claim analysis below. See [§3](#3-gemini-verdict-summary)
for the verbatim verdict.

---

## 1. The blocker that triggered this

After Blockers 1, 2, 4 were proved from existing fields (commit
`688ed40`), the remaining piece for the body of
`grossPow_hasDerivWithinAt` was identifying

```
∂₁H(s,s) = ∫ ψ'(u_s) · A(u_s) dμ
```

(from `hasDerivWithinAt_integral_of_strongL2Deriv` with `ψ(x) := |x|^{q(s)}`,
`u_s := P_s f`, `q(s) > 1`) with the energy term in `grossPowDeriv`,
namely

```
-q(s) · D.energy(u_s, u_s^{q(s)-1}).
```

The bridge uses `h_gen`'s pairing identity `⟪coreToL2 g, A f⟫ = -energy g f`,
applied with `g := u_s^{q-1}`. This forces `IsCore (u_s^{q-1})`.

For the natural concrete cores (smooth functions / polynomials in
Gaussian instances), `|u_s|^{q-1}` is generally **not smooth** at zeros
of `u_s` for non-integer `q-1` (it's only `C^{⌊q-1⌋}`). So a
straightforward `IsCore_rpow_pos` axiom would be false at the
discharge stage.

---

## 2. The 4 claims I sent to Gemini

(Full query: written this session; reproduced in
[§7](#7-the-full-query-sent-to-gemini).)

**(1)** `core_dense_in_L2` is *not* provable from the existing fields.
Counterexample: `IsCore f := ∀ x, f x = 0`.

**(2)** Adding `core_dense_in_L2` alone is *insufficient* for
Blocker 3 — both sides of the pairing identity need continuity in the
*same* norm, and `energy` is typically not L²-continuous (only
form-norm-continuous), so density extension needs form-norm
machinery.

**(3)** Adding `IsCore_rpow_pos` fails for smooth Gaussian cores
because `|f|^{q-1}` for non-integer `q-1` has limited regularity at
zeros of `f`.

**(4)** The clean abstraction is a separate `IsFormDomain` predicate
(broader than `IsCore`, Sobolev W^{1,2}-like, closed under positive
rpow, where `energy` lives).

---

## 3. Gemini verdict (summary)

**(1) ✅ True**, but my counterexample was *wrong* (it violated
`IsCore_const c` for `c ≠ 0`). **Corrected counterexample**:
`IsCore f := ∃ c, ∀ x, f x = c` (the constant-functions subspace) —
satisfies all four `IsCore_*` axioms, but is not dense in L² unless
the space is trivial. Conclusion stands: density must be
explicitly axiomatised.

**(2) ⚠️ False premise, right conclusion.** Subtlety Gemini caught:
for a *fixed* `f ∈ dom(A)` (and `Af ∈ L²`), the map
`g ↦ ⟨g, Af⟩` *is* L²-continuous (Cauchy–Schwarz bounds it by
`‖Af‖_{L²}`). So `core_dense_in_L2` *would* let us uniquely *extend
the definition* of the pairing to all `g ∈ L²`. **The catch**: we
can't then prove the nonlinear chain rule (Gross's energy identity)
just from that L²-extension — that step requires form-norm machinery
(Stampacchia / D(E) chain rule) regardless. So we'd be exporting
"L²-extended energy" which would match the actual `energy` only on
the form domain anyway.

**(3) ✅ True** — fatal for a smooth core. **But Gemini surfaced the
textbook escape**:

> *Don't evaluate at `f ≥ 0`; evaluate at strictly positive
> `f ≥ ε > 0`. Then `u_s = P_s f ≥ ε` (positivity + conservation;
> `P_t (const ε) = const ε`). On `[ε, ∞)`, `x ↦ x^{q-1}` is C^∞ for
> any `q > 1`, so applying it to `u_s` preserves the smooth core.
> Prove hypercontractivity for `f ≥ ε`, then pass `ε → 0` via
> Fatou / MCT at the end of the Gross theorem.*

This is the standard trick in Gross 1975's original argument.

**(4) ✅ True, but simpler design than I proposed**:

> *Don't make `IsFormDomain` a separate predicate — make it the
> baseline. Replace `IsCore` with the closed form domain `D(E)`
> directly (with Markovian property
> `u ∈ D(E) ⇒ u ∧ 1 ∈ D(E)`, etc.), define the generator entirely
> via the form, and leave smooth cores as instance-level
> implementation details.*

---

## 4. Two paths forward

### Path A — Strictly-positive escape (chosen)

Adopt Gemini's Blocker 3 escape:

1. Add hypothesis `(hf_pos : ∃ ε > 0, ∀ᵐ x ∂μ, ε ≤ f x)` to
   `grossPow_hasDerivWithinAt`.
2. Derive `(P_s f : X → ℝ) y ≥ ε` a.e. from `P_positivity` +
   `P_conservation` + the existing `Linfty_contraction` proof
   technique. (We need a *lower* bound version — `0 ≤ f - const ε`
   in Lp, then `0 ≤ P_t (f - const ε) = P_t f - const ε`, hence
   `P_t f ≥ ε` a.e. Same template as `Linfty_contraction`.)
3. With `u_s ≥ ε > 0` a.e., `u_s^{q-1}` is in the smooth core (the
   functional calculus `x ↦ x^{q-1}` is C^∞ on `[ε, ∞)`). This *will*
   require a closure axiom like `IsCore_smooth_comp_of_pos`, but it's
   far weaker than full `IsCore_rpow_pos` and *does* hold for the
   natural Gaussian-instance cores: smooth-on-positive-reals
   composition preserves Schwartz / polynomial-tail cores in the
   ε-bounded regime.
4. Propagate `hf_pos` up to the final hypercontractivity assembly
   (`gross_lsi_implies_hypercontractive_of_hypotheses`).
5. Add an outer ε→0 step in that final assembly: replace generic
   `f ∈ Lp ℝ 2 μ` by `f_ε := f ∨ ε` (or similar), prove the
   hypercontractivity bound for `f_ε`, pass `ε → 0` via Fatou /
   monotone convergence to recover the bound for `f`.

**Cost:**

* ~30 LOC for the lower-bound contraction lemma (mirroring
  `Linfty_contraction`).
* ~1 new closure axiom on `IsCore` (or instance-level lemma) — far
  smaller than the full restructure of Path B.
* ~100–150 LOC for the ε→0 outer step in the final hypercontractivity
  assembly (standard approximation / Fatou).
* The `hf_pos` hypothesis propagates through ~4 signatures
  (`grossPow_pos`, `grossLogNorm_hasDerivWithinAt`,
  `grossLogNorm_antitoneOn`, `grossLogNorm_deriv_nonpos`); the ε→0
  step recovers the un-positivity-restricted theorem at the
  endpoint.

**Risks / known unknowns:**

* The exact form of the `IsCore_smooth_comp_of_pos` axiom (or
  weaker, like `IsCore_rpow_pos_strict : ∀ f core, (∀ x, ε ≤ f x) →
  ∀ r, IsCore (fun x => f x ^ r)`) needs to be chosen so that
  concrete Gaussian instances can discharge it. This is an
  instance-specific question; we'll know it works once
  `Gaussian1D` / `GaussianFin` discharge it.
* The ε→0 step at the end uses Fatou — needs `Lp ℝ 2 μ` topology
  + Markov-semigroup continuity to commute with `eLpNorm`. Standard
  but ~100 LOC.

### Path B — Architectural refactor

Gemini's preferred long-term design:

* Replace `IsCore` with the closed Dirichlet form domain
  `D(E) := IsFormDomain`, with Markovian field
  `u ∈ D(E) → u ⊓ 1 ∈ D(E)` and the contraction axiom.
* Define the generator via the form domain.
* Push smooth cores to per-instance implementation.

**Cost:** structural refactor of
[`Hypercontractivity.lean`](../MarkovSemigroups/Abstract/Hypercontractivity.lean)
+ restate of the relevant Gross theorems + per-instance form-domain
construction (each Gaussian instance needs Sobolev W^{1,2}-style
construction). Roughly ~500–1000 LOC of net new work spread across
the abstract structure and 3+ instances.

**Why we're not taking this now:**

1. The abstract framework is still in flux (Route A still has P3, W,
   Phase 4 to land).
2. Path A unblocks `grossPow_hasDerivWithinAt` immediately and
   matches Gross 1975's original proof structure.
3. The downstream consumer (`gaussian-hilbert`'s
   `HypercontractivityFromBE`) would need significant re-wiring under
   Path B.
4. Path B remains the morally correct long-term design and should
   be revisited after P3 / W / Phase 4 land (or as a separate
   refactor pass).

---

## 5. Decision

**Path A.** Documented here in §4. Will be executed in commits
following this doc.

Path B is acknowledged as the correct long-term design but
deferred — see [§7 of the parent structural-blockers
doc](grosspow-hasderivwithinAt-structural-blockers.md) for the
broader context.

---

## 6. Why this is publishable

The strictly-positive escape isn't a hack — it's the standard
textbook structure of Gross's 1975 proof. Mainstream sources
(BGL Ch 5, Gross's original paper, Davies *Heat Kernels and Spectral
Theory*) all prove hypercontractivity first for strictly positive
core elements and pass to the limit at the end. Doing the same in
the abstract framework just matches the textbook.

The `ε → 0` step is the place where the abstract framework needs
to know "P_t is L^p-continuous as p varies" in a precise sense, which
is itself a textbook lemma about Markov semigroups but worth
flagging.

---

## 7. The full query sent to Gemini

The full Gemini query (with the 4 claims, counterexample, sufficiency
question, regularity objection, and design alternative) is reproduced
verbatim in the session transcript at
`~/.claude/projects/-Users-mdouglas-Documents-GitHub-pphi2/`
(today's session, immediately preceding the `Gemini Deep Think
completed in 0m 28s` line). The verdict is in [§3 above](#3-gemini-verdict-summary).

---

## 8. Related docs

* [`plans/grosspow-hasderivwithinAt-structural-blockers.md`](grosspow-hasderivwithinAt-structural-blockers.md)
  — original blockers analysis (4 blockers; 3 of 4 now discharged).
* [`plans/gross-discharge.md`](gross-discharge.md) — Route A
  overall roadmap.
* [`plans/p2-strongL2-leibniz-discharge.md`](p2-strongL2-leibniz-discharge.md)
  — the now-discharged P2 Leibniz kernel.
