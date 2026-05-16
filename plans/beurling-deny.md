# Beurling–Deny decomposition: finite case proved, general case axiomatized

**Status:** scoped, not started (as of 2026-05-16).

**Goal:** formulate the Beurling–Deny decomposition of a (regular)
Dirichlet form, **prove the finite-state case sorry-free**, and
**axiomatize the general case** as a single vetted existence axiom,
with the finite case certified as a literal instance of the same
predicate.

**Cross-repo scope:** internal to `markov-semigroups`. The *criteria*
strand (target 1, semigroup characterization) is deliberately **out of
scope** — see "Decoupled" below.

**Estimated total:** ~250–400 lines, ~3–6 active days (finite math is
elementary; cost is API design + axiom vetting + the consistency
corollary's measure plumbing).

---

## Background & target

Beurling–Deny / LeJan (Fukushima–Oshima–Takeda, *Dirichlet Forms and
Symmetric Markov Processes*, 2nd ed., **Thm 3.2.1**): a regular
Dirichlet form decomposes, for core `u,v`, as

    E(u,v) = Eᶜ(u,v)                                  -- strongly local (diffusion)
           + ∬_{X×X∖Δ} (u(x)-u(y))(v(x)-v(y)) dJ      -- jump
           + ∫_X u·v dk                               -- killing

with `Eᶜ` strongly local, `J` a symmetric Radon measure off the
diagonal, `k` a Radon measure. The LeJan refinement (Thm 3.2.2)
representing `Eᶜ` via the energy measure is **explicitly out of scope**
(separable, much heavier — needs the carré-du-champ-as-measure upgrade
of `Diffusion/CarreDuChamp.lean`).

Reference access: FOT §3.2 — local copy in
`refs/Fukushima-Oshima-Takeda-2011-dirichlet-forms-symmetric-markov-processes-2ed.pdf`
(institutional access; untracked). **Exact location (body-verified):
Ch. 3 §3.2 "Formulae of Beurling–Deny and LeJan"; Thm 3.2.1 stated
top of p. 120, proof pp. 120–123 (uniqueness, J as vague limit,
construction of k and Eᶜ); LeJan energy measure μ⟨u⟩ + Lemmas
3.2.1–3.2.2 pp. 123–130 (the out-of-scope refinement).** Chapter
summary: `refs/summaries/Fukushima-Oshima-Takeda/03-scope-of-dirichlet-forms.md`.
The Γ-calculus context is in Ledoux's free 2000 NUMDAM survey
(`refs/Ledoux-2000-*.pdf`); the LeJan energy-measure refinement
corresponds to Cor 4.3 / §1 there.

## Why finite + axiom (not full proof)

The full theorem sits behind two walls with **no sister-project
shortcut**: Kato form-representation and capacity / quasi-continuity
theory (neither in Mathlib; `kato`, `quasi.continuous` = 0 hits across
all our catalogs). The finite case carries the entire *algebraic*
content of the theorem with none of the analysis, so it illustrates
the general statement and de-risks the formulation, while the general
case is honest axiom debt.

**Decoupled:** the Beurling–Deny *decomposition* (this plan) is
form-intrinsic and needs **no** spectral theory. The *criteria*
(target 1: positivity-preserving ↔ contractions operate) do need the
unbounded spectral theorem — to be **consumed**, not reformalized,
from M. Cipollina's quantumlib (~13k LOC, ~ITP June 2026; see memory
`quantumlib-unbounded-spectral-theorem`). Not part of this plan.

## Design decisions (locked)

- **Placement:** new `MarkovSemigroups/Abstract/BeurlingDeny.lean`,
  next to `DirichletForm.lean`. Reuses `Matrix/HeatKernel.lean`
  (`IsZMatrix`, `IsEntryNonneg` API) for the finite sign content.
- **Structured def + one axiom.** Define one predicate
  `IsBeurlingDenyDecomposition E Eᶜ J k` (representation eqn + jump
  symmetry + strong-locality of `Eᶜ`). General case = single existence
  `axiom` over a regular Dirichlet form. Finite theorem proves the
  *same* predicate.
- **Measure API:** Mathlib `Measure (X × X)` (jump), `Measure X`
  (killing) — only stated in the axiom, not constructed. `Eᶜ` kept
  abstract as a strongly-local symmetric form (`Prop`: vanishes when
  one argument is constant near the other's support). This is exactly
  FOT 3.2.1.
- **Markov property** enters as a `Prop` mixin **hypothesis**, never a
  `DirichletSpace` class field (the class has no Markov field; adding
  one is rejected per def-study leaf-placement guardrails).
- **Finite theorem + consistency corollary** (both sorry-free).

## Phases

### Phase 1 — Pure-matrix Beurling–Deny identity (~80 lines, 1 day)
The reusable core, **no Markov hypothesis**. For symmetric
`Q : Matrix X X ℝ` (`Fintype X`, `DecidableEq X`), set
`c x y := - Q x y`, `k x := ∑ y, Q x y`. Prove for all `u v : X → ℝ`:

    ∑ x, ∑ y, u x * Q x y * v y
      = (1/2) * ∑ x, ∑ y, (if x = y then 0 else c x y)*(u x-u y)*(v x-v y)
      + ∑ x, k x * u x * v x

Proof: `Finset.sum` reindex (swap `x↔y` in cross terms, use symmetry)
+ `ring`. Algebraic identity verified by hand in the design
discussion. Also prove **uniqueness** of `(c,k)` given the form
(c from off-diagonal, k from row sums).

### Phase 2 — Finite positivity (~40 lines, 0.5 day)
Under the finite Markov / Z-matrix hypothesis (`HeatKernel.IsZMatrix Q`,
i.e. `Q x y ≤ 0` for `x ≠ y`, plus nonneg row sums `0 ≤ k x` for the
no-negative-killing condition): conclude `0 ≤ c x y` and `0 ≤ k x`,
so they are genuine (jump / killing) weights. Reuse HeatKernel API.

### Phase 3 — General predicate + axiom (~50 lines, 0.5 day)
`structure IsBeurlingDenyDecomposition` (representation integral eqn,
`J` swap-invariant, `Eᶜ` strongly local). `IsRegularDirichletForm`
predicate stated faithfully per FOT (core dense in form-norm and
sup-norm) even though instances are not yet provable — must be
non-vacuous (axiom-protocol red-flag check). Then:

    axiom beurling_deny_decomposition :
      IsRegularDirichletForm E → ∃ Eᶜ J k, IsBeurlingDenyDecomposition E Eᶜ J k

Full docstring: FOT Thm 3.2.1 citation, 3-line strategy, `(NOT
VERIFIED)`, LeJan-out-of-scope note.

### Phase 4 — Consistency corollary (~60 lines, 1 day)
`Fintype X`: feed Phase-1/2 `c,k` as `J := weighted counting measure on
X×X∖Δ`, `k := ∑ Dirac`, `Eᶜ := 0`, and prove
`IsBeurlingDenyDecomposition E 0 J k`. Certifies finite-X as a literal
instance of the general predicate (the "illustrates the general
theorem" payoff). Risk: finite-measure ↔ finite-sum integral plumbing
(`Measure.sum`, `integral_dirac`, `lintegral`/`integral` over
`Fintype`). Stage as separate lemma if it balloons.

### Phase 5 — Vetting & bookkeeping (~0.5 day)
- Gemini `deep_think_gemini` vetting of the axiom (typed correctly /
  strong enough for FOT 3.2.1 / non-vacuous / hypotheses sufficient),
  per `~/.claude/CLAUDE.md` axiom protocol. Optionally Codex literature
  search for an existing formalization.
- Add `AXIOM_AUDIT.md` row (`Sources: DT[, GR]`, rating, FOT 3.2.1
  note). Bump axiom count in `README.md` "Current Status" in the same
  commit.
- `lake build` green; `#print axioms` on finite theorems shows only
  `Classical.choice/propext/Quot.sound` (no leakage of the BD axiom
  into the finite results).

## Risks

- **Phase 4 measure plumbing** — main Lean risk; the finite math is
  trivial but `Measure`-valued integrals over a `Fintype` can be
  fiddly. Mitigation: prove the integral-to-sum reduction as a
  standalone lemma first; fall back to "Phase 4 deferred, prose
  correspondence only" if it exceeds ~1 day.
- **Axiom vacuity** — `IsRegularDirichletForm` must encode real FOT
  content, not a placeholder, or the audit rejects it. Mitigation:
  state regularity as the genuine density condition; accept that no
  instance is provable yet (debt, not vacuity).
- **`∀ f, IsCore f` gap** — `DirichletSpace` does not give all
  functions core; the finite bridge takes `hcore : ∀ f, ds.IsCore f`
  as an explicit hypothesis (true for the finite instance). Keep the
  pure-matrix lemma `DirichletSpace`-free so it is reusable regardless.

## Done = 
`lake build` green; finite theorem + uniqueness + positivity +
consistency corollary sorry-free; one vetted axiom recorded in
`AXIOM_AUDIT.md` + `README.md`; `#print axioms` clean on the finite
results. Then move this file to `plans/archive/` and add a
`plans/history.md` entry.
