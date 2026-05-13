# Codex hand-off — Stage N1 (multivariate Gaussian BE instance) in markov-semigroups

**Updated 2026-05-12 (concrete pivot)**: the original brief called for a
generic `BakryEmerySpace.pi` tensorization lemma. Codex correctly
identified that the current `BakryEmerySpace` class exposes the
semigroup as a bare `(X → ℝ) → (X → ℝ)` operator with no kernel
representation, so a generic product-semigroup constructor is not
derivable without first refactoring the class (a multi-week project
out of scope here). The brief now targets a **concrete** instance.

**Updated 2026-05-13 (mid-N1 progress + bundle refactor)**: codex
has landed N1.0–N1.3 (IsCoreFin + closures, measure-side fields,
Γ/energy + DirichletSpace instance, semigroup fields zero/mean/contraction/
selfAdjoint/compose) plus the derivative bridge for N1.4
(`hasDerivAt_coordSection_ouSemigroupFin_C1`,
`section_deriv_ouSemigroupFin_eq`, `section_secondDeriv_ouSemigroupFin_eq`)
on branch `feat/bakry-emery-multivariate-gaussian` (commits `28962ea`,
`1711914`). Build is clean, 0 axioms, 0 sorries, 1371 lines so far.
Concurrently, **main** has received the Gross-API bundle refactor
(commits `6e4ad85`, `371780b`) introducing
`DirichletMarkovSemigroup`. Codex's branch has been rebased onto this
new main; the rebase was a 6-line adaptation.

**Remaining**: N1.4 `gradient_decay`, N1.5 L²/entropy decay fields +
`IsCore_semigroup`, N1.6 wrap into the `BakryEmerySpace (Fin n → ℝ)`
instance. Realistic remaining-line budget given the kernel-pushforward
infrastructure codex already invested in: ~700-900 more lines (final
file size ~2000-2300 lines), ~7-10 active days.

**Mission**: build the concrete multivariate Gaussian Bakry-Émery
instance `stdGaussianFin.bakryEmerySpace n : BakryEmerySpace (Fin n → ℝ)`
in **this repo** (`markov-semigroups`), using the explicit 1D Mehler
kernel from `EuclideanEntropyDecay.lean` and coordinate-by-coordinate
Fubini, so that downstream gaussian-hilbert can route
`ouSemigroupAct_eLpNorm_hypercontractive` through the bundled Gross
hypercontractivity machinery. **No new axioms.**

This is the long sub-stage of a three-stage discharge (N1 → N2 → N3).
Only N1 is in scope for this hand-off. N2 and N3 (~90 lines combined,
in gaussian-hilbert) will be done in a separate session after N1 merges.

All work happens in this repo (`~/Documents/GitHub/markov-semigroups`).
**Do not modify gaussian-hilbert** as part of this hand-off.

---

## Before you start: read these in order

1. **`docs/stage-n-detailed-plan.md`** (this repo) — the authoritative
   plan. Read all of Sub-stage N1 carefully (sections N1.0 through
   N1.6), the dependency graph, the verification checkpoints, and
   *especially* Risk 1, Risk 2, Risk 4.
2. **`~/Documents/GitHub/gaussian-hilbert/docs/stage-n-byproducts.md`**
   (sister repo) — context on what the instance is for and why we want
   the byproducts. Skim only.
3. **`MarkovSemigroups/Diffusion/CarreDuChamp.lean`** (this repo) —
   the `BakryEmerySpace` class definition you are instantiating. Read
   the whole file and list all 22 fields you need to fill.
4. **`MarkovSemigroups/Abstract/DirichletForm.lean`** (this repo) —
   the parent `DirichletSpace` class. You need its 13 fields too
   (they come via the `extends` clause).
5. **`MarkovSemigroups/Abstract/Hypercontractivity.lean`** (this repo,
   **POST-BUNDLE-REFACTOR**) — read the new `MarkovSemigroup` structure
   (line 76) and the bundled `DirichletMarkovSemigroup` (line 137).
   The Gross axioms now take `DirichletMarkovSemigroup` directly, with
   no separate `h_compatible`/`h_gen` side hypotheses. The new
   `MarkovSemigroup` has 4 extra structural fields the BE-instance's
   bare `semigroup` field doesn't directly provide: `conservation`
   (P_t 1 = 1), `positivity` (f ≥ 0 ⇒ P_t f ≥ 0), `symmetry`, and an
   `eLpNorm`-form contraction. **You don't need to wire these up
   inside `EuclideanFin.lean`** (N3 in gaussian-hilbert is responsible
   for building the `DirichletMarkovSemigroup` from your
   `BakryEmerySpace`), but you should be aware that downstream needs
   them when planning the BE-instance wrap (N1.6).
6. **`MarkovSemigroups/Instances/WorkInProgress/EuclideanEntropyDecay.lean`**
   (this repo) — the **current home** of the 1D `Gaussian1D.bakryEmerySpace`.
   Note that the 4 historical 1D BE axioms
   (`ouSemigroup_preserves_IsCore`, `ouSemigroup_gradient_decay`,
   `ouSemigroup_l2_sq_hasDerivWithinAt`,
   `ouSemigroup_entropy_sq_decay_bound`) **have been fully discharged**
   into proved theorems (commits `1b3f797`, `6a89298`, `00cd52b`,
   `ab36ab0`). The 1D BE instance is now axiom-free
   (`#print axioms Gaussian1D.bakryEmerySpace` shows only
   `propext, Classical.choice, Quot.sound`). The original
   `Instances/WorkInProgress/Euclidean.lean` no longer carries the
   load-bearing 1D axioms.
7. **`MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean`**
   (this repo, **your work in progress**) — re-read what's already
   built. The namespace is `GaussianFin` (parallel to `Gaussian1D`).
   N1.0–N1.3 are done; the derivative bridge for N1.4 has just landed
   (`hasDerivAt_coordSection_ouSemigroupFin_C1`,
   `section_deriv_ouSemigroupFin_eq`,
   `section_secondDeriv_ouSemigroupFin_eq`). Continue from there.
8. **`~/.claude/AXIOM_AUDIT_FORMAT.md`** (global) — the audit-doc
   conventions you must follow when updating
   `AXIOM_AUDIT.md` (top-level of this repo).

After reading, write a one-paragraph summary of what you understand
the remaining scope to be, and pause for confirmation before writing
code.

---

## Repository setup

- **Repo**: `~/Documents/GitHub/markov-semigroups`
- **Base branch**: `main` at `371780b` (head includes the bundle refactor).
- **Working branch**: `feat/bakry-emery-multivariate-gaussian` (already
  exists, pushed to origin, rebased on top of the bundle commit). The
  existing worktree is at
  `/private/tmp/markov-semigroups-bakry-emery-multivariate-gaussian`.
- **Build command**: `lake build` from the repo root.
- **Sister repo for downstream verification**: `~/Documents/GitHub/gaussian-hilbert`
  consumes this lemma but **do not modify gaussian-hilbert** as part of
  this hand-off — that's N2/N3 scope.

---

## Anti-delegation guards (READ THIS — non-negotiable)

A previous codex hand-off in this codebase (polynomial-density, 2026-05-10)
falsely "discharged" an axiom by replacing it with `:= by simpa using
upstreamAxiom` — i.e. just renaming the same axiom. **Do not do this.**

Specifically, the following patterns are **forbidden** and will be
rejected on review:

- **No `:= by exact` or `:= by simpa` delegations** that just forward to
  an upstream axiom or lemma with the same statement. If
  `BakryEmerySpace.pi` is "proved" by delegating to a single
  upstream lemma of essentially the same content, that's a false
  discharge.
- **No new `axiom` declarations** in `markov-semigroups` without
  explicit notification. If you genuinely cannot prove a field of the
  instance (e.g. Risk 2's entropy tensorization), **stop, write a
  diagnostic note in the PR description, and ask for guidance.** Do
  not silently add an axiom and continue. The exit ramp for entropy
  is documented in the plan's Risk 2.
- **No `sorry` left in committed code.** If a field is incomplete,
  either prove it or stop and report. (Temporary `sorry`s during
  development are fine; final commit must be sorry-free.)
- **No deletion or modification of existing axioms** in
  `Concentration.lean`, `Hypercontractivity.lean`, `CarreDuChamp.lean`,
  `DobrushinZegarlinski/`, `Matrix/`, or anywhere else. You are adding
  a new theorem, not refactoring existing ones. (Note: the 4
  historical 1D BE axioms in `Euclidean.lean` have *already been
  discharged* in main — do not look for them; they're proved theorems
  now in `EuclideanEntropyDecay.lean`, `EuclideanHermite.lean`,
  `EuclideanStein.lean`, etc.)
- **No "infrastructure" axioms added under the guise of definitional
  bridges.** If you find yourself wanting an axiom like
  `Function.update_section_eq` or `Measure.pi_comm`, search Mathlib
  first (`lean_local_search`, `lean_loogle`); these are likely
  already there.

When in doubt, **pause and report** rather than guess. The cost of
asking is 30 seconds; the cost of a silent bad axiom is days of audit
work.

---

## Deliverables

### 1. Existing file: `MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean`

**Status (2026-05-13)**: file exists on branch
`feat/bakry-emery-multivariate-gaussian` at 1371 lines, 0 axioms, 0 sorries.
Namespace is `GaussianFin` (parallel to `Gaussian1D`). N1.0–N1.3 plus
the derivative bridge for N1.4 are done. Continue from there.

**Sub-stage map** (with completion status):
- **N1.0 — IsCoreFin** ✅ DONE: definition + 9 helpers (contDiff, bound,
  measurable, stronglyMeasurable, partial_contDiff, partial_*).
- **N1.1 — measure-side fields** ✅ DONE: `γFin`, `IsCoreFin_const/add/smul/mul`,
  `partialDeriv_mul`, `partialDeriv_add`, `dirichletSpaceFin` (full
  `DirichletSpace` instance assembled).
- **N1.2 — Γ/energy fields** ✅ DONE: `ouGammaFin`, `ouEnergyFin`,
  `ouGammaFin_symm/nonneg/leibniz`.
- **N1.3 — semigroup fields** ✅ DONE: `ouSemigroupFin_zero/mean/contraction/
  selfAdjoint/compose` plus the kernel-pushforward infrastructure
  (`mixCLM`, `rotCLM`, `smulFinCLM`, `ou_kernel_map_fin`,
  `charFunDual_γFin`).
- **N1.4 derivative bridge** ✅ DONE (just landed):
  `hasDerivAt_coordSection_ouSemigroupFin_C1`,
  `section_deriv_ouSemigroupFin_eq`,
  `section_secondDeriv_ouSemigroupFin_eq` — the
  dominated-differentiation-under-the-Gaussian-integral chain used
  for N1.4's main calculation.
- **N1.4 — gradient_decay** ⏳ NEXT: coordinate decomposition
  `∫ Γ(P_t f) dγ_n = Σᵢ ∫∫... Γᵢ(P_t f-section, P_t f-section)...`,
  then per-i apply the 1D `ouSemigroup_gradient_decay` from
  `EuclideanEntropyDecay.lean` (note: this is now a **proved
  theorem**, not an axiom — call it directly). Sum to recover the
  `e^{-2t}` factor. Use the derivative bridge to compute the section
  derivatives. ~150-250 lines.
- **N1.5 — L²/entropy decay + IsCore_semigroup** ⏳: same
  coordinate-decomposition pattern using
  `ouSemigroup_l2_sq_hasDerivWithinAt` and
  `ouSemigroup_entropy_sq_decay_bound` (both proved theorems in
  `EuclideanEntropyDecay.lean`). Entropy decomposition uses
  `Ent_{γ_n}(g) = ∫ Ent_{γ}(g(·, x_¬i)) dγ_{¬i}` (conditional-entropy
  chain rule). Also prove preservation of `IsCoreFin` under
  `ouSemigroupFin`. ~250-350 lines.
- **N1.6 — wrap + smoke test** ⏳: assemble
  `def stdGaussianFin_bakryEmerySpace (n : ℕ) : BakryEmerySpace (Fin n → ℝ)`,
  smoke test at `n = 2`, `#print axioms` clean. Use a name that
  doesn't conflict with gaussian-hilbert's planned
  `stdGaussianFin.bakryEmerySpace` (which would be the re-export).
  ~50-100 lines.

The remaining-line budget is **~700-900 more lines** (final file
size ~2000-2300 lines). If you find yourself at 2500+ lines, something
has gone wrong — pause and report.

**Note on the discharged 1D axioms**: when you call into the 1D BE
machinery for the per-coordinate sub-bound, you are calling **proved
theorems**, not axioms. In particular `Gaussian1D.bakryEmerySpace.gradient_decay`,
`Gaussian1D.bakryEmerySpace.semigroup_l2_decay_bound`,
`Gaussian1D.bakryEmerySpace.semigroup_entropy_sq_decay_bound`,
`Gaussian1D.bakryEmerySpace.semigroup_l2_sq_hasDerivWithinAt` are all
available as fields of the 1D `BakryEmerySpace` instance — no axiom
names to invoke. (The historical 4 1D BE axioms were superseded by
commits `1b3f797`, `6a89298`, `00cd52b`, `ab36ab0` between
2026-05-09 and 2026-05-13.)

### 2. Library import root

Add an import for `MarkovSemigroups.Instances.WorkInProgress.EuclideanFin`
to the top-level library re-export module (likely `MarkovSemigroups.lean`
— verify by inspecting the existing module structure). One line.

### 3. Audit doc update: `markov-semigroups/AXIOM_AUDIT.md`

Add a row to the "Recently added" or equivalent section noting:
- Theorem: `stdGaussianFin.bakryEmerySpace` (and ancillary
  `γFin`, `ouSemigroupFin`, `ouGammaFin`, `IsCoreFin`, etc.)
- File: `MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean`
- What it proves: multivariate Gaussian BE instance with curvature 1
- That it adds **0 new axioms** (transitive deps: the 4 existing 1D BE
  axioms in `Euclidean.lean` + the 6 DirichletSpace inheritance axioms
  — both pre-existing)
- Used by (downstream): gaussian-hilbert's planned `stdGaussianFin_satisfiesLogSobolev`
  and ultimately the `ouSemigroupAct_eLpNorm_hypercontractive` discharge

Follow the format conventions in `~/.claude/AXIOM_AUDIT_FORMAT.md`.

### Note on future generalization

We deliberately ship a concrete instance now rather than a generic
`BakryEmerySpace.pi`. The generic version is blocked on a class refactor
(adding a kernel mixin or a tensor-product structure to `BakryEmerySpace`),
which deserves its own focused design pass — see
[`stage-n-detailed-plan.md`](stage-n-detailed-plan.md) "Future
generalization" section. **Do not** add a generic `BakryEmerySpace.pi`
on the side; it's intentionally out of scope.

---

## Sub-stage checkpoints (mandatory)

Build clean and `#print axioms` after each sub-stage. Report progress
after each. Do not move on if the previous sub-stage has a build error
or an unexpected axiom dependency.

| Checkpoint | Verification |
|---|---|
| After N1.0 (IsCoreFin + closure) | ✅ DONE |
| After N1.1 (measure-side fields) | ✅ DONE |
| After N1.2 (Γ/energy fields) | ✅ DONE |
| After N1.3 (semigroup fields) | ✅ DONE |
| After N1.4 derivative bridge | ✅ DONE (commits 28962ea, 1711914) |
| **After N1.4 gradient_decay** | **CURRENT TARGET** — partial instance has `gradient_decay` field filled, rest `sorry` |
| After N1.5 (L²/entropy fields + IsCore_semigroup) | all BE fields filled, **no `sorry`** |
| After N1.6 (wrap + smoke test) | `example : BakryEmerySpace (Fin 2 → ℝ) := stdGaussianFin_bakryEmerySpace 2` typechecks; `#print axioms` shows **only Mathlib core**: `[propext, Classical.choice, Quot.sound]` |
| Final | `lake build` clean on the entire markov-semigroups library |

If a checkpoint fails (e.g. you cannot fill `gradient_decay` cleanly),
stop and report. Do not "continue with a sorry" past a checkpoint.

---

## Tactical recommendations (from Gemini-vetted plan review)

These are domain-expert tips you should follow unless you have a good
reason not to:

1. **`IsCoreFin` formulation**: mirror the 1D `IsCore`:
   `ContDiff ℝ ⊤ f ∧ ∃ M, ∀ x, ‖f x‖ ≤ M ∧ ‖∂ᵢ f x‖ ≤ M ∧ ‖∂ᵢ∂ⱼ f x‖ ≤ M`
   (uniform bound on the function, all 1st partials, and all 2nd partials).
   This is simpler than the algebraic tensor closure for a concrete
   instance because we don't need general tensor functoriality.
2. **Multivariate Mehler formulation**: use the direct integral form
   `(P_t f)(x) = ∫ f(e^{-t}·x + √(1-e^{-2t})·y) dγ_n(y)` with `γ_n =
   Measure.pi (fun _ => gaussianReal 0 1)`. Fubini factors this into
   per-coordinate 1D Mehler integrals. Expect non-trivial effort on
   `AEStronglyMeasurable` lemmas for partially-integrated Mehler
   kernels — mechanical but tedious.
3. **`gradient_decay` proof**: prove `ouGammaFin.section_eq_1d` and
   `ouSemigroupFin.section_eq_1d` as named helper lemmas first
   (the just-landed derivative bridge gives you the latter), then the
   decay bound is a `∑ᵢ ≤ exp(-2t) · ∑ᵢ` coordinate-wise
   calculation reducing to the 1D gradient-decay field of
   `Gaussian1D.bakryEmerySpace`. The 1D fact is now a **proved
   theorem** (the historical axiom `ouSemigroup_gradient_decay` was
   discharged in commit `6a89298`), accessible as
   `Gaussian1D.bakryEmerySpace.gradient_decay` or via the
   `BakryEmerySpace` interface.
4. **Entropy decay (Risk 2)**: if it stalls past 1.5 days, **stop**.
   The exit ramp is to factor `entropy_tensorize_le` as a clearly-named
   helper lemma that is either proved or reported as needing further
   work — but DO NOT add it as an axiom without explicit notification.
   Note: on product measures the inequality is actually *equality* in
   the form `Ent_{γ_n}(g) = ∫ Ent_{γ}(g_section) dγ_{¬i}` after the
   right coordinate decomposition; this is conditional-entropy chain
   rule, not a Gross-style tensorization shortcut.
5. **Measurability**: Mathlib's `MeasureTheory.integral_prod` requires
   `AEStronglyMeasurable`; for the Mehler integrand
   `f(e^{-t}·x + √(1-e^{-2t})·y)` with `f` continuous, this follows
   from `Continuous` on the inner shifted argument. Search for
   `Measurable.pi`, `Continuous.measurable`, or
   `AEStronglyMeasurable.prod_mk` if you get stuck.

---

## What NOT to touch

- `MarkovSemigroups/Abstract/*.lean` — the abstract framework. Read but
  do not modify. **Do not** add a kernel mixin or a generic
  `BakryEmerySpace.pi` here; the class refactor is out of scope (see
  "Note on future generalization" above). In particular, the bundled
  `DirichletMarkovSemigroup` in `Abstract/Hypercontractivity.lean`
  (lines 137+) is finalized — do not edit it.
- `MarkovSemigroups/Diffusion/CarreDuChamp.lean` — the parent
  `BakryEmerySpace` class definition. Do not modify.
- `MarkovSemigroups/Instances/WorkInProgress/Euclidean.lean`,
  `EuclideanEntropyDecay.lean`, `EuclideanHermite.lean`,
  `EuclideanStein.lean` — the 1D instance and its supporting files.
  Read carefully (especially for the API of
  `Gaussian1D.bakryEmerySpace.gradient_decay /
  semigroup_l2_decay_bound / semigroup_l2_sq_hasDerivWithinAt /
  semigroup_entropy_sq_decay_bound`) but do not modify any of the
  existing theorems or definitions.
- `MarkovSemigroups/Matrix/`, `MarkovSemigroups/DobrushinZegarlinski/`,
  `MarkovSemigroups/Concentration/` — out of scope.
- Anything in `~/Documents/GitHub/gaussian-hilbert` — that's N2/N3
  scope.
- `lake-manifest.json`, `lakefile.lean`, toolchain files — leave alone.

---

## Final reporting

When you finish (or hit a checkpoint failure), report:

1. **Final commit hash** on `feat/bakry-emery-multivariate-gaussian`.
2. **Worktree path** so the diff can be reviewed.
3. **`#print axioms` output** for `GaussianFin.stdGaussianFin_bakryEmerySpace`
   (or whatever the final BE-instance binding is called). Expected:
   ```
   axioms it depends on: [propext, Classical.choice, Quot.sound]
   ```
   *Only* Mathlib core. The 4 historical 1D BE axioms were already
   discharged in main, so the multivariate instance is downstream of
   a fully-proved 1D chain — no markov-semigroups axiom should appear.
   **Anything else is unexpected and must be flagged.**
4. **Build status**: `lake build` output, full clean expected.
5. **Line counts**: per-section line count for `EuclideanFin.lean` (so
   we can verify the ~2000-2300 final budget held).
6. **Any deviations from the plan**: if you had to inline a helper,
   skip a sub-section, or invoke an unexpected Mathlib lemma, say so
   explicitly. Particularly important: flag if any field's proof
   required substantive new mathematical input (vs mechanical Fubini
   reduction to a 1D fact).

If any checkpoint **failed**, stop and report the failure with:
- Which sub-stage and which field
- The current proof state Lean shows
- What you tried
- What Mathlib API you searched and didn't find

Do not push partial-but-broken work to the branch.

---

## Suggested invocation

```
/codex:rescue --background --model gpt-5.4-thinking --effort high
  Read docs/stage-n1-codex-brief.md in markov-semigroups and execute
  it against ~/Documents/GitHub/markov-semigroups. Anti-delegation
  guards are strict.
```

Use `--effort high` for the substantial Fubini reasoning; this is
not a routine refactor.
