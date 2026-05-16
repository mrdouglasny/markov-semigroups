# Discharging the Gross axiom — route decision + corrected Route A

**Status:** scoped, not started. **Vetting trail (2026-05-16):**
Gemini deep-think pass 1 found two analytical traps + the route
misjudgment (folded in: weak-L² difference quotients; S–V as
hypothesis; hille-yosida bridge). Gemini pass 2 **green-lit for Codex
handoff** subject to 4 fixes — all now applied: (1) deleted the
right-derivative-only constraint, two-sided interior via the
hille-yosida bridge; (2) integrability discharged free from the
structural `hμ : IsProbabilityMeasure μ` (`L^∞⊂L²⊂L¹`); (3) `ε≤P_tf≤M`
derived from existing `P_positivity`+`P_conservation`, not a bespoke
field; (4) `Done =` already Route-A. Gemini explicitly endorsed
S–V-as-hypothesis as the correct Lean 4 pattern. **Next: re-vet the
concrete `generator_compat` statement (0b) with Gemini before
engineering.**

**Recommendation (revised 2026-05-16 per user directive "we want the
most general result which is feasible"): execute the corrected
Route A** — the abstract BGL §5.2 theorem on
`DirichletMarkovSemigroup`, with a `hille-yosida` generator bridge and
`stroock_varopoulos` as a theorem hypothesis. This is the *most general
feasible* deliverable and **also unblocks pphi2** (the GaussianFin
instance discharges the S–V hypothesis with the cheap concrete Gaussian
chain rule). Route B
([`gaussian-ou-hypercontractivity.md`](gaussian-ou-hypercontractivity.md))
is demoted to **fallback** (sound, but yields *no general result* —
only the Gaussian instance).

**Why this is "most general feasible," precisely.** Three generality
tiers: (1) concrete Gaussian (Route B) — not general; (2) abstract
symmetric-Markov Dirichlet form with S–V as bundled data (this plan) —
general, = the textbook BGL theorem; (3) abstract with S–V *derived*
from a carré-du-champ / Beurling–Deny representation — strictly more
general but **infeasible/circular here** (the repo axiomatizes
Beurling–Deny; cf. [`beurling-deny.md`](beurling-deny.md)). Tier 2 is
the maximum feasible. Carrying S–V as a theorem hypothesis is *not* a generality
compromise — every symmetric Markov Dirichlet form satisfies it, so
requiring it is how the general theorem is correctly stated; only the
*proof obligation* is deferred to instances (Gaussian: ~10 lines).

**Goal (unchanged):** remove `gross_lsi_implies_hypercontractive`
([`Abstract/Hypercontractivity.lean:269`](../MarkovSemigroups/Abstract/Hypercontractivity.lean))
from the live pphi2 axiom chain.

---

## Route decision (corrected)

My original Route-A justification — "Route B requires re-plumbing
gaussian-hilbert" — was a **false economy** (Gemini, correct):

- `gaussian-hilbert`'s `ouSemigroupAct_eLpNorm_hypercontractive`
  (`HypercontractivityFromBE.lean:314`) is a **theorem with a fixed
  signature**. Whether its *proof* invokes the abstract Gross axiom or
  a concrete Route-B theorem is internal to that one file. Swapping it
  is a localized change; `PolynomialChaosConcentration` and **pphi2
  are untouched** (they consume only the theorem's type).
- In the concrete Mehler-kernel setting of Route B, **both Route-A
  analytical traps evaporate**: pointwise `t`-derivatives under the
  integral are legitimate (explicit smooth kernel), and
  Stroock–Varopoulos is a ~10-line application of the spatial chain
  rule for the explicit Gaussian Dirichlet form `∫∇u·∇v dγ`.

Route B's total cost (the ~1900–3200-line concrete Gaussian Gross
build) is unchanged and real; but it is **sound**, whereas Route A is
analytically much harder at the abstract carrier (below). Net: Route B
for pphi2; Route A only if the *general* abstract theorem is wanted
for its own sake (e.g. Mathlib upstreaming).

---

## `hille-yosida` leverage (project dependency)

The `hille-yosida` dep (`StronglyContinuousSemigroup`,
`ContractingSemigroup`, generator, `resolvent`,
`hilleYosidaResolventBound`) **materially de-risks Route A, but only
for two of the three traps**:

- **Trap 3 — dissolved.** With a genuine C₀ generator `A`, for
  `f ∈ D(A)` the orbit `t ↦ P_t f` is *two-sided* differentiable for
  `t > 0` with `d/dt P_t f = A P_t f` (one-sidedness is only at
  `t=0`). The right-derivative-only restriction was an artifact of
  the fragile 0⁺-bootstrap, **not** intrinsic. Using hille-yosida's
  generator gives genuine `HasDerivAt` for `t > 0`.
- **Trap 1 — downgraded from "hallucination" to "standard".** The
  generator gives the *linear* orbit derivative rigorously and the
  form duality `⟨φ, A g⟩ = -E(φ, g)` on the core. The Gross
  computation `d/dt ∫(P_tf)ᵍ = q'∫uᵍ log u + q∫u^{q-1}·A u` then
  proceeds at the *form* level — exactly the standard BGL §5.2
  argument, not the unprovable pointwise route. The residual
  difficulty (justifying `d/dt` through the integral for the
  *nonlinear* `(·)ᵍ`) remains and still needs the difference-quotient
  / convexity handling — hille-yosida does **not** remove Phase 2's
  bottleneck, it makes it standard rather than a trap.
- **Trap 2 — unaffected.** S–V is nonlinear / carré-du-champ-kernel
  structure, orthogonal to linear C₀-semigroup theory. hille-yosida
  gives `A` and the resolvent, not the pointwise convexity
  representation. S–V stays a theorem hypothesis (Phase 0).

**Precondition (real cost):** this leverage requires actually wiring
`DirichletMarkovSemigroup` to hille-yosida's
`StronglyContinuousSemigroup` — generator `A`, `core ⊆ D(A)`, and the
form duality `⟨g, A h⟩ = -E(g,h)`. `L2Semigroup.lean` is currently an
explicit *stub* for exactly this bridge; building it is a Phase-0-
scale undertaking, but on firm, reusable footing rather than a
0⁺-bootstrap. Net effect: Gemini's "abort Route A" is **too strong** —
with hille-yosida, Route A's Phases 0/1 collapse to a standard
generator bridge and Trap 3 vanishes. Route B is still preferred for
pphi2 (Trap 2 + the Phase-2 nonlinear bottleneck remain either way,
and Route-B consumption is cheap), but Route A is materially less
infeasible than the abstract framing suggested.

## Gemini-identified traps in the original Route-A plan

These corrections are folded into the Route-A spec below. They are
*not* shallow — each matches established practice in this repo.

1. **No pointwise `t`-differentiation of an abstract orbit.** An
   abstract symmetric Markov semigroup gives *strong* (L²-norm)
   differentiability of `t ↦ P_t f`, never pointwise-a.e.-in-`x`.
   `hasDerivAt_integral_of_dominated_loc_of_deriv_le` is unusable
   here. Use **weak-L² difference quotients + the convexity bound
   `xᵍ − yᵍ ≤ q·x^{q-1}(x−y)}`** to decouple the moving exponent from
   the orbit and trigger the weak energy-form definition.
2. **Stroock–Varopoulos cannot be proved at the abstract carrier.**
   The pointwise S–V proof needs an *integral representation* of the
   Dirichlet form — i.e. the **Beurling–Deny decomposition**
   ([`beurling-deny.md`](beurling-deny.md)), which this repo
   axiomatizes. Proving S–V abstractly is circular. It must remain a
   structural field / hypothesis (which is why it is already an
   axiom). **Original Phase 4 deleted.**
3. **(Resolved by the hille-yosida bridge — NOT right-derivative
   only.)** The *original 0⁺-bootstrap* idea yielded only
   `HasDerivWithinAt … (Set.Ici t)`. But Phase 0c uses hille-yosida's
   genuine C₀ generator, which gives a **two-sided `HasDerivAt` for
   every `t > 0`** (one-sidedness only at `t=0`, which the interior
   ODE never touches). Gemini point 1 (accepted): the earlier
   "target right-derivatives only / `antitone_on_of_hasDerivWithinAt_nonpos`"
   instruction is **deleted** — it contradicted the bridge and would
   needlessly complicate Phase 2/3's product & chain rules. Use
   standard two-sided `deriv` on the interior; right value at `t=0` is
   only the boundary. `IsCore_semigroup` remains required (answers the
   original design question: sufficient).

---

## Corrected Route-A spec (the harder, abstract option)

### Phase 0 — `L2Semigroup`→hille-yosida bridge + structure augmentation

`L2Semigroup.lean` is today a **pure stub**: it works only at the
*function* level (`BakryEmerySpace.semigroup : X→ℝ`), has **no
hille-yosida import or usage**, and merely restates the Γ energy
identity. The bridge is built from scratch. Three sub-phases + the
remaining fields.

API facts (verified 2026-05-16 vs `.lake/packages/HilleYosida`):
hille-yosida exposes `StronglyContinuousSemigroup`/`ContractingSemigroup`
(`operator : ℝ → X →L[ℝ] X`, `at_zero`, `semigroup`, `strong_cont`,
`contracting`); `.generator x : Prop` = ∃ Ax, **right** difference
quotient `(1/t)•(S t x − x) → Ax` over `𝓝[>] 0`; `.domain` (Submodule),
`.generatorMap`, `semigroup_maps_domain`, `semigroup_generator_comm`,
`ContractingSemigroup.resolvent`, `hilleYosidaResolventBound`. It does
**not** package any `HasDeriv*` for `t ↦ S t x` — only the right
difference-quotient + the commutation `A(S t x) = S t (A x)`.

#### 0a — Semigroup repackaging (cheap; fields already line up 1:1)

`MarkovSemigroup`'s fields map directly onto `ContractingSemigroup
(Lp ℝ 2 S.μ)`: `P_zero↔at_zero`, `P_semigroup↔semigroup`,
`P_strong_cont↔strong_cont`, `P_contraction↔contracting` (the field
is `P_contraction`, not `P_l2_contraction`).
Deliverable: `def MarkovSemigroup.toContractingSemigroup :
HilleYosida.ContractingSemigroup (Lp ℝ 2 S.μ)`, modulo coercion/defeq.
**~50–120 lines, 1–2 d. Low risk.**

#### 0b — Form↔generator identification (the crux; a Kato-family problem)

hille-yosida's `.generator` needs **strong (norm)** convergence;
`energy_eq_deriv` only gives a **weak, scalar-paired 0⁺ derivative**
`(d/ds)|₀₊ ⟨[f],P_s[g]⟩ = -E(f,g)`. Upgrading weak-form ⇒
strong-generator-membership with `core ⊆ domain(A)` and
`⟨[g],A[f]⟩_{L²} = -E(g,f)` **is essentially Kato's first
representation theorem** — the same form↔operator gap flagged for
Beurling–Deny ([`beurling-deny.md`](beurling-deny.md)) and the
quantumlib dependency (memory `quantumlib-unbounded-spectral-theorem`).
**Not feasible to derive abstractly here.**

Resolution (project precedent: `energy_eq_deriv` is *already* a
postulated compatibility field): **replace `energy_eq_deriv` with a
strengthened `generator_compat`**, discharged **per instance**
(GaussianFin: explicit OU generator `A f = f″ − x·f′`). Proposed
statement — mirrors the existing `coreToL2`/`⟪·,·⟫_ℝ` idiom and
hille-yosida's `.generator` filter *verbatim*:

```lean
/-- Generator–form compatibility (STRONG form). Strengthens
`energy_eq_deriv`: `coreToL2 f ∈ dom(A)` with the difference
quotient converging in **L²-norm** (not merely weakly), and the
generator value `Af` pinned by the form against every core test
function. The Kato obligation, postulated; discharged per instance. -/
generator_compat : ∀ {f : X → ℝ} (hf : IsCore f),
  ∃ Af : Lp ℝ 2 μ,
    Filter.Tendsto
      (fun t : ℝ => (1 / t) • (P t (coreToL2 hf) - coreToL2 hf))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds Af)
    ∧ ∀ {g : X → ℝ} (hg : IsCore g),
        ⟪coreToL2 hg, Af⟫_ℝ = - energy g f
```

Notes for the Gemini soundness pass:
- Sign: `A` = generator (`lim (P_t−I)/t`); the form's nonneg
  self-adjoint operator is `−A`, so `⟨g,Af⟩ = −E(g,f)` — consistent
  with `energy_eq_deriv`'s sign and `P_symmetric` (`energy_symm` ⇒
  `⟨g,Af⟩=⟨f,Ag⟩` on core).
- **`generator_compat ⇒ energy_eq_deriv`**: pair the strong limit
  with `coreToL2 hg` through the continuous functional
  `⟪coreToL2 hg, ·⟫_ℝ`; so `energy_eq_deriv` becomes a derived
  corollary (drop it from the structure).
- Uses hille-yosida's *exact* filter `nhdsWithin 0 (Set.Ioi 0)` and
  quotient, so `.generator`, `semigroup_maps_domain`,
  `semigroup_generator_comm` apply with zero re-derivation.
- `[IsProbabilityMeasure μ]` is **already** a structure field
  (`MarkovSemigroup.hμ`, an `instance`); the `⟪·,·⟫_ℝ` pairing of an
  L^∞-bounded test function is therefore automatically well-defined.

**Field + GaussianFin discharge: ~150–300 lines, 3–5 d. Phase 0's
make-or-break risk** — vet *this statement* before engineering.

#### 0c — Derivative-at-`t` lemma (hille-yosida lacks it)

From `semigroup_maps_domain` + `semigroup_generator_comm` +
`generator_compat`, derive a **two-sided**
`HasDerivAt (fun t => ⟪coreToL2 hφ, S.P t (coreToL2 hf)⟫_ℝ)
(-(energy φ (P_t f))) t` for every **`t > 0`** (`φ,f` core). Gemini
point 1 (accepted): the hille-yosida bridge gives genuine two-sided
differentiability on the interior — **do not** restrict to
right-derivatives there; that only complicates Phase 2's product/
chain rule with needless `derivWithin`/`Set.Ici` juggling. The
one-sided right value is needed *only* at the boundary `t = 0`, which
the interior ODE never touches. hille-yosida packages
maps-domain/comm but **not** this `HasDeriv*` — a genuine deliverable.
**~200–400 lines, ~1 wk.**

#### 0d — Remaining structural change

Besides replacing `energy_eq_deriv` with `generator_compat` (0b),
only **one** genuinely new field is needed:
- `IsCore_semigroup : ∀ t, 0 ≤ t → ∀ {g}, IsCore g → IsCore (P t g)`

The `ε ≤ P_t f ≤ M` bound is **not** a bespoke field (Gemini point 3,
accepted): derive it as a ~3-line lemma from the *existing*
`P_positivity` + `P_conservation` (`P_t 1 = 1`) —
`f − ε·1 ≥ 0 ⇒ P_t(f − ε·1) ≥ 0 ⇒ P_t f ≥ ε·1`, dually `≤ M`. Keeps
`DirichletMarkovSemigroup` Mathlib-standard.

**Stroock–Varopoulos: a hypothesis to the theorem, NOT a structure
field** (Trap 2 — cannot be proved abstractly; would need the
Beurling–Deny representation). Design decision (def-study
leaf-placement): `gross_lsi_implies_hypercontractive` takes an
explicit `h_sv : StroockVaropoulos D` argument. Rationale: a DMS is a
valid DMS without S–V; only the Gross implication needs it, so
bundling it onto the structure would burden every construction
needlessly and reduce generality of the structure. Instances satisfy
`h_sv` at the call-site — GaussianFin via the ~10-line explicit
Gaussian chain rule; the existing `stroock_varopoulos` axiom supplies
it generically in the meantime. *Alternative:* a bundled
`IsStroockVaropoulos` mixin class — adopt only if S–V gains multiple
independent consumers.

Every instance must fill the two new fields (GaussianFin uses
`ouSemigroupFin_preserves_IsCore` + explicit bounds). **~150–250
lines + fixups, 3–5 d.**

### ~~Phase 1~~ — subsumed by Phase 0c

The original Phase 1 (`HasDerivWithinAt (fun t => ⟨φ,P_t g⟩)
(-E(φ,P_{t₀}g)) (Set.Ici t₀)` via a fragile `energy_eq_deriv` 0⁺
**bootstrap**) is replaced by **Phase 0c**, which derives the same
two-sided interior derivative directly from the hille-yosida generator
(`semigroup_generator_comm` + `generator_compat`). Cleaner and on firm
C₀-semigroup footing rather than a bootstrap.

### Phase 2 — Weak-L² difference-quotient derivative (the bottleneck)

`d/dt N(t)` (**two-sided, `t > 0`** — Gemini point 1) via difference
quotients, **not** pointwise differentiation under the integral.
Split the increment `∫(P_{t+h}f)^{q(t+h)} − ∫(P_t f)^{q(t)}` into (i)
an exponent difference at fixed spatial function (1D calculus) and
(ii) an orbit difference bounded by the convexity inequality
`xᵍ − yᵍ ≤ q·x^{q-1}(x−y)}`, whose `h→0` limit is the weak energy
form `−q·E(uᵍ⁻¹·…)` via **Phase 0c**.

*Integrability is free here* (Gemini point 2, accepted): with the
structural `hμ : IsProbabilityMeasure μ`, `L^∞(μ) ⊂ L²(μ) ⊂ L¹(μ)`,
so the L²-bounded `u^{q-1}` (Phase 0d markov bound) pairs validly and
`∫ log u` is finite — zero generality cost (LSI is a probability-
measure notion; pphi2's Gaussian space is one). eLpNorm↔`(∫·ᵍ)^{1/q}`
bridge as before. **~700–1300 lines, 2–4 wk.**

### Phase 3 — Algebraic closure (monotonicity)

Phase 2 ⊕ LSI ⊕ S–V hypothesis ⊕ `q'=2ρ(q-1)` ⇒ `d/dt log N ≤ 0` on
`(0,∞)`; then `N` is `AntitoneOn [0,∞)` via continuity on the closed
ray (strong continuity + the Phase-0d bounds) + nonpositive *two-sided*
interior derivative (Mathlib `antitoneOn_of_deriv_nonpos`-style — **no**
`derivWithin` juggling); ⇒ `N(t) ≤ N(0)`; unwrap to
`IsHypercontractive` (`0<ρ` firewall). **~200–400 lines, 3–5 d.**

### ~~Phase 4~~ — deleted (Trap 2)

S–V is a theorem hypothesis (Phase 0), discharged by concrete
instances. Abstract proof would require the Beurling–Deny
representation — circular here.

---

## Summary

| Phase | Deliverable | Lines | Time |
|---|---|---|---|
| 0a | `MarkovSemigroup.toContractingSemigroup` (repackage) | 50–120 | 1–2 d |
| 0b | `generator_compat` field (Kato-factored) + GaussianFin discharge | 150–300 | 3–5 d |
| 0c | derivative-at-`t` lemma (**subsumes old Phase 1**) | 200–400 | 1 wk |
| 0d | `IsCore_semigroup` field (ε≤·≤M derived, not a field) | 60–120 | 2–3 d |
| 2 | weak-L² two-sided difference-quotient derivative | 700–1300 | 2–4 wk |
| 3 | monotonicity (two-sided interior) → `IsHypercontractive` | 200–400 | 3–5 d |
| **Route A total** | S–V a theorem hypothesis (instance-discharged) | **~1380–2670** | multi-week |

Old "Phase 1" (0⁺-bootstrap of the generator–form identity) is
**subsumed by Phase 0c**: the hille-yosida generator replaces the
fragile bootstrap.

## Risks

- **Phase 0b is the make-or-break risk.** The weak-form ⇒
  strong-generator upgrade is a Kato-family form-representation
  problem, infeasible to *derive* abstractly. Mitigation: factor it as
  the postulated `generator_compat` field (project precedent:
  `energy_eq_deriv`), discharged per instance. If even the
  *per-instance* GaussianFin discharge proves hard, the OU generator
  is fully explicit there, so it remains tractable — but this is the
  one sub-phase to **Codex/Gemini-vet before engineering** (the
  field's exact statement: strong vs weak, domain core, symmetry).
- Phase 0 is a **breaking structure change** rippling to every
  `DirichletMarkovSemigroup` instance (GaussianFin via
  `ouSemigroupFin_preserves_IsCore` + explicit OU generator).
- Phase 2 stays the analytical bottleneck (standard BGL §5.2 given
  0b/0c, but heavy Lean plumbing).
- Discharging Gross still leaves the **3 GaussianFin axioms** on the
  pphi2 chain (LSI/BE-instance inputs); tracked in `AXIOM_AUDIT.md`.

## Done =

`gross_lsi_implies_hypercontractive` is a theorem on the augmented
`DirichletMarkovSemigroup` (S–V as hypothesis); the GaussianFin
instance discharges `generator_compat` + the S–V hypothesis so
`gaussian-hilbert`'s `ouSemigroupAct_eLpNorm_hypercontractive` proves
through it; `#print axioms` there no longer lists
`gross_lsi_implies_hypercontractive` / `stroock_varopoulos`;
`AXIOM_AUDIT.md`/`status.md`/`README.md` updated same commit; this
file → `plans/archive/` + `plans/history.md` entry.
