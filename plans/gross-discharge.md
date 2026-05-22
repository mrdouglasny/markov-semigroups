# Discharging the Gross axiom — reconciled against branch reality

**Status (2026-05-21): ABSTRACT SPINE COMPLETE.** H0 ✅, G1 ✅, G2 ✅,
G4 ✅, **P2 ✅, P3 ✅, final reduction ✅** — the hypothesis-parameterised
theorem `gross_lsi_implies_hypercontractive_of_hypotheses` is fully
proved and **`Abstract/GrossODE.lean` is sorry-free**; `#print axioms`
= `[propext, Classical.choice, Quot.sound]`. The theorem takes four
per-instance predicates as hypotheses: `CoreSemigroupInvariant`,
`GeneratorCompat`, `StroockVaropoulos` (relaxed to `1 < q`, deep-think
vetted), and `CoreLpL2Approx` (the 4th, deep-think vetted). Phase-by-phase
detail and lessons are archived under
[`archive/`](archive/) and consolidated in [`history.md`](history.md).

**ONLY REMAINING WORK: W (wire gaussian-hilbert).** Discharge the four
predicates for the GaussianFin / Ornstein–Uhlenbeck instance (smooth
bounded core + `+1/n` density), and feed them to
`gross_lsi_implies_hypercontractive_of_hypotheses` to eliminate the
top-level `gross_lsi_implies_hypercontractive` axiom downstream. See §W
below and [`gaussianfin-0b-readiness.md`](gaussianfin-0b-readiness.md).

**Reconciled 2026-05-16 against branch `feat/lp-carrier-stdGaussianFin-dirichletmarkov`**
(the rev gaussian-hilbert actually pins). Earlier hille-yosida/
structure-strengthening framing is **superseded** — see §1.

**Goal (unchanged):** turn `gross_lsi_implies_hypercontractive`
([`Abstract/Hypercontractivity.lean:269`](../MarkovSemigroups/Abstract/Hypercontractivity.lean))
from an axiom into a theorem, so the *existing* gaussian-hilbert
wiring (`HypercontractivityFromBE` → `ouSemigroupAct_eLpNorm_hypercontractive`
→ `polynomial_chaos_concentration` → pphi2) becomes Gross-axiom-free.

**Vetting trail:** Gemini passes 1–3 (analytical traps;
S–V-as-hypothesis; `generator_compat` green-lit). **Pass 4
(2026-05-16): plan "100% green-lit for Codex handoff"** with two
fixes, both applied: (i) **S–V binding trap** — `GeneratorCompat` is
existential so no global `A`; `StroockVaropoulos` now takes `Au` + its
`Tendsto` witness explicitly (§2); (ii) **right-derivative
consistency** — dropping the hille-yosida bridge means no free
two-sided derivative, so P2/P3 are **right-derivative only**
(self-contained via `h_gen`+`h_core`; ‡ in §3). G2 DCT strategy
endorsed. Ready for execution.

**Execution progress (branch tip `aa9cc47`):**

- **H0 ✅** (`64f3c44`) — 3 predicates + hypothesis-parameterised
  theorem; build green, non-breaking.
- **G1 ✅** (`924c405`) — OU generator named, fully proved.
- **G2 ✅ DONE.** `GaussianFin.generatorCompat_stdGaussianFin` is
  **sorry-free**. `#print axioms` = `propext`/`Classical.choice`/
  `Quot.sound` + exactly **two** custom axioms,
  `gaussianFin_diffQuot_tendsto_Lp` + `gaussianFin_integrationByParts`
  — both *general, Mathlib-native* (no project defs), Gemini-vetted
  **Standard / Likely correct**, in `AXIOM_AUDIT.md`. The deep cruxes
  Codex stalled on (nD heat eqn, γ-IBP, the DCT difference-quotient)
  were promoted to these general vetted axioms (the project lemmas
  proved from them by unfolding / instantiation); the third axiom
  `gaussianOU_heatEquation_within_zero` was subsumed by the DCT axiom
  and is **off** the live critical path. The `ouGeneratorFin_ibp`
  Lp-coercion bridge (G4) is also closed.
- **Abstract Gross relocated.**
  `gross_lsi_implies_hypercontractive_of_hypotheses` moved from
  `Hypercontractivity.lean` (predicates stay) to new
  **`Abstract/GrossODE.lean`**; legacy `gross_lsi_implies_hypercontractive`
  axiom retained (non-breaking) until **W**.
- **P3 ✅ scaffolded.** Exponent calculus + the P2 chain-rule
  assembly (`grossLogNorm_hasDerivWithinAt`) + the `antitoneOn`
  closure (`antitoneOn_of_hasDerivWithinAt_nonpos` on `Set.Ici 0`)
  are **proved**; only the P3 algebra and an interior-continuity
  bridge remain as sorries.
- **P2 decomposed (no axiom — would be circular).** Split into a
  general Mathlib-native exponent-path Leibniz lemma (pointwise core
  `hasDerivAt_abs_rpow_exponent` **proved**) and a general
  Mathlib-native Bochner–Leibniz lemma through a strong-`L²`
  derivative (the reusable kernel, *to be proved*, not axiomatized) +
  thin Gross glue.

**Remaining:** the one general `hasDerivWithinAt_integral_of_strongL2Deriv`
Leibniz kernel + the `grossPow_*`/glue + the P3 algebra
(`grossLogNorm_deriv_nonpos`) + the final `eLpNorm↔∫·^q` reduction →
then **W** (rewire gaussian-hilbert). Total open: 8 documented
`sorry`s in `GrossODE.lean`. gaussian-hilbert unaffected throughout
(new files outside its import closure).

---

## 1. Branch reality → the design pivot

`EuclideanFinLp.lean` on the consumed branch is **sorry-/axiom-free**
and already ships:
- `ouSemigroupFinLp t : Lp ℝ 2 (γFin n) →L[ℝ] Lp ℝ 2 (γFin n)` + all
  field lemmas + `isCoreFin_memLp` — **G3 done**;
- `markovSemigroup n` — the bundled `MarkovSemigroup`, **built
  directly (no hille-yosida `toContractingSemigroup`)** — old Phase 0a
  is OBE;
- `stdGaussianFin_dirichletMarkovSemigroup n : DirichletMarkovSemigroup`
  — the full DMS instance, filling the **weak** `energy_eq_deriv`.

gaussian-hilbert feeds this weak instance into the **abstract
`gross_lsi_implies_hypercontractive` axiom**. The 3 GaussianFin
axioms in `EuclideanFin.lean` persist on the branch.

**Pivot — do NOT strengthen the structure.** The earlier plan
(`energy_eq_deriv → generator_compat`) is now a **breaking change to a
working sorry-free shipped instance**. The same def-study /
leaf-placement logic that made **S–V a theorem hypothesis** applies
verbatim to the strong-generator facts: state
`gross_lsi_implies_hypercontractive` taking them as **explicit
`Prop` hypotheses**, leaving `DirichletMarkovSemigroup` (and the
branch instance) **untouched**. Discharge the hypotheses at the
GaussianFin call-site. This is strictly better post-branch:
non-breaking, Mathlib-clean, and consistent with the S–V decision
Gemini endorsed.

Reconciled theorem shape:

```lean
theorem gross_lsi_implies_hypercontractive
    (D : DirichletMarkovSemigroup X) (ρ : ℝ) (hρ : 0 < ρ)
    (h_lsi : D.SatisfiesLogSobolev ρ)
    (h_core : CoreSemigroupInvariant D)   -- P_t maps core→core
    (h_gen  : GeneratorCompat D)          -- strong-L² generator + form id
    (h_sv   : StroockVaropoulos D) :      -- generator-paired S–V
    D.IsHypercontractive ρ
```

No structural field is added; `energy_eq_deriv` stays; the branch's
`stdGaussianFin_dirichletMarkovSemigroup` is **not refilled**. The
GaussianFin instance supplies `h_core`/`h_gen`/`h_sv` where Gross is
invoked (in gaussian-hilbert's `HypercontractivityFromBE`, replacing
`apply gross_lsi_implies_hypercontractive` (axiom) with the same
applied to the new theorem + the three discharges — Gemini's "≈5-line
consumption swap", now literally just adding the hypothesis args).

---

## 2. The three hypothesis predicates

**`CoreSemigroupInvariant D`** := `∀ t ≥ 0, IsCore g → IsCore (P_t g)`
(+ power closure used by S–V). GaussianFin: discharged by the existing
`ouSemigroupFin_preserves_IsCore` (Standard axiom) — no new work.

**`GeneratorCompat D`** (Gemini pass-3 green-lit, idiomatic form):
```lean
∀ {f : X → ℝ} (hf : IsCore f), ∃ Af : Lp ℝ 2 μ,
  Filter.Tendsto (fun t : ℝ => t⁻¹ • (P t (coreToL2 hf) - coreToL2 hf))
    (𝓝[>] 0) (𝓝 Af)
  ∧ ∀ {g : X → ℝ} (hg : IsCore g), ⟪coreToL2 hg, Af⟫_ℝ = - energy g f
```
(`P t` = the **0a/branch L²-CLM** `ouSemigroupFinLp`, not pointwise.)
Strong (norm) limit ⇒ subsumes `energy_eq_deriv`; sign matches
`P_symmetric`/`energy_symm`; `[IsProbabilityMeasure μ]` is already a
`MarkovSemigroup` field so the pairing is well-defined.

**`StroockVaropoulos D`** — generator-paired (Gemini pass-3: `u^{q-1}
∉ core`, abstract `E(u,u^{q-1})` unusable) **with the binding trap
fixed (Gemini pass-4)**: `GeneratorCompat` is an existential, so there
is *no global `A`* to write `A (coreToL2 hu)`. Decouple by passing
the generator element `Au` + its strong-limit witness explicitly:
```lean
def StroockVaropoulos (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ {u : X → ℝ} (hu : IsCore u) (q : ℝ) (hq : 2 ≤ q)
    (Au : Lp ℝ 2 D.μ),
    Filter.Tendsto (fun t : ℝ => t⁻¹ • (D.P t (coreToL2 hu)
        - coreToL2 hu)) (𝓝[>] 0) (𝓝 Au) →
    (4*(q-1)/q^2) * D.energy (u^(q/2)) (u^(q/2))
      ≤ ⟪upow hu (q-1), - Au⟫_ℝ
```
In P3, Codex destructs `h_gen` to get `Au` + the `Tendsto` proof and
feeds them straight into `h_sv` — no `Classical.choose`, no dependent-
type-hell on the `GeneratorCompat` proof. LHS needs only `u^{q-1} ∈
L²` (free: `ε≤u≤M` + prob. measure) and `Au ∈ L²`.
*Lp `HPow` note (Gemini pass-4):* `Lp ℝ 2 μ` has **no** global real-
power instance — `upow hu (q-1)` := apply `(·)^(q-1)` to the
representative pointwise then repackage via `MemLp.toLp` (trivial
under the L∞ bounds).

---

## 3. Genuinely-remaining work (all off the branch)

Base every change on `feat/lp-carrier-stdGaussianFin-dirichletmarkov`.

| # | Item | Where | Status / effort |
|---|------|-------|-----------------|
| H0 | Define the 3 predicates (`CoreSemigroupInvariant`, `GeneratorCompat`, `StroockVaropoulos`) + restate the theorem with them as hypotheses | `Abstract/Hypercontractivity.lean` | **✅ DONE** — branch commit `64f3c44`; build green, `#print axioms` clean (no custom axioms), non-breaking |
| G1 | Name the OU generator: `ouGenerator1D` (the `g″−x·g′` already used in `EuclideanStein.lean`) + `ouGeneratorFin` lift | new `EuclideanGenerator.lean` | **✅ DONE** — branch `924c405`; fully proved (no sorry, `#print axioms` clean), incl. named restatements of the proved heat-eqn + γ-IBP; non-breaking |
| G2 | Strong-L² limit for GaussianFin ⇒ discharges `GeneratorCompat` | `EuclideanGenerator{Lp,Limit,Compat}.lean` | **✅ DONE** — `generatorCompat_stdGaussianFin` **sorry-free** (branch `aa9cc47`). `#print axioms` = Lean built-ins + exactly 2 custom: `gaussianFin_diffQuot_tendsto_Lp` + `gaussianFin_integrationByParts`, both *general Mathlib-native*, Gemini Standard-vetted (`AXIOM_AUDIT.md`). `gaussianOU_heatEquation_within_zero` proved-but-subsumed (off live path). `memLp_ouGeneratorFin`, `ouGeneratorFin_ibp` (=G4) proved. |
| G4 | nD γ-IBP (form-id half of `h_gen`) | folded into G2 | **✅ DONE** — `gaussianFin_integrationByParts` (general vetted axiom) ⇒ `ouGeneratorFin_ibp_integral`/`ouGeneratorFin_ibp` proved. |
| P2 | The Gross ODE: right-difference-quotient derivative of `∫(P_tf)^{q(t)}` (right-derivative only; `h_core`+`h_gen` self-contained) | `Abstract/GrossODE.lean` | **✅ Leibniz kernel + entropy bridge + antitoneOn continuity DISCHARGED axiom-free (2026-05-20).** Exponent calculus + chain-rule assembly `grossLogNorm_hasDerivWithinAt` + pointwise `hasDerivAt_abs_rpow_exponent` **proved**. **`hasDerivWithinAt_integral_of_strongL2Deriv`** is fully proved — `#print axioms` = `[propext, Classical.choice, Quot.sound]`. 11-lemma toolkit + ~150-line 9-step body. **`grossEntropy_eq`** (log-of-power algebra) ✅ DISCHARGED axiom-free via `Real.log_rpow` + 3-way case split on `q=0` / `|u|=0` / general. **`grossLogNorm_antitoneOn` continuity sorry closed** via `HasDerivWithinAt.continuousWithinAt`. Statements are project-definition-free → Mathlib-upstreamable. See `plans/archive/p2-strongL2-leibniz-discharge.md`. Remaining: `hasDerivAt_integral_rpow_exponent` DCT plumbing ⬜ (needs `ContDiff ℝ 1 a` neighborhood-of-`s` hypothesis), `grossPow_pos` ⬜ (statement is false-as-stated for `f ≡ 0`, needs hypothesis fix), `grossPow_hasDerivWithinAt` composition ⬜ (blocked by the DCT lemma above + energy-pairing identification). |
| P3 | Algebraic closure: P2 ⊕ `h_lsi` ⊕ `h_sv` ⊕ `q'=2ρ(q-1)` ⇒ `d⁺/dt log N ≤ 0`; `antitoneOn_of_hasDerivWithinAt_nonpos` on `Set.Ici 0` ⇒ `IsHypercontractive` (`0<ρ` firewall) | `Abstract/GrossODE.lean` | **🟡 scaffolded.** `antitoneOn` closure **proved structurally**; remaining: the cancellation `grossLogNorm_deriv_nonpos` (LSI on `u^{q/2}` + coupling + S–V) ⬜ + interior-continuity bridge ⬜ + final `eLpNorm↔∫·^q` reduction ⬜. ~200–400 L. |
| W | Wire gaussian-hilbert: pass the 3 discharges to the now-theorem (`GrossODE.gross_lsi_implies_hypercontractive_of_hypotheses`) | gaussian-hilbert | ⬜ ~10–30 L, hrs (after P2/P3) |

**Total ≈ 1450–2600 L, multi-week.** G3/0a/DMS-instance contribute
**0** (already done). **hille-yosida is fully dropped** — not even an
aid: G2 mirrors how the branch proved the weak field directly (Mehler
DCT), and the right-derivative design (‡) makes the abstract proof
self-contained without any C₀-semigroup module.

> **‡ Right-derivative consistency (Gemini pass-4, my prior error
> fixed).** Passes 1–3 deleted the "right-derivative-only" constraint
> *because the hille-yosida bridge was then mandated* (giving free
> two-sided derivatives). The branch-reconciliation **dropped that
> bridge** but I left the two-sided wording — a contradiction.
> Without the bridge, `GeneratorCompat`'s `𝓝[>] 0` gives **only** the
> right derivative; a left-derivative would need pushing a limit
> through `P_{t−h}` as `h→0⁺` (the joint-limit machinery hille-yosida
> supplied, now gone). So **right-derivative only** — and it is fully
> rigorous and *self-contained*: `h_core` ⇒ `P_tf ∈ core` ⇒ `h_gen`
> gives `A(P_tf)` as a strong right limit; `antitoneOn` on `Set.Ici 0`
> closes monotonicity. This is the original pre-hille-yosida design,
> now correctly justified — and the exact pattern the OU-entropy
> discharge already used (`hasDerivWithinAt_Ici_…`).

## 4. Risks

- **No breaking change** (the pivot's whole point): the branch's
  sorry-free instance is untouched; H0 only adds theorem args.
- **G2 is the real remaining math risk** but **low**: the 1D linear
  heat eqn (`hasDerivAt_t_ouSemigroup`) and γ-IBP
  (`gaussian_dirichlet_form_bilinear`) are *already proved*; G2/G4 are
  tensor-lift + the pointwise→strong-L² DCT pattern the repo has run
  for the entropy/quadratic discharges. No Kato/spectral/finite-chaos.
- **P2 is the effort bottleneck** (standard BGL §5.2 given the
  hypotheses; heavy Lean plumbing).
- The 3 GaussianFin axioms remain on the pphi2 chain regardless
  (tracked in `AXIOM_AUDIT.md`); full pphi2-axiom-freedom = this plan
  **+** their discharge.

## 5. Done =

`gross_lsi_implies_hypercontractive` is a theorem (3 hypotheses, no
structure change); GaussianFin discharges `h_core`/`h_gen`/`h_sv`;
gaussian-hilbert's `ouSemigroupAct_eLpNorm_hypercontractive` proves
through the theorem; `#print axioms` there no longer lists
`gross_lsi_implies_hypercontractive` / `stroock_varopoulos`;
`AXIOM_AUDIT.md`/`status.md`/`README.md` updated same commit; work
merged from / rebased onto
`feat/lp-carrier-stdGaussianFin-dirichletmarkov`; this file →
`plans/archive/` + `plans/history.md` entry.

---

*Superseded framing retained in git history (commits ef272f6 →
651e71f): hille-yosida `toContractingSemigroup` bridge as a mandated
Phase 0a, and `energy_eq_deriv → generator_compat` structure
strengthening. Both dropped: the branch built the bundled
semigroup/DMS directly and shipped it sorry-free, so a structure
break is unjustified — hypotheses, not fields.*
