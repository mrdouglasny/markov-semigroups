# Discharging the Gross axiom — reconciled against branch reality

**Status:** scoped, not started. **Reconciled 2026-05-16 against
branch `feat/lp-carrier-stdGaussianFin-dirichletmarkov`** (the rev
gaussian-hilbert actually pins). Earlier hille-yosida/structure-
strengthening framing is **superseded** — see §1.

**Goal (unchanged):** turn `gross_lsi_implies_hypercontractive`
([`Abstract/Hypercontractivity.lean:269`](../MarkovSemigroups/Abstract/Hypercontractivity.lean))
from an axiom into a theorem, so the *existing* gaussian-hilbert
wiring (`HypercontractivityFromBE` → `ouSemigroupAct_eLpNorm_hypercontractive`
→ `polynomial_chaos_concentration` → pphi2) becomes Gross-axiom-free.

**Vetting trail:** Gemini deep-think passes 1–3 (analytical traps;
S–V-as-hypothesis; `generator_compat` green-lit). Those verdicts still
hold; only the *delivery vehicle* changes per §1.

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

**`StroockVaropoulos D`** — generator-paired (Gemini pass-3 trap fix:
`u^{q-1} ∉ core`, so the abstract `E(u,u^{q-1})` is unusable):
```lean
∀ {u} (hu : IsCore u) (q) (hq : 2 ≤ q),
  (4*(q-1)/q^2) * energy (u^(q/2)) (u^(q/2))
    ≤ ⟪coreToL2 hu ^ (q-1), - (A (coreToL2 hu))⟫_ℝ
```
LHS needs only `u^{q-1} ∈ L²` (free: `ε≤u≤M` + prob. measure) and
`A u ∈ L²` (from `h_gen`).

---

## 3. Genuinely-remaining work (all off the branch)

Base every change on `feat/lp-carrier-stdGaussianFin-dirichletmarkov`.

| # | Item | Where | Status / effort |
|---|------|-------|-----------------|
| H0 | Define the 3 predicates (`CoreSemigroupInvariant`, `GeneratorCompat`, `StroockVaropoulos`) + restate the theorem with them as hypotheses | `Abstract/Hypercontractivity.lean` | non-breaking; ~80–150 L, 1–2 d |
| G1 | Name the OU generator: `ouGenerator1D` (the `g″−x·g′` already used in `EuclideanStein.lean`) + `ouGeneratorFin` lift | EuclideanStein/EuclideanFin | low, ~80 L |
| G2 | Strong-L² linear limit for GaussianFin: `t→0⁺` endpoint of the proved 1D `hasDerivAt_t_ouSemigroup` + pointwise→L² (DCT, repo-standard) + nD lift ⇒ discharges `GeneratorCompat` for the branch instance | new, off branch | moderate-routine, ~250–450 L |
| G4 | nD γ-IBP: tensor-lift the proved 1D `gaussian_dirichlet_form_bilinear` ⇒ the form-id half of `h_gen` + the generator-paired `h_sv` | new, off branch | moderate-routine, ~150–300 L |
| P2 | The Gross ODE: weak-L² difference-quotient derivative of `∫(P_tf)^{q(t)}` (Gemini Trap-1 method; two-sided interior; `L^∞⊂L²⊂L¹` free from `hμ`) | `Abstract/` | bottleneck, ~700–1300 L, 2–4 wk |
| P3 | Algebraic closure: P2 ⊕ `h_lsi` ⊕ `h_sv` ⊕ `q'=2ρ(q-1)` ⇒ `d/dt log N ≤0` on `(0,∞)`; `AntitoneOn`-via-continuity ⇒ `IsHypercontractive` (`0<ρ` firewall) | `Abstract/` | ~200–400 L, 3–5 d |
| W | Wire gaussian-hilbert: pass the 3 discharges to the now-theorem | gaussian-hilbert | ~10–30 L, hrs |

**Total ≈ 1450–2600 L, multi-week.** G3/0a/DMS-instance contribute
**0** (already done). hille-yosida is now an *optional* implementation
aid for G2 only, **not** a mandated bridge (the branch proved the
weak field directly; G2 mirrors that, plus the strong upgrade).

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
