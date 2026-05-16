# Discharge the abstract Gross axiom (`gross_lsi_implies_hypercontractive`)

**Status:** scoped, not started (as of 2026-05-16).

**Goal:** replace the axiom
`gross_lsi_implies_hypercontractive`
([`Abstract/Hypercontractivity.lean:269`](../MarkovSemigroups/Abstract/Hypercontractivity.lean))
with a Lean theorem, together with its load-bearing dependency
`stroock_varopoulos` ([:242](../MarkovSemigroups/Abstract/Hypercontractivity.lean)).
This is **Route A** (discharge the abstract axiom on the
`DirichletMarkovSemigroup` carrier), as opposed to **Route B** (the
concrete Gaussian route in
[`gaussian-ou-hypercontractivity.md`](gaussian-ou-hypercontractivity.md)).

**Why Route A is the relevant one.** Verified 2026-05-16: the live
pphi2 dependency chain bottoms out in the *abstract* axiom, not a
concrete Gaussian1D instance —
`gaussian-hilbert/GaussianHilbert/HypercontractivityFromBE.lean:204`
applies `gross_lsi_implies_hypercontractive` to a GaussianFin-built
`DirichletMarkovSemigroup` to prove the now-theorem
`ouSemigroupAct_eLpNorm_hypercontractive` (:314), consumed by
`polynomial_chaos_concentration` → pphi2. So **discharging the
abstract axiom directly makes the pphi2 path Gross-axiom-free with no
re-plumbing of gaussian-hilbert**; the Route-B concrete plan would
instead require rerouting gaussian-hilbert off the abstract axiom.

**Cross-repo scope:** internal to `markov-semigroups`, but Phase 0 is
a **breaking structure change** — every `DirichletMarkovSemigroup`
instance (incl. the GaussianFin one in gaussian-hilbert's reach) must
supply the new field. Coordinated like any structure refactor.

**Estimated total:** ~1700–3000 lines, multi-week (consistent with
the `AXIOM_AUDIT.md` 2000–4000 line estimate for this axiom).

---

## Mathematical content (already algebraically closed)

Gross's differentiation method. For `f ≥ 0` in core, `u(t)=P_t f`,
`q(t)=1+(p-1)e^{2ρt}` (so `q(0)=p`, `q'=2ρ(q-1)`),
`N(t)=‖u(t)‖_{q(t)}`:

    d/dt log N(t) ≤ 0  ⟺  q'·Ent_μ(u�q) ≤ q²·E(u, u^{q-1}).

Chain: **LSI** on `v=u^{q/2}` (`ρ·Ent_μ(u�q) ≤ 2·E(u^{q/2},u^{q/2})`)
⊕ **Stroock–Varopoulos** (`(4(q-1)/q²)·E(u^{q/2},u^{q/2}) ≤
E(u,u^{q-1})`) ⊕ the exponent ODE `q'=2ρ(q-1)` closes it with
equality in the bound. The algebra is `ring`/`nlinarith`; the cost is
entirely the analysis/Lean machinery below.

---

## Dependency chain

```
gross_lsi_implies_hypercontractive  (axiom → theorem)        [Phase 3]
   ↑ uses
 • d/dt of ∫ (P_t f)^{q(t)} dμ  + eLpNorm bridge             [Phase 2]
 • generator–form identity at all t (bootstrap)              [Phase 1]
 • stroock_varopoulos  (axiom → theorem)                     [Phase 4]
 • LSI (SatisfiesLogSobolev — hypothesis, given)
   ↑ all require
 DirichletMarkovSemigroup + core-invariance field            [Phase 0]
```

---

## Phase 0 — Structure augmentation (breaking change)

`DirichletMarkovSemigroup` (Hypercontractivity.lean:149) currently
exposes `energy_eq_deriv` only at **t=0⁺** and asserts **no**
core-invariance under `P_t`. Gross's proof needs `u=P_tf` and its
powers `u^{q/2}`, `u^{q-1}` in the core (to apply S–V and the form).

Add one field:
```lean
IsCore_semigroup : ∀ t, 0 ≤ t → ∀ {g}, IsCore g → IsCore (P t g)
```
(plus reuse the existing power-closure hypotheses S–V already takes).

- **Breaking:** every instance must fill it. The GaussianFin instance
  already has `ouSemigroupFin_preserves_IsCore` (an axiom) to discharge
  it; the abstract `MarkovSemigroup`-only users supply it as data.
- **Open design question (vet first — see Risks):** is core-invariance
  *sufficient*, or is an explicit differentiability/continuity-of
  `t ↦ ⟨φ, P_t g⟩` beyond 0⁺ also required as a field? Phase 1's
  bootstrap argument is supposed to derive it from the semigroup law +
  `energy_eq_deriv`; this must be confirmed sound before Phase 0 is
  finalized (a wrong field set wastes the whole effort).

**Estimate:** ~100–200 lines + instance fixups. **2–4 days.**

## Phase 1 — Generator–form identity at all `t` (bootstrap)

For `t₀>0`, `φ,g` core: `d/dt|_{t₀} ⟨φ,P_t g⟩
= d/ds|_{0⁺} ⟨φ, P_s(P_{t₀}g)⟩ = -E(φ, P_{t₀}g)` — using the
semigroup law `P_{t₀+s}=P_{t₀}∘P_s`, `energy_eq_deriv` (0⁺ form), and
Phase 0 core-invariance (`P_{t₀}g` core). Only the existing fields +
Phase 0; **no generator field needed**.

**Estimate:** ~300–500 lines. **1 week.**

## Phase 2 — `Lpᵍ`/`eLpNorm` calculus (the bottleneck)

(a) Bridge `eLpNorm (P t f) (ofReal q) μ` ↔ `(∫ |P t f|^q dμ)^{1/q}`
(`MemLp`, `q≥1`, ENNReal/Real coercions — the "Bochner trap" noted in
the file). (b) Parametric derivative of `F(t)=∫ (P_t f)^{q(t)} dμ`:
`F' = q'∫uᵍ log u dμ - q²E(u,u^{q-1})`, via
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` with a moving
exponent; dominators on `uᵍ log u`, integrability of `u^{q-1}`.

**Estimate:** ~800–1500 lines. **2–4 weeks** (the dominant cost).

## Phase 3 — Algebraic closure → `IsHypercontractive`

Phase 2 derivative ⊕ LSI ⊕ `stroock_varopoulos` (Phase 4) ⊕
`q'=2ρ(q-1)` ⇒ `d/dt log N ≤ 0`; Mathlib antitone-from-nonpositive
-derivative ⇒ `N(t) ≤ N(0)`; unwrap to the `IsHypercontractive`
predicate (note the `0<ρ` firewall — Hypercontractivity.lean:262).
Reduction general `f` → `|f|` → `f≥0` via `P_positivity`.

**Estimate:** ~200–400 lines. **3–5 days.**

## Phase 4 — Discharge `stroock_varopoulos`

The pointwise convexity inequality
`(a-b)(a^{p-1}-b^{p-1}) ≥ (4(p-1)/p²)(a^{p/2}-b^{p/2})²` (`a,b≥0`,
`p≥2`; reduces to `(p-2)²≥0` at `b=0`, general case by `u=a/b`
substitution) integrated against the symmetric Markov kernel via the
right-derivative form of `energy`. **This is the same real-variable
lemma as Phase 1 of the Route-B plan** — reuse it. Per `AXIOM_AUDIT.md`
discharge plan for `stroock_varopoulos`.

**Estimate:** ~400–600 lines. **1–2 weeks.** Independent of Phases
1–3; can run in parallel.

---

## Summary

| Phase | Deliverable | Lines | Time |
|---|---|---|---|
| 0 | `IsCore_semigroup` field + instance fixups | 100–200 | 2–4 d |
| 1 | generator–form identity at all `t` | 300–500 | 1 wk |
| 2 | `eLpNorm`/parametric-derivative machinery | 800–1500 | 2–4 wk |
| 3 | algebraic closure → `IsHypercontractive` | 200–400 | 3–5 d |
| 4 | `stroock_varopoulos` theorem | 400–600 | 1–2 wk |
| **Total** | | **~1700–3000** | **multi-week** |

## Risks

- **Phase 0 design (highest leverage).** Whether core-invariance alone
  suffices vs. needing an explicit regularity field is the one
  decision that wastes weeks if wrong. **Mitigation (do first):**
  Gemini deep-think + Codex review of the Phase-0 field set and the
  Phase-1 bootstrap soundness on the `Lp ℝ 2 μ` carrier, *before*
  touching the structure (per `~/.claude/CLAUDE.md` long-path policy).
- **Phase 0 breaking change** ripples to every `DirichletMarkovSemigroup`
  instance; the GaussianFin one (gaussian-hilbert's reach) needs its
  `IsCore_semigroup` filled from `ouSemigroupFin_preserves_IsCore`.
- **Phase 2** is the classic Lp-differentiation-under-the-integral
  grind; expect many 50–100 line Mathlib bridging lemmas.
- Discharging only `gross_lsi_implies_hypercontractive` still leaves
  the **3 GaussianFin axioms** on the pphi2 chain (they supply the LSI
  / BE-instance inputs). Their discharge is tracked separately in
  `AXIOM_AUDIT.md` (tensor-lift of already-discharged 1D facts). Full
  pphi2-Gross-axiom-freedom = this plan **+** GaussianFin discharge.

## Done =

`gross_lsi_implies_hypercontractive` and `stroock_varopoulos` are
theorems; `lake build` green; `#print axioms` on gaussian-hilbert's
`ouSemigroupAct_eLpNorm_hypercontractive` no longer lists either;
`AXIOM_AUDIT.md` / `status.md` / `README.md` counts updated in the
same commit; this file → `plans/archive/` + `plans/history.md` entry.
(`gross_hypercontractive_implies_lsi` — the reverse direction, no
pphi2 consumer — is out of scope here.)
