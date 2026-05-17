# Gaussian OU hypercontractivity: full discharge chain

**Status:** SUPERSEDED as the pphi2-unblocking path (reconciled
2026-05-16). Not started; retained as the **Route-B alternative** and
for its reusable techniques (Phase 1 Stroock–Varopoulos pointwise
lemma, Mehler-kernel representation). *(The "Status update
(2026-05-14)" section below is earlier context — accurate at the
time, now subsumed by the 2026-05-16 reconciliation note.)*

> **Reconciliation (2026-05-16).** Reality diverged from this plan's
> strategy. This plan's Phases 5–6 are *done in the codebase*, but via
> a **different route than Phases 1–4 propose**: gaussian-hilbert's
> `HypercontractivityFromBE.lean` discharged the local
> `ouSemigroupAct_eLpNorm_hypercontractive` (now a theorem, :314) and
> `polynomial_chaos_concentration` (now a theorem) by **consuming the
> abstract `gross_lsi_implies_hypercontractive` axiom + the 3
> GaussianFin axioms** on a GaussianFin-built
> `DirichletMarkovSemigroup` — *not* by building the concrete
> `Gaussian1D.dirichletMarkovSemigroup` of Phases 1–4. So this plan's
> strategic note ("the abstract axioms are not removed / not used") is
> **false in the as-built code**: the abstract Gross axiom is now the
> binding axiom on the live pphi2 chain. Consequently the actual work
> remaining to make pphi2 Gross-axiom-free is **Route A —
> [`gross-discharge.md`](gross-discharge.md)** (discharge the abstract
> `gross_lsi_implies_hypercontractive` + `stroock_varopoulos`
> directly), **plus** discharging the 3 GaussianFin axioms (tracked in
> `AXIOM_AUDIT.md`). Phases 1–4 here remain a valid *alternative*
> (concrete Gaussian1D Gross) but would additionally require rerouting
> gaussian-hilbert off the abstract axiom, so Route A is preferred.

**Goal (original):** discharge the chain of axioms blocking `pphi2`'s
`gaussian_hypercontractivity_continuum`, replacing them with theorems
proved from the explicit Gaussian Ornstein-Uhlenbeck Mehler kernel.

**Cross-repo scope:** spans `markov-semigroups` (phases 1–4) and
`gaussian-hilbert` (phases 5–6). Phase 7 (`pphi2`-internal) is out of
scope for this plan.

**Estimated total:** ~1900–3200 lines, ~6–9 weeks of focused work.

## Status update (2026-05-14)

Since this plan was originally scoped (2026-05-13), two structural
changes have landed on `main` that affect Phases 2 and 4:

* **2026-05-13: Lp-carrier refactor** (commits `c133b8a`, `65f0364`,
  `78b2694`, `1f81794`, merge `e1e2011`). The abstract `MarkovSemigroup`
  carrier was moved from `(X → ℝ) → (X → ℝ)` to bounded operators
  on `L²(μ)`, `Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`, after `gemini-3.1-pro-preview`
  flagged that the previous pointwise carrier was unsound (Bochner
  junk-value trap on non-integrable inputs). Design doc:
  [`docs/lp-carrier-refactor-design.md`](../docs/lp-carrier-refactor-design.md).
  `gross_lsi_implies_hypercontractive` also acquired an `hρ : 0 < ρ`
  hypothesis to firewall a vacuity issue. **Affects Phase 2** below.

* **2026-05-13: Stage N1 — multivariate Gaussian BE instance merge**
  (commit `8ed9e52`). The codex branch
  `feat/bakry-emery-multivariate-gaussian` landed
  `stdGaussianFin.bakryEmerySpace n : BakryEmerySpace (Fin n → ℝ)`
  with 3 placeholder textbook axioms (`ouSemigroupFin_l2_sq_hasDerivWithinAt`,
  `ouSemigroupFin_preserves_IsCore`, `ouSemigroupFin_entropy_sq_decay_bound`),
  all `gemini-3.1-pro-preview`-vetted **Standard**, all tensor-lift
  analogues of historical 1D primitives that have already been
  discharged in `Gaussian1D`. Detailed codex plan:
  [`docs/stage-n-detailed-plan.md`](../docs/stage-n-detailed-plan.md);
  N1 codex hand-off (now mostly historical):
  [`docs/stage-n1-codex-brief.md`](../docs/stage-n1-codex-brief.md).
  **Affects Phase 4** below.

* **2026-05-13: Stage N Phase 2 codex hand-off** is open
  (commit `7ccef48`):
  [`docs/stage-n-phase-2-codex-brief.md`](../docs/stage-n-phase-2-codex-brief.md).
  It builds the **concrete `DirichletMarkovSemigroup (Fin n → ℝ)`**
  for the standard multivariate Gaussian OU using the Lp-carrier
  framework. ~3–5 active days, no new axioms. This is the (Lp-carrier
  era) replacement for **Phase 2 + Phase 4 combined** of this plan.

**Net effect on this plan:**
- **Phase 1** (Stroock–Varopoulos for `Gaussian1D`) is unchanged and
  unstarted; it remains the natural first concrete bite.
- **Phase 2** (the `DirichletMarkovSemigroup` *instance* construction)
  is being delivered for the multivariate Gaussian directly by the
  codex Phase 2 brief, leveraging Stage N1. The 1D analog is no
  longer the priority — once the `n`-dim instance exists, the 1D
  case is `n = 1`.
- **Phase 3** (Gross-LSI⇒HC for the concrete instance) is unchanged
  in shape but should now target the `Fin n → ℝ` instance directly.
- **Phase 4** (tensorization to multivariate) is partly delivered by
  Stage N1; the remaining work is (a) discharging the 3 GaussianFin
  placeholder axioms by tensor-lift, (b) the Lp-carrier wrap that
  Phase 2 codex brief is building.
- **Phases 5–6** (gaussian-hilbert wire-in) unchanged.

The plan below retains its original 1D-first framing for educational
value; the *delivery* path is now multivariate-first via Stage N.

---

## Motivation

`pphi2`'s polynomial-chaos-concentration plan
(`pphi2/docs/polynomial-chaos-concentration.md`) explicitly requires
the Bonami–Nelson hypercontractivity bound for the OU semigroup,
ultimately stemming from Gross 1975 (LSI ⇒ HC). Currently:

* `markov-semigroups/Abstract/Hypercontractivity.lean` has the abstract
  Gross axioms on a bundled `DirichletMarkovSemigroup` structure.
* `gaussian-hilbert/GaussianHilbert/OUEigenfunctions.lean` has a local
  axiom `ouSemigroupAct_eLpNorm_hypercontractive` stating
  hypercontractivity directly for the `n`-dim Gaussian OU.
* `gaussian-hilbert/GaussianHilbert/PolynomialChaosConcentration.lean`
  has `bonami_nelson_chaos` *proved* in terms of the local axiom, and
  `polynomial_chaos_concentration` (Janson 5.10) **stated as an axiom**.
* `pphi2/ContinuumLimit/Hypercontractivity.lean` consumes
  `polynomial_chaos_concentration` via gaussian-hilbert.

The clean discharge route is to prove Gross-LSI⇒HC concretely for the
Gaussian1D `DirichletMarkovSemigroup` (using the explicit Mehler
kernel), tensorize to `n` dimensions, then collapse the gaussian-hilbert
axiom and complete `polynomial_chaos_concentration` as a theorem.

---

## Dependency chain (top-down)

```
pphi2.gaussian_hypercontractivity_continuum                          [Phase 7]
        ↑
gaussian-hilbert.polynomial_chaos_concentration  (currently axiom)   [Phase 6]
        ↑
gaussian-hilbert.bonami_nelson_chaos  (PROVED, uses local axiom ↓)
        ↑
gaussian-hilbert.ouSemigroupAct_eLpNorm_hypercontractive  (axiom)    [Phase 5]
        ↑ discharged by
markov-semigroups: n-dim Gaussian OU is hypercontractive  (theorem)  [Phase 4]
        ↑ uses (instance-level Gross)
markov-semigroups: Gross-LSI⇒HC for Gaussian1D       (theorem)       [Phase 3]
        ↑ uses
  • stroock_varopoulos for Gaussian1D  (theorem, not axiom)          [Phase 1]
  • Bakry-Émery LSI for Gaussian1D.bakryEmerySpace (proved already)
  • L^p norm differentiation under OU semigroup  (theorem)
        ↑ uses
DirichletMarkovSemigroup *instance* for Gaussian1D  (data)           [Phase 2]
        ↑ uses
Existing Gaussian1D.bakryEmerySpace + ouSemigroup machinery (proved)
```

---

## Phase 1 — Stroock–Varopoulos for `Gaussian1D` (theorem, not axiom)

**Statement:**
```lean
theorem stroock_varopoulos_gaussian1D (p : ℝ) (hp : 2 ≤ p)
    (f : ℝ → ℝ) (hf : Gaussian1D.IsCore f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_p_half : Gaussian1D.IsCore (fun x => f x ^ (p / 2)))
    (hf_p_one  : Gaussian1D.IsCore (fun x => f x ^ (p - 1))) :
    (4 * (p - 1) / p ^ 2) *
      Gaussian1D.ouEnergy (fun x => f x ^ (p / 2)) (fun x => f x ^ (p / 2)) ≤
    Gaussian1D.ouEnergy f (fun x => f x ^ (p - 1))
```

**Sub-pieces:**

1. **Pointwise real-variable inequality**
   `(a − b)(a^{p − 1} − b^{p − 1}) ≥ (4(p − 1)/p²) (a^{p/2} − b^{p/2})²`
   for `a, b ≥ 0`, `p ≥ 2`. Elementary calculus: scaling `b = 0` reduces
   to `(p − 2)² ≥ 0`; general case by substitution `u = a/b` and
   one-variable derivative. **~150 lines.**

2. **Mehler kernel representation of `⟨g, h − P_t h⟩`.** For our concrete
   `Gaussian1D.ouSemigroup`, derive the 2D Gaussian kernel
   `(x, y) ↦ ρ_t(x, y)` (joint density of `N(0, [[1, e^{−t}], [e^{−t}, 1]])`)
   via the orthogonal-invariance trick already used in
   `semigroup_selfAdjoint`. Express
   `⟨g, h − P_t h⟩ = (1/2) ∫∫ (g(x) − g(y))(h(x) − h(y)) K_t(x, y) dγ(x) dγ(y)`
   where `K_t = ρ_t / (ρ_γ ⊗ ρ_γ)`. **~200 lines.**

3. **Integration + limit.** Apply the pointwise inequality inside the
   double integral, divide by `t`, take `t ↘ 0` via the right-derivative
   form of `ouEnergy`. **~150 lines.**

**Estimate:** 400–600 lines, 1–2 weeks.

**Risks / blockers:**
- The kernel-representation step needs care with `b(t) = √(1 − e^{−2t}) → 0`
  as `t → 0+` (the kernel degenerates). The orthogonal-invariance route
  we already used in `EuclideanStein.lean:semigroup_selfAdjoint` handles
  this cleanly.
- `IsCore` closure under `f ↦ f^{p/2}` and `f ↦ f^{p − 1}` is left as
  explicit hypotheses (matching the abstract `stroock_varopoulos` axiom).

**File:** new `MarkovSemigroups/Instances/WorkInProgress/EuclideanStroockVaropoulos.lean`.

---

## Phase 2 — `DirichletMarkovSemigroup` instance for `Gaussian1D`

**Deliverable:**
```lean
def Gaussian1D.dirichletMarkovSemigroup : DirichletMarkovSemigroup ℝ
```

filling all fields of the bundled structure. Most are already proved:

| Field | Status |
|---|---|
| `μ, hμ, P` | trivial (`γ`, `ouSemigroup`) |
| `P_zero` | trivial (= identity) |
| `P_semigroup` | reuses `ouSemigroup_compose` (proved) |
| `P_conservation` | `P_t 1 = 1` is immediate from probability measure |
| `P_positivity` | `f ≥ 0 ⇒ P_t f = ∫ f(...) dγ ≥ 0` |
| `P_symmetric` | reuses `semigroup_selfAdjoint` (proved) |
| `P_l2_contraction` | reuses `semigroup_contraction` (proved); rewrap to `eLpNorm` form |
| `energy, energy_*, IsCore_*` | reuse `bakryEmerySpace.toDirichletSpace` fields |
| `energy_eq_deriv` | **NEW**: `(d/ds) ⟨f, P_s g⟩|_{s=0+} = -E(f, g)`. Needs Mehler-derivative + γ-invariance argument. ~100 lines. |

**Estimate:** 200–300 lines, 3–5 days.

**Risks:** the `eLpNorm` rewrap of `semigroup_contraction` (currently
stated as `∫ (P_t f)² ≤ ∫ f²`) needs bridging to `eLpNorm`-form via
Mathlib's `MemLp` / `eLpNorm_le_eLpNorm` API. Some plumbing required.

**File:** new file or addition to `EuclideanEntropyDecay.lean` near
existing `bakryEmerySpace` instance.

---

## Phase 3 — Gross-LSI⇒HC for `Gaussian1D`

The instance-level discharge of `gross_lsi_implies_hypercontractive`
(abstract axiom in `Abstract/Hypercontractivity.lean`).

**Three sub-pieces:**

### 3a. L^p norm differentiation along the semigroup

For `f` positive, bounded, in `IsCore`:
```
(d/dt) ‖P_t f‖_{L^{q(t)}(γ)}^{q(t)}
  = q'(t) · ∫ (P_t f)^{q(t)} · log(P_t f) dγ
  + q(t) · ∫ (P_t f)^{q(t) − 1} · (∂_t P_t f) dγ
```

Uses parametric DCT machinery similar to what we built for entropy
decay (`EuclideanEntropyDecay.lean`). The integrability bookkeeping is
heavier (moving exponent `q(t) = 1 + (p − 1) e^{2t}`). **~400–600 lines.**

### 3b. Closing the differential inequality

Substitute the heat equation `∂_t P_t f = L P_t f` (via existing
`hasDerivAt_t_ouSemigroup` — proved in `EuclideanStein.lean` for IsCore;
will need a slightly weakened version for `(P_t f)^{q − 1}` powers).

Apply Stroock–Varopoulos (Phase 1) with `g := P_t f`, `p := q(t)`, to
relate `E(P_t f, (P_t f)^{q − 1})` to `E((P_t f)^{q/2}, (P_t f)^{q/2})`.

Apply LSI for `Gaussian1D.bakryEmerySpace` (`ρ = 1`, available from
the abstract Bakry-Émery LSI theorem in `Diffusion/CarreDuChamp.lean`)
to bound the entropy of `(P_t f)^{q/2}` against its energy.

Combine to get `(d/dt) ‖P_t f‖_{L^{q(t)}}^{q(t)} ≤ 0`. **~200–400 lines.**

### 3c. From differential inequality to `IsHypercontractive`

Integrate the differential inequality from `0` to `t`; conclude
`‖P_t f‖_{L^{q(t)}} ≤ ‖f‖_{L^p}` whenever `q(t) ≤ 1 + (p − 1) e^{2t}`.
**~100–200 lines.**

**Estimate:** 700–1200 lines, 2–3 weeks.

**Risks:**
- Step 3a is the L^p analog of our entropy/Fisher derivative work; it
  needs `|f|^{q/2}` to remain in the core throughout `t ∈ [0, T]`, which
  is the same closure-under-smooth-functions issue we papered over for
  the abstract `stroock_varopoulos` axiom.
- Mathlib's `eLpNorm` API + chain rule + parametric DCT need to be
  carefully composed. Expect bridging lemmas (50-100 lines each) for
  several `eLpNorm` manipulations not directly in Mathlib.

**File:** new file `MarkovSemigroups/Instances/WorkInProgress/EuclideanGrossHC.lean`.

---

## Phase 4 — Tensorize to multivariate Gaussian OU

Once Codex's `feat/bakry-emery-multivariate-gaussian` branch lands, we
have the `n`-dim Gaussian OU on `Fin n → ℝ`.

**Two paths to multivariate hypercontractivity:**

**Path A (tensorization, recommended):** Gross hypercontractivity
tensorizes by Hölder + product-measure-Fubini:

```lean
theorem gross_tensorize {X Y : Type*} ...
    (DX : DirichletMarkovSemigroup X) (DY : DirichletMarkovSemigroup Y)
    {ρ : ℝ} (hX : DX.IsHypercontractive ρ) (hY : DY.IsHypercontractive ρ) :
    (productDirichletMarkov DX DY).IsHypercontractive ρ
```

Plus an inductive `Fin n` argument. **~300–500 lines.**

**Path B (direct via Bakry-Émery):** the `n`-dim Gaussian OU is itself
a `BakryEmerySpace` with curvature `ρ = 1`. Apply Phase 3 verbatim to
the `n`-dim instance. **~600–800 lines** (proofs are slightly longer in
multidim because of the gradient).

Recommended: Path A. Cleaner, reuses 1D work.

**Risks:** Mathlib's `MeasureTheory.Measure.pi` infrastructure +
`eLpNorm`-on-product-spaces lemmas need to line up. Some bridging
required (~50-100 lines).

**File:** new file `MarkovSemigroups/Instances/WorkInProgress/EuclideanFinGrossHC.lean`
(or extending Codex's WIP).

---

## Phase 5 — Discharge gaussian-hilbert's local hypercontractivity axiom

The axiom in `gaussian-hilbert/GaussianHilbert/OUEigenfunctions.lean`:
```lean
axiom ouSemigroupAct_eLpNorm_hypercontractive {n : ℕ}
    (p : ℝ) (hp : 2 ≤ p) (t : ℝ) (_ht : 0 ≤ t)
    (_h_nelson : p - 1 ≤ Real.exp (2 * t))
    (f : MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) :
    eLpNorm ((ouSemigroupAct n t f : (Fin n → ℝ) → ℝ))
        (ENNReal.ofReal p) (stdGaussianFin n) ≤
      eLpNorm ((f : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n)
```

Becomes:
```lean
theorem ouSemigroupAct_eLpNorm_hypercontractive ... := by
  -- Construct the DirichletMarkovSemigroup for nD OU (Phase 4 output).
  -- Invoke its IsHypercontractive at ρ = 1 with the Nelson parameters.
  -- Unwrap to the eLpNorm form.
```

**Estimate:** 50–150 lines, mostly notation bridging. **1 day** once
Phase 4 is done.

**File:** edit `gaussian-hilbert/GaussianHilbert/OUEigenfunctions.lean`.

---

## Phase 6 — `polynomial_chaos_concentration` in gaussian-hilbert

Currently axiomatized in `PolynomialChaosConcentration.lean`. The
theorem is **Markov + Bonami–Nelson + optimize p**:

* `bonami_nelson_chaosLE`: `‖F‖_{L^p} ≤ (d + 1)(p − 1)^{d/2} ‖F‖_{L²}`
  (already proved in the file, modulo the local axiom from Phase 5).
* Markov inequality: `ℙ(|F| > λ‖F‖_2) ≤ (‖F‖_p / (λ‖F‖_2))^p`.
* Optimize: set `p − 1 = (λ/e)^{2/d}` (or similar), get tail
  `~ exp(−c_d λ^{2/d})`.

**Estimate:** 200–400 lines, **3–5 days** once Phase 5 is done.

**File:** edit `gaussian-hilbert/GaussianHilbert/PolynomialChaosConcentration.lean`.

---

## Phase 7 (out of scope) — pphi2's specialization

In `pphi2/Pphi2/ContinuumLimit/Hypercontractivity.lean` +
`Pphi2/NelsonEstimate/*`: specialize `polynomial_chaos_concentration`
to the GFF / lattice. This is `pphi2`-internal work, not in
`markov-semigroups` scope. Per pphi2's own estimate: **2–3 weeks**.

---

## Summary table

| Phase | Repo | Deliverable | Lines | Time |
|---|---|---|---|---|
| 1 | markov-semigroups | `stroock_varopoulos_gaussian1D` theorem | 400–600 | 1–2 wk |
| 2 | markov-semigroups | `Gaussian1D.dirichletMarkovSemigroup` instance | 200–300 | 3–5 d |
| 3 | markov-semigroups | Gross-LSI⇒HC for Gaussian1D | 700–1200 | 2–3 wk |
| 4 | markov-semigroups | nD Gaussian OU hypercontractive | 300–500 | 1–2 wk |
| 5 | gaussian-hilbert | Discharge `ouSemigroupAct_eLpNorm_hypercontractive` | 50–150 | 1 d |
| 6 | gaussian-hilbert | `polynomial_chaos_concentration` theorem | 200–400 | 3–5 d |
| **Total (Phases 1–6)** | | | **~1900–3200** | **~6–9 wk** |
| 7 | pphi2 (out of scope) | `gaussian_hypercontractivity_continuum` etc. | — | 2–3 wk |

---

## Strategic notes

* The abstract axioms `stroock_varopoulos`,
  `gross_lsi_implies_hypercontractive`,
  `gross_hypercontractive_implies_lsi` in
  `Abstract/Hypercontractivity.lean` are **not** removed by this plan —
  the proofs go through the concrete `Gaussian1D` instance, not the
  abstract `DirichletMarkovSemigroup`. Those abstract axioms remain as
  vetted-Standard textbook bridges, available for future use cases.

* Phases 1–3 are essentially "redo the BGL §5.2 proof for Gaussian1D
  using the explicit Mehler kernel". They are independent of the
  abstract Gross framework.

* Phase 4 depends on Codex's branch landing. Can be done in parallel
  with Phases 1–3.

* **Bottleneck is Phase 3** (L^p differentiation): the analog of our
  entropy/Fisher derivative work but with moving exponent `q(t)`. Most
  of the multi-week budget is here.

* **Lighter alternative**: skip the general Gross theorem and prove
  `bonami_nelson_chaos_gaussian1D` directly (L^p contraction along the
  chaos eigenvalue) without going through abstract Gross. ~600 lines
  instead of ~1500–2000 — but it is not the general Gross theorem,
  just the Nelson special case. Sufficient for `pphi2`'s actual need;
  loses the abstract reusability.

---

## References

* Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, §5.2 (Gross theorem proof) and §1.7
  (Stroock–Varopoulos).
* Stroock, *Logarithmic Sobolev inequalities for Gibbs states*, in
  *Dirichlet Forms (Varenna 1992)*, Lecture Notes in Math. 1563.
* Varopoulos, "Hardy–Littlewood theory for semigroups," J. Funct.
  Anal. 63 (1985).
* Bonami, "Étude des coefficients de Fourier des fonctions de
  L^p(G)," Ann. Inst. Fourier 20 (1970).
* Nelson, "The free Markoff field," J. Funct. Anal. 12 (1973).
* Gross, "Logarithmic Sobolev inequalities," Amer. J. Math. 97 (1975).

## Cross-repo doc links

* `pphi2/docs/polynomial-chaos-concentration.md` — pphi2's plan that
  consumes the end of this chain (Phase 6 → Phase 7).
* `pphi2/docs/hypercontractivity.md` — pphi2's overview of why
  hypercontractivity is needed in the P(Φ)₂ construction.
* `gaussian-hilbert/GaussianHilbert/PolynomialChaosConcentration.lean`
  — site of Phase 6.
* `gaussian-hilbert/GaussianHilbert/OUEigenfunctions.lean`
  — site of Phase 5.
