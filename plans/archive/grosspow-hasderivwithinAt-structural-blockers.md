> **📦 ARCHIVED 2026-05-21 — work complete (GrossODE.lean is sorry-free). Retained for provenance; see [`../history.md`](../history.md).**

# `grossPow_hasDerivWithinAt` — structural blockers and design decision

**Date:** 2026-05-20
**Status:** Awaits user vet + design decision.
**File:** [`MarkovSemigroups/Abstract/GrossODE.lean`](../MarkovSemigroups/Abstract/GrossODE.lean).
**Parent plans:**
[`plans/gross-discharge.md`](gross-discharge.md) (overall Route A roadmap),
[`plans/p2-strongL2-leibniz-discharge.md`](p2-strongL2-leibniz-discharge.md)
(the now-discharged P2 Leibniz kernel).
**Vetting trace this session:** Gemini deep-think (`gemini-3.1-pro-preview`,
2026-05-20) independently confirmed the `grossPow_pos` false-statement
diagnosis whose fix exposed Blockers 1–3 below.

---

## 0. Background and cast of characters

### 0.1 The big picture

`markov-semigroups` is the abstract Markov-semigroup framework that
underpins the Gross axiom `gross_lsi_implies_hypercontractive` (Gross
1975, *Amer. J. Math.* 97, Thm 1) used downstream by the
**pphi2** T² φ⁴₂ continuum-limit project (via gaussian-hilbert's
`HypercontractivityFromBE`). Discharging Gross removes the long-pole
final-non-trivial-axiom on the pphi2 T² critical path.

The Gross discharge is partitioned into workstreams in
[`plans/gross-discharge.md`](gross-discharge.md):

* **H0** ✅ — the hypothesis-parameterised abstract Gross.
* **G1** ✅ — naming the OU generator.
* **G2** ✅ — `GaussianFin.generatorCompat_stdGaussianFin` (the discharge
  of the `GeneratorCompat` predicate, see below, for the Gaussian
  instance).
* **P2** — the Gross ODE: the right-derivative formula for
  `Λ(s) := log ‖P_s f‖_{q(s)}` in terms of `grossPowDeriv`
  (the "exponent half + semigroup half" diagonal total derivative).
  **The P2 *analytic kernel* `hasDerivWithinAt_integral_of_strongL2Deriv`
  is fully proved axiom-free as of today.**
* **P3** — algebraic closure: P2 + LSI + Stroock–Varopoulos imply
  `d⁺/ds Λ ≤ 0`. Self-contained algebraic identity. Still a `sorry`.
* **W** — wire the now-theorem `gross_lsi_implies_hypercontractive_of_hypotheses`
  back to gaussian-hilbert.

`grossPow_hasDerivWithinAt` (the subject of this doc) is the *composition*
that closes P2: given the two analytic ingredients, derive the
diagonal total derivative formula.

### 0.2 The two abstract structures

Definitions live in
[`MarkovSemigroups/Abstract/Hypercontractivity.lean`](../MarkovSemigroups/Abstract/Hypercontractivity.lean):

```lean
structure MarkovSemigroup (X : Type*) [MeasurableSpace X] where
  /-- Reference probability measure. -/
  μ : Measure X
  hμ : IsProbabilityMeasure μ
  /-- The Lp-CLM action of the semigroup. -/
  P : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  P_zero      : P 0 = ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)
  P_semigroup : ∀ s t, 0 ≤ s → 0 ≤ t → P (s + t) = (P s).comp (P t)
  P_strong_cont : ∀ f, Tendsto (fun t : ℝ => P t f)
                    (nhdsWithin 0 (Set.Ici 0)) (nhds f)
  P_contraction : ∀ t, 0 ≤ t → ‖P t‖ ≤ 1                  -- L² operator norm
  P_conservation : ∀ t, 0 ≤ t → ∀ f, (∀ᵐ x ∂μ, (f : X → ℝ) x = 1) → P t f = f
  P_positivity   : ∀ t, 0 ≤ t → ∀ f, 0 ≤ f → 0 ≤ P t f    -- preserves a.e. ≥ 0
  P_symmetric    : ∀ t, 0 ≤ t → ∀ f g, ⟪f, P t g⟫_ℝ = ⟪P t f, g⟫_ℝ
```

```lean
structure DirichletMarkovSemigroup (X : Type*) [MeasurableSpace X]
    extends MarkovSemigroup X where
  energy   : (X → ℝ) → (X → ℝ) → ℝ
  energy_symm     : ...
  energy_nonneg   : ...
  IsCore          : (X → ℝ) → Prop                        -- the form-core predicate
  IsCore_const    : ∀ c : ℝ, IsCore (fun _ => c)
  IsCore_add      : ∀ {f g}, IsCore f → IsCore g → IsCore (f + g)
  IsCore_smul     : ∀ (c : ℝ) {f}, IsCore f → IsCore (c • f)
  IsCore_memLp    : ∀ {f}, IsCore f → MemLp f 2 μ
  -- (plus energy compatibility fields: energy_add_left, energy_smul_left, …)
```

### 0.3 Derived names

```lean
def coreToL2 (D : DirichletMarkovSemigroup X) {f : X → ℝ} (hf : D.IsCore f)
    : Lp ℝ 2 D.μ :=
  (D.IsCore_memLp hf).toLp f          -- lift a core function to its Lp class

def grossExponent (ρ p s : ℝ) : ℝ :=
  1 + (p - 1) * Real.exp (2 * ρ * s)  -- the moving exponent q(s)

def grossPow (D) (hf : D.IsCore f) (ρ p s : ℝ) : ℝ :=
  ∫ x, |((D.P s (D.coreToL2 hf) : X → ℝ) x)| ^ grossExponent ρ p s ∂D.μ
  -- F(s) = ∫ |P_s f|^{q(s)}     (= ‖P_s f‖_{q(s)}^{q(s)})

def grossLogNorm (D) (hf) (ρ p s : ℝ) : ℝ :=
  (grossExponent ρ p s)⁻¹ * Real.log (grossPow D hf ρ p s)
  -- Λ(s) = q(s)⁻¹ · log F(s) = log ‖P_s f‖_{q(s)}

def grossLogIntegral (D) (hf) (ρ p s : ℝ) : ℝ :=
  ∫ x, |((D.P s (D.coreToL2 hf) : X → ℝ) x)| ^ grossExponent ρ p s
      * Real.log |((D.P s (D.coreToL2 hf) : X → ℝ) x)| ∂D.μ
  -- ∫ |P_s f|^{q(s)} · log|P_s f| (the integral appearing in F')

def grossPowDeriv (D) (hf) (ρ p s : ℝ) : ℝ :=
  2 * ρ * (grossExponent ρ p s - 1) * grossLogIntegral D hf ρ p s
    - grossExponent ρ p s
        * D.energy ((D.P s (D.coreToL2 hf) : X → ℝ))
            (fun x => |((D.P s (D.coreToL2 hf) : X → ℝ) x)|
                      ^ (grossExponent ρ p s - 1))
  -- F'(s) = q'(s)·grossLogIntegral - q(s)·E(P_s f, (P_s f)^{q(s)-1})
```

The two hypothesis predicates from
[`Hypercontractivity.lean`](../MarkovSemigroups/Abstract/Hypercontractivity.lean):

```lean
def CoreSemigroupInvariant (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ {g : X → ℝ} (hg : D.IsCore g),
    ∃ (g' : X → ℝ) (hg' : D.IsCore g'),
      D.P t (D.coreToL2 hg) = D.coreToL2 hg'
  -- the orbit stays in the L²-image of the core (up to Lp equivalence)

def GeneratorCompat (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ {f : X → ℝ} (hf : D.IsCore f), ∃ Af : Lp ℝ 2 D.μ,
    Tendsto (fun t : ℝ => t⁻¹ • (D.P t (D.coreToL2 hf) - D.coreToL2 hf))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Af)
    ∧ ∀ {g : X → ℝ} (hg : D.IsCore g),
        ⟪D.coreToL2 hg, Af⟫_ℝ = - D.energy g f
  -- the L²-strong right-derivative Af exists at t=0, AND pairs with
  -- core elements via the Dirichlet form
```

### 0.4 Shorthand used in the docstring of `grossPow_hasDerivWithinAt`

| Shorthand | Lean / formal meaning |
|---|---|
| `u_s` | The orbit `D.P s (D.coreToL2 hf) : Lp ℝ 2 D.μ`, or its `X → ℝ` coercion (context-dependent). |
| `u_σ` | Same with `σ` in place of `s`. |
| `q(s)` | `grossExponent ρ p s = 1 + (p-1)·exp(2ρs)` (always `> 1` for `1 < p` and `s ≥ 0`). |
| `q'(s)` | `deriv (grossExponent ρ p) s = 2 ρ (p-1) exp(2ρs) = 2 ρ (q(s) - 1)`. |
| `F(s)` | `grossPow D hf ρ p s`. |
| `Λ(s)` | `grossLogNorm D hf ρ p s`. |
| `ψ` | `ψ(x) := |x|^{q(s)}` (the rpow nonlinearity, parameterised by `q(s)`). |
| `ψ'(u_s)` | The pointwise derivative `q · u_s^{q-1}` (using `u_s ≥ 0` to drop the sign). |
| `A(u_s)` | The `Af` term witnessed by `GeneratorCompat` at `f := g'` where `D.P s (coreToL2 hf) = coreToL2 hg'` (via `CoreSemigroupInvariant`). Heuristically the generator applied to `u_s`. |
| `H(σ, τ)` | `∫ y, |((D.P σ (D.coreToL2 hf)) : X → ℝ) y| ^ grossExponent ρ p τ ∂D.μ` — a two-variable function with `σ` moving the orbit and `τ` moving the exponent. `H(s, s) = F(s)`. |
| `∂₁H(σ, τ)` | Partial derivative in `σ` (orbit) at the point `(σ, τ)`. |
| `∂₂H(σ, τ)` | Partial derivative in `τ` (exponent) at the point `(σ, τ)`. |
| `E(g, h)` | `D.energy g h`. |

### 0.5 The two analytic ingredients (now proved axiom-free)

```lean
/-- Parametric `rpow`-exponent Leibniz. -/
theorem hasDerivAt_integral_rpow_exponent {Y : Type*}
    [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    {w : Y → ℝ} (hw : Measurable w) {M : ℝ} (hM : ∀ y, |w y| ≤ M)
    {a : ℝ → ℝ} {a' s : ℝ}
    (ha_cd : ContDiff ℝ 1 a) (ha : HasDerivAt a a' s)
    (ha_pos : ∀ σ, 0 < a σ) :
    HasDerivAt (fun σ => ∫ y, |w y| ^ a σ ∂ν)
      (a' * ∫ y, |w y| ^ a s * Real.log |w y| ∂ν) s
```

Gives `∂₂H` (the exponent half) when applied with `w := u_s`,
`a := grossExponent ρ p`, `M` an L^∞ bound on `u_s`.

```lean
/-- Bochner-Leibniz through a strong-L² right derivative. -/
theorem hasDerivWithinAt_integral_of_strongL2Deriv {Y : Type*}
    [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (u : ℝ → Lp ℝ 2 ν) (u' : Lp ℝ 2 ν) {s : ℝ} (hs : 0 ≤ s)
    (hu : HasDerivWithinAt u u' (Set.Ici 0) s)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    {M K : ℝ} (hK_nn : 0 ≤ K)
    (hψ_bound : ∀ x ∈ Set.Icc (-M) M, |deriv ψ x| ≤ K)
    (h_u_bound : ∀ᶠ σ in nhdsWithin s (Set.Ici 0),
        ∀ᵐ y ∂ν, |(u σ : Y → ℝ) y| ≤ M)
    (h_u_s_bound : ∀ᵐ y ∂ν, |(u s : Y → ℝ) y| ≤ M) :
    HasDerivWithinAt (fun σ => ∫ y, ψ ((u σ : Y → ℝ) y) ∂ν)
      (∫ y, deriv ψ ((u s : Y → ℝ) y) * (u' : Y → ℝ) y ∂ν)
      (Set.Ici 0) s
```

Gives `∂₁H` (the orbit half) when applied with `ψ(x) := |x|^{q(s)}`,
`u(σ) := D.P σ (D.coreToL2 hf)`, `u' := Af` from `GeneratorCompat`.

---

## 1. Where we are

`GrossODE.lean` currently has **3 active `sorry`s**:

| Sorry | File:line (approx) | Status |
|---|---|---|
| `grossPow_hasDerivWithinAt` | `GrossODE.lean:~1322` | Body — **structural blockers below**. |
| `grossLogNorm_deriv_nonpos` | `GrossODE.lean:~1413` | P3 algebra (~200–400 LOC, self-contained — doesn't need any of the structural pieces in this doc). |
| `gross_lsi_implies_hypercontractive_of_hypotheses` | `GrossODE.lean:~1479` | Final assembly (~80–150 LOC; depends on the antitone consequence of P2 + P3). |

For `grossPow_hasDerivWithinAt`:

* The **analytic ingredients** (§0.5) are both proved axiom-free as
  of today (`#print axioms` = Mathlib core).
* The **composition** that wires them into
  `d/ds H(s, s) = ∂₁H(s, s) + ∂₂H(s, s)` exposes 4 mismatches between
  what the analytic lemmas need and what the abstract
  `DirichletMarkovSemigroup` interface provides.

---

## 2. The 4 structural blockers

### Blocker 1 — L^∞ orbit bound

**The need.** The `h_u_bound` argument of
`hasDerivWithinAt_integral_of_strongL2Deriv` (§0.5) demands

```lean
(h_u_bound : ∀ᶠ σ in nhdsWithin s (Set.Ici 0),
    ∀ᵐ y ∂ν, |(u σ : Y → ℝ) y| ≤ M)
```

In our application this becomes: *the orbit `D.P σ (D.coreToL2 hf)`
is uniformly L^∞-bounded a.e. in a right-neighbourhood of `s`.*

**What the framework provides.** From §0.2, `MarkovSemigroup` has
**only L²-contraction** (`P_contraction : ‖P t‖ ≤ 1` for the
operator norm on `Lp ℝ 2 μ`). There is no L^∞-contraction field; no
field guarantees `‖P_t f‖_∞ ≤ ‖f‖_∞`.

For *Markov kernels* (where `P t` arises from a probability kernel
`k_t` on `X`), the bound `‖P_t f‖_∞ ≤ ‖f‖_∞` is immediate from
positivity + conservation by Jensen on the kernel. But at the
*abstract Lp-CLM level*, the existing `P_positivity` +
`P_conservation` fields do **not** imply L^∞-contraction: positivity
is order-preservation in Lp, not pointwise; conservation pins only
the constant 1.

**The gap.** This bound is needed *uniformly in σ in a
right-neighbourhood of s*. Standard Markov semigroups satisfy this
immediately, but the abstract `DirichletMarkovSemigroup` does not
advertise it. Either supply the bound as a theorem hypothesis or add
a structure field.

---

### Blocker 2 — Orbit L^{q(s)}-integrability

**The need.** The integrand `|(D.P s (D.coreToL2 hf) : X → ℝ)|^{q(s)}`
in `grossPow` must be `Integrable` (otherwise Mathlib's convention
`∫ (non-integrable) = 0` makes `grossPow = 0`, breaking everything
downstream). Already discovered today while proving `grossPow_pos`
and currently handled with explicit `h_int` arguments threaded
through `grossPow_pos` → `grossLogNorm_hasDerivWithinAt` →
`grossLogNorm_antitoneOn`. For `grossPow_hasDerivWithinAt` we
additionally need it for **a neighbourhood** of `s`, not just at the
point `s`.

**What the framework provides.** `IsCore_memLp` gives only `MemLp f 2
μ` (L²). `CoreSemigroupInvariant` says the orbit stays in
`coreToL2`-image (so still L²), but L^{q(s)} for `q(s) > 2` is not
covered.

**The gap.** Same shape as Blocker 1. For the body of
`grossPow_hasDerivWithinAt` we need joint integrability of the σ- and
τ-integrand of `H(σ, τ)` and its partial derivatives in a
neighbourhood of `(s, s)`. Both follow from L^∞ boundedness of `u_σ`
(Blocker 1) + ψ being `ContDiff 1` on a compact interval, but the
hypothesis must be made explicit.

---

### Blocker 3 — Core-membership of `|u_s|^{q-1}`

**The need.** To identify the ∂₁H half as
`−q(s) · E(u_s, u_s^{q-1})` (the `energy`-pairing form in
`grossPowDeriv`), we use `h_gen`'s pairing identity (§0.3):

```
∀ g core, ⟪coreToL2 g, Af⟫_ℝ = - energy g f
```

Setting `g := u_s^{q-1}` (where `u_s = coreToL2 hg'` via
`CoreSemigroupInvariant`), the identity yields

`⟪coreToL2 (u_s^{q-1}), A(u_s)⟫ = - energy (u_s^{q-1}) g'`

which (by `energy_symm` and the substitution `g' = u_s` modulo
Lp-equivalence) becomes `= - energy g' (u_s^{q-1}) = - energy u_s
(u_s^{q-1})`, the term in `grossPowDeriv`.

This step **requires `D.IsCore (u_s^{q-1})`**, i.e., the core is
closed under the pointwise nonlinear functional calculus `t ↦ t^{q-1}`
applied to a nonnegative core element.

**What the framework provides.** §0.2 shows `IsCore` is closed under
linear operations (`IsCore_const`, `IsCore_add`, `IsCore_smul`) and
gives MemLp 2 (`IsCore_memLp`). **There is no closure axiom for
nonlinear rpow.**

For concrete instances (`Gaussian1D`, `GaussianFin`), the core (e.g.
`C^∞_c` or Schwartz-times-cutoff-style spaces) typically *is* closed
under positive rpow applied to a nonneg core element, modulo
approximation near `t = 0`. But at the abstract level this is
unsupplied.

**The gap.** Either add a closure field `IsCore_rpow_pos` to
`DirichletMarkovSemigroup`, or bypass `h_gen` via a density argument
(extend the pairing from `coreToL2 g` to general `g ∈ L²` by
continuity of inner product + `Af ∈ L²`) — but the density route
needs a separate hypothesis `core_dense_in_L2` (the density of
`coreToL2`-image in `Lp ℝ 2 μ`), which is **also** implicit in
"Dirichlet form core" but not currently exposed.

---

### Blocker 4 — Measurability upgrade for `hasDerivAt_integral_rpow_exponent`

**The need.** §0.5 shows `hasDerivAt_integral_rpow_exponent` takes
`(hw : Measurable w)`. We want to apply it with
`w := ((D.P s (D.coreToL2 hf)) : X → ℝ)`. But Lp coercion gives
only `AEStronglyMeasurable`, not pointwise `Measurable`.

**The gap.** Easy. Weaken the hypothesis of
`hasDerivAt_integral_rpow_exponent` from `Measurable w` to
`AEStronglyMeasurable w ν`. The body of that lemma uses `hw` in two
places (to derive `Measurable (F σ)` and `Measurable (F' σ)`), both
reformulable with `Continuous.comp_aestronglyMeasurable`. ~5–10 LOC.

**Status:** trivial relative to the other three; will be done as
part of any discharge path.

---

## 3. The design choice

### Route (a) — Hypothesis-only (localise the cost)

Add the missing pieces as hypotheses to `grossPow_hasDerivWithinAt`:

```lean
theorem grossPow_hasDerivWithinAt
    (D : DirichletMarkovSemigroup X) (ρ p : ℝ) (hρ : 0 < ρ) (hp : 1 < p)
    (h_core : CoreSemigroupInvariant D)
    (h_gen : GeneratorCompat D)
    {f : X → ℝ} (hf : D.IsCore f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_ne : ¬ f =ᵐ[D.μ] 0)
    {s : ℝ} (hs : 0 ≤ s)
    -- NEW (Blockers 1, 2, 3):
    (h_orbit_Linf : ∃ M, ∀ᶠ σ in 𝓝[Set.Ici 0] s,
        ∀ᵐ y ∂D.μ, |(D.P σ (D.coreToL2 hf) : X → ℝ) y| ≤ M)
    (h_int : ∀ σ ∈ Set.Ici (0:ℝ),
        Integrable (fun x => |(D.P σ (D.coreToL2 hf) : X → ℝ) x|
                              ^ grossExponent ρ p σ) D.μ)
    (h_pow_core : D.IsCore
        (fun x => (D.P s (D.coreToL2 hf) : X → ℝ) x ^ (grossExponent ρ p s - 1))) :
    HasDerivWithinAt (grossPow D hf ρ p) (grossPowDeriv D hf ρ p s) (Set.Ici 0) s
```

These then **cascade** through `grossLogNorm_hasDerivWithinAt`,
`grossLogNorm_antitoneOn`, and the final
`gross_lsi_implies_hypercontractive_of_hypotheses`. Cumulatively **~6
signatures touched** (the existing `h_int` already cascades through 3
of them).

**Pros:** local, surgical, no impact on instances or downstream
`gaussian-hilbert`.

**Cons:** the propagation makes the abstract theorems verbose;
concrete instances need to *prove* these every time they apply the
theorems (provable for `Gaussian1D`/`GaussianFin`, but the
boilerplate is non-trivial — and each new instance pays the cost
again).

---

### Route (b) — Structure refactor (pay once at the instance)

Strengthen the abstract structures so the hypotheses become *fields*
that concrete instances supply once:

* **`MarkovSemigroup`** — add
  ```
  P_Linfty_contraction : ∀ t, 0 ≤ t → ∀ f : Lp ℝ 2 μ, ∀ M : ℝ,
      (∀ᵐ x ∂μ, |(f : α → ℝ) x| ≤ M) →
      (∀ᵐ x ∂μ, |(P t f : α → ℝ) x| ≤ M)
  ```
* **`DirichletMarkovSemigroup`** (or strengthen `IsCore`) — add
  closure under positive rpow:
  ```
  IsCore_rpow_pos : ∀ {f : X → ℝ} (hf : IsCore f) (hf_nn : ∀ x, 0 ≤ f x)
      (r : ℝ) (hr : 0 ≤ r), IsCore (fun x => f x ^ r)
  ```
  OR add a density field
  ```
  core_dense_in_L2 : Dense (Set.range (fun (hf : Σ f, IsCore f) =>
      coreToL2 hf.2))
  ```
  (which would let us discharge Blocker 3 by L² density instead of
  by core closure).
* **`CoreSemigroupInvariant`** — strengthen the conclusion to
  L^q-regularity (`MemLp` for all relevant `q`), which makes Blocker
  2 disappear automatically.

**Pros:** abstract theorems stay clean; concrete instances supply the
fields *once* and downstream theorems use them without propagation.
The 4 hypotheses *are* textbook Markov-semigroup facts (L^∞
contraction, orbit Lp regularity, core stability under positive
rpow), so naming them as fields is the morally-correct abstraction.

**Cons:** ripple effects through
`MarkovSemigroups.Abstract.Hypercontractivity` (the structures
themselves) and every existing instance:
* `MarkovSemigroups.Instances.WorkInProgress.Euclidean`
* `MarkovSemigroups.Instances.WorkInProgress.EuclideanFin`
* `MarkovSemigroups.Instances.WorkInProgress.TwoPoint`
* gaussian-hilbert `HypercontractivityFromBE.lean` (which builds a
  `DirichletMarkovSemigroup` from the `BakryEmery` framework).

Each instance must discharge the new fields. All existing instances
*do* satisfy these properties, but exposing them is its own piece of
work — likely a handful of small new lemmas per instance.

---

## 4. Recommendation

Route (b) is the *correct* design move because:

1. The 4 hypotheses are **textbook Markov-semigroup facts**, not
   theorem-specific assumptions. Adding them as fields names the
   right abstraction.
2. The cascade in Route (a) makes the abstract Gross theorems
   noticeably uglier — 3+ extra hypotheses on each of 4 theorems.
3. Concrete instances already *do* satisfy these properties; Route
   (b) just makes them explicit.

But (b) is a non-trivial refactor: ~4 structure fields added, with
each existing instance needing to supply them. The instance
discharges should mostly be standard Markov / Gaussian facts, but
they'd land as a wave of new "small proved-lemmas" on each instance,
plus possibly cascading minor changes to downstream consumers.

---

## 5. Open questions for the user

1. **Route (a) vs (b)?**

2. **For Route (b), how aggressively?**
   - **(b1) Minimal:** add only `P_Linfty_contraction` and
     `IsCore_rpow_pos`. Leave L^q-integrability to be derived inline
     in each use site.
   - **(b2) Full:** also add `core_dense_in_L2` and strengthen
     `CoreSemigroupInvariant` to L^q-regularity (`MemLp (↑(P_s f))
     q μ` for the relevant `q`).

3. **Order of attack — should we attempt
   `grossLogNorm_deriv_nonpos` (P3 algebra) *first*** — it's
   self-contained, doesn't depend on these blockers, and is the only
   sorry that needs the genuine mathematical content of P3 (LSI +
   Stroock–Varopoulos + the `q' = 2ρ(q-1)` coupling) — **or finish
   the structural refactor first?**

4. **Push deferral:** the 12 markov-semigroups commits + 1 pphi2
   commit are still local on `main`. Should we keep accumulating, or
   push now so the intermediate state is visible to the
   gaussian-hilbert consumer (which pins markov-semigroups and would
   otherwise be unaware)?

---

## 6. Today's actual closures (for context)

7 sorries discharged today, all axiom-free:

* **P2 Leibniz kernel `hasDerivWithinAt_integral_of_strongL2Deriv`**
  (Steps 8–9 of its 9-step body closed today; Steps 1–7 closed in the
  immediately-preceding session). Steps 8 = "F' = ⟪u', g_Lp⟫_ℝ
  identification"; Step 9 = "slope F s identification via
  `slope_def_field` + `integral_sub` + `L2.inner_def` + Lp coercion
  reps + `psi_sub_eq_diff_mul_averagedDerivField` + `field_simp`".
* **`grossLogNorm_antitoneOn` continuity sorry** — closed via
  `HasDerivWithinAt.continuousWithinAt` (one line).
* **`grossEntropy_eq`** — log-of-power algebra
  (`∫ |u|^q · log(|u|^q) = q · ∫ |u|^q · log |u|`) via
  `Real.log_rpow` + 3-way case split on `q = 0` / `|u| = 0` /
  general.
* **`grossPow_pos`** — false-statement bug fix (statement was
  provably false for `f := 0`; Gemini-vetted) + body proof using
  `P_symmetric` + `P_conservation` to derive `∫ P_s f = ∫ f > 0`,
  then `integral_pos_iff_support_of_nonneg_ae` to conclude.
* **`hasDerivAt_integral_rpow_exponent`** — signature strengthened
  from `HasDerivAt a a' s` (a single point) to
  `ContDiff ℝ 1 a + HasDerivAt a a' s` (so the parametric DCT
  applies); body ~180 LOC. Key Mathlib lemma:
  `Real.mul_exp_neg_le_exp_neg_one` (the analytic supremum bound
  `y · exp(-y) ≤ 1/e`, which substituted with `y := a σ · (-log t)`
  yields `t^{a σ} · (-log t) ≤ 1/(e · a σ)` on `t ∈ (0, 1]`).

GrossODE.lean active sorries: **7 → 3**.

`#print axioms` of every closure today =
`[propext, Classical.choice, Quot.sound]`.

---

## 7. Today's commits (for tracking)

`markov-semigroups`: 12 commits on `main` (`d06f4a6` through `5f06f9f`).
`pphi2`: 1 commit on `main` (`ebf4442` — T² master plan reflects P2 ✅).

All commits are **local; nothing pushed yet** (the user hasn't
authorised pushing this session).
