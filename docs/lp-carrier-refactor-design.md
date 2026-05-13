# Lp-carrier MarkovSemigroup refactor design (Option 2)

*Authored 2026-05-13 to address the structural blocker found during
Stage N3 of the gaussian-hilbert hypercontractivity discharge.*

*Vetted by gemini-3.1-pro-preview 2026-05-13 (two passes — initial
flaw identification, then refactor-shape vet); **Verdict: commit to
this refactor**.*

## Why this refactor

The current `MarkovSemigroup` structure in `Abstract/Hypercontractivity.lean`
(post-bundle, commit `371780b`) is **mathematically unsound** for the
intended downstream use:

> Lean's `integral` returns `0` for non-integrable inputs, but iterated
> Bochner integrals of signed oscillatory functions don't unconditionally
> commute. If `f` is signed and non-absolutely-integrable, the unconditional
> field `P_semigroup` can fail because one side hits the junk value `0`
> while the other side conditionally converges to a non-zero value.
>
> — gemini-3.1-pro-preview, 2026-05-13

The fix per 3.1-pro: change the semigroup carrier from
`(X → ℝ) → (X → ℝ)` to bounded operators on the L² Hilbert space:
`Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`. On L² equivalence classes, junk values
don't exist; the semigroup laws hold flawlessly and unconditionally.

## Refactor scope

- **Files changed**: `MarkovSemigroups/Abstract/Hypercontractivity.lean`
  (and any concrete instances that consume it — currently *none* in
  markov-semigroups main; the previous Gross axioms have no in-repo
  downstream consumers).
- **Files added**: a new concrete instance file
  (`Instances/.../EuclideanFinLp.lean` or similar) building the
  Lp-valued multivariate Gaussian OU semigroup. Wraps the existing
  pointwise `ouSemigroupFin` to act on Lp classes.
- **Downstream impact**: gaussian-hilbert's
  `ouSemigroupAct_eLpNorm_hypercontractive` discharge becomes natural
  via the Lp-formulated Gross axiom.

## New structure shapes (3.1-pro vetted)

### `MarkovSemigroup`

```lean
structure MarkovSemigroup (X : Type*) [MeasurableSpace X] where
  /-- Reference probability measure. -/
  μ : Measure X
  hμ : IsProbabilityMeasure μ
  /-- Bounded linear operator on L² at each time t. -/
  P : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  /-- P 0 = identity. -/
  P_zero : P 0 = ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)
  /-- Semigroup property for t ≥ 0. -/
  P_semigroup : ∀ s t, 0 ≤ s → 0 ≤ t → P (s + t) = (P s).comp (P t)
  /-- Strong continuity at t = 0+. -/
  P_strong_cont : ∀ f : Lp ℝ 2 μ,
    Filter.Tendsto (fun t : ℝ => P t f) (nhdsWithin 0 (Set.Ici 0)) (nhds f)
  /-- Operator-norm contraction. -/
  P_contraction : ∀ t, 0 ≤ t → ‖P t‖ ≤ 1
  /-- Markov: P fixes any a.e.-constant-1 function (probability conservation).

  Uses the a.e.-equality formulation rather than `(1 : Lp ℝ 2 μ)` because
  Lp does not carry a global `One` instance (Mathlib provides this only
  for `p = ∞`). The probability-measure hypothesis on μ ensures the
  constant-1 function lies in L². -/
  P_conservation : ∀ t, 0 ≤ t → ∀ f : Lp ℝ 2 μ,
    (∀ᵐ x ∂μ, (f : X → ℝ) x = 1) → P t f = f
  /-- Markov: positivity preservation, via Lp's order structure. -/
  P_positivity : ∀ t, 0 ≤ t → ∀ f : Lp ℝ 2 μ, 0 ≤ f → 0 ≤ P t f
  /-- Symmetry on L²: `⟪f, P t g⟫ = ⟪P t f, g⟫`. -/
  P_symmetric : ∀ t, 0 ≤ t → ∀ f g : Lp ℝ 2 μ,
    ⟪f, P t g⟫_ℝ = ⟪P t f, g⟫_ℝ
```

### `DirichletMarkovSemigroup`

```lean
structure DirichletMarkovSemigroup (X : Type*) [MeasurableSpace X]
    extends MarkovSemigroup X where
  /-- Energy form on the core algebra (not on Lp). -/
  energy : (X → ℝ) → (X → ℝ) → ℝ
  energy_symm : ∀ f g, energy f g = energy g f
  energy_nonneg : ∀ f, 0 ≤ energy f f
  IsCore : (X → ℝ) → Prop
  IsCore_const : ∀ c : ℝ, IsCore (fun _ => c)
  IsCore_add : ∀ {f g}, IsCore f → IsCore g → IsCore (f + g)
  IsCore_smul : ∀ (c : ℝ) {f}, IsCore f → IsCore (c • f)
  energy_add_left : ∀ f₁ f₂ g, IsCore f₁ → IsCore f₂ → IsCore g →
    energy (f₁ + f₂) g = energy f₁ g + energy f₂ g
  energy_smul_left : ∀ (c : ℝ) f g, IsCore f → IsCore g →
    energy (c • f) g = c * energy f g
  energy_const : ∀ c : ℝ, energy (fun _ => c) (fun _ => c) = 0
  /-- Every IsCore function lies in L²(μ). -/
  IsCore_memLp : ∀ {f}, IsCore f → MemLp f 2 μ
  /-- Generator-form compatibility:
    E(f, g) = -(d/dt)|_{t=0+} ⟪[f], P_t [g]⟫_{L²(μ)}. -/
  energy_eq_deriv : ∀ f g (hf : IsCore f) (hg : IsCore g),
    HasDerivWithinAt
      (fun t : ℝ => ⟪coreToL2 hf, P t (coreToL2 hg)⟫_ℝ)
      (-energy f g) (Set.Ici 0) 0
```

with helper `coreToL2 (hf : IsCore f) : Lp ℝ 2 μ := (IsCore_memLp hf).toLp f`
defined inside the namespace to keep `energy_eq_deriv` readable.

### `IsHypercontractive` (the key predicate)

```lean
def MarkovSemigroup.IsHypercontractive (S : MarkovSemigroup X) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ (p q t : ℝ), 1 < p → p ≤ q → 0 < t →
    q ≤ 1 + (p - 1) * Real.exp (2 * ρ * t) →
    ∀ f : Lp ℝ 2 S.μ, MemLp ((⇑f) : X → ℝ) (ENNReal.ofReal p) S.μ →
      eLpNorm (((S.P t f) : X → ℝ)) (ENNReal.ofReal q) S.μ ≤
      eLpNorm ((⇑f) : X → ℝ) (ENNReal.ofReal p) S.μ
```

The `Lp ℝ 2 μ`-source with `MemLp` hypothesis for `L^p` lets the
predicate handle both `p < 2` (where `L² ⊂ L^p` for probability μ,
hypothesis trivially satisfied) and `p > 2` (where `L^p ⊂ L²`,
filtering Lp elements that also lie in L^p). `eLpNorm` returns `⊤`
for non-`L^q` functions, gracefully handling the case where `P t f`
exits `L^q`.

3.1-pro: "Brilliant." Verdict on this formulation.

### Gross axioms

```lean
axiom gross_lsi_implies_hypercontractive {X : Type*} [MeasurableSpace X]
    (D : DirichletMarkovSemigroup X) (ρ : ℝ)
    (h_lsi : D.SatisfiesLogSobolev ρ) :
    D.toMarkovSemigroup.IsHypercontractive ρ

axiom gross_hypercontractive_implies_lsi {X : Type*} [MeasurableSpace X]
    (D : DirichletMarkovSemigroup X) (ρ : ℝ)
    (h_hc : D.toMarkovSemigroup.IsHypercontractive ρ) :
    D.SatisfiesLogSobolev ρ
```

Note: the Gross axioms themselves are *unchanged in spirit* — they
still encode the LSI ⇔ HC equivalence (Gross 1975 Theorems 1 & 2).
Only the surrounding structure changes. The proof outline is the
same; only the formalization carrier differs.

Stroock-Varopoulos is similarly unaffected — it speaks the energy form
on IsCore, no Lp-side change.

## Bridging lemmas (post-structure-refactor)

Helpful adapters to land alongside the structure:

```lean
-- The semigroup is self-adjoint on Lp ℝ 2 μ.
lemma MarkovSemigroup.isSelfAdjoint (S : MarkovSemigroup X)
    {t : ℝ} (ht : 0 ≤ t) : IsSelfAdjoint (S.P t) := ...

-- Bridge: every MarkovSemigroup is a HilleYosida ContractingSemigroup.
def MarkovSemigroup.toContractingSemigroup (S : MarkovSemigroup X) :
    HilleYosida.ContractingSemigroup (Lp ℝ 2 S.μ) := ...

-- Bridge: the Dirichlet form on IsCore agrees with the inner-product
-- form `⟪f, -L g⟫` via the generator.
lemma DirichletMarkovSemigroup.energy_eq_inner_generator (D : DirichletMarkovSemigroup X)
    {f g : X → ℝ} (hf : D.IsCore f) (hg : D.IsCore g) (hg_dom : (D.coreToL2 hg) ∈ generatorDomain) :
    D.energy f g = ⟪D.coreToL2 hf, -D.generator (D.coreToL2 hg)⟫_ℝ := ...
```

## Time-domain decision

3.1-pro flagged that we have a fork: time as `ℝ` (with `0 ≤ t`
hypotheses) vs `ℝ≥0` / `NNReal` (with hypotheses dropped). **Decision:
keep time as `ℝ`**, with explicit `0 ≤ t` hypotheses. Rationale:

- Matches the current convention (no migration of consumers).
- Makes `energy_eq_deriv` natural via `HasDerivWithinAt _ _ (Set.Ici 0) 0`.
- The `0 ≤ t` overhead is minor compared to the ergonomics of
  Mathlib's `ℝ`-based calculus API.
- We can always provide `toStronglyContinuousSemigroup` (with `ℝ≥0`
  time) later as a separate adapter if needed.

## Re-vetting the Gross axioms

After the refactor lands, both Gross axioms need a fresh
gemini-3.1-pro-preview vet pass to confirm the new statements are:
- Type-correct
- Hypothesis-sufficient on the new carrier
- Non-vacuous
- Correct strength
- The same as the (true) BGL textbook content

Expected verdict: Standard (the math is unchanged; only the formalization
structure shifted to a sound one).

## Phase plan

### Phase 1 (markov-semigroups, ~3-4 active days)

1. Rewrite `Abstract/Hypercontractivity.lean` with the new structures.
2. Restate `gross_lsi_implies_hypercontractive` / `gross_hypercontractive_implies_lsi` / `stroock_varopoulos` on the new structures.
3. Build clean. No downstream consumers in markov-semigroups main.
4. Get gemini-3.1-pro-preview re-vet of the three restated axioms.
5. Update `AXIOM_AUDIT.md` with the new vetting records.
6. Push to main.

### Phase 2 (markov-semigroups, ~3-5 active days)

1. In a new file `Instances/WorkInProgress/EuclideanFinLp.lean`:
   - Define `ouSemigroupFinLp t : Lp ℝ 2 (γFin n) →L[ℝ] Lp ℝ 2 (γFin n)` by lifting `ouSemigroupFin t` to a.e.-classes.
   - Prove well-definedness on a.e.-classes (Mehler integral preserves a.e.-equality).
   - Prove the C₀-semigroup laws (`P_zero`, `P_semigroup`, `P_strong_cont`).
   - Prove operator-norm contraction (`P_contraction`).
   - Prove Markov properties (`P_conservation`, `P_positivity`, `P_symmetric`).
2. Construct the `DirichletMarkovSemigroup (Fin n → ℝ)` instance using
   the existing `dirichletSpaceFin` energy form + `IsCoreFin` core.
3. Prove `energy_eq_deriv`: the multivariate Gaussian Stein/IBP identity at t=0.
4. Verify with `#print axioms` that the new instance's closure is
   `[propext, Classical.choice, Quot.sound]` plus exactly the 3
   already-vetted GaussianFin axioms.

### Phase 3 (gaussian-hilbert, ~1-2 active days)

1. In `OUEigenfunctions.lean`:
   - Replace `axiom ouSemigroupAct_eLpNorm_hypercontractive` with a theorem proof:
     - Build / instantiate `stdGaussianDMS n := stdGaussianFin_dirichletMarkovSemigroup n`.
     - Apply `gross_lsi_implies_hypercontractive stdGaussianDMS 1 stdGaussianFin_LSI`.
     - Translate the abstract `IsHypercontractive` to the concrete
       `ouSemigroupAct`-form via the Stage Ag agreement theorem.
2. Verify with `#print axioms`: closure should be exactly
   `[propext, Classical.choice, Quot.sound,
   gross_lsi_implies_hypercontractive,
   ouSemigroupFin_l2_sq_hasDerivWithinAt,
   ouSemigroupFin_preserves_IsCore,
   ouSemigroupFin_entropy_sq_decay_bound]` plus possibly
   `Mathlib.AnalyticOn.*` if any analytic-continuation tools are used.
3. Update `AXIOM_AUDIT.md` to show 0 active gaussian-hilbert axioms.
4. Rebuild downstream consumers (`bonami_nelson_*`, `polynomial_chaos_concentration`).

## Total estimated effort

~7-11 active days across Phases 1+2+3. Possible to do
Phases 1 and 2 in parallel by different agents.

## Verification

- `lake build` of full markov-semigroups + gaussian-hilbert clean.
- `#print axioms` matches expected closure at each phase boundary.
- Audit doc reflects new structure.
- No regression in upstream `lgt`, `pphi2`, `pphi2N` (none of which import the Gross axioms today).
