# Stage N detailed plan — multivariate Bakry-Émery instance for `stdGaussianFin n`

*Updated 2026-05-12: pivoted from a **generic** `BakryEmerySpace.pi`
tensorization lemma to the **concrete** instance
`stdGaussianFin.bakryEmerySpace n`, because the current
`BakryEmerySpace` class exposes the semigroup as a bare operator
(no kernel representation), so a generic product-semigroup constructor
is not derivable without first refactoring the class — out of scope here.*

*Updated 2026-05-13: (a) the 4 historical 1D BE textbook axioms in
`Euclidean.lean` have been fully discharged into proved theorems; the
1D `Gaussian1D.bakryEmerySpace` (now in
`Instances/WorkInProgress/EuclideanEntropyDecay.lean`) is axiom-free.
(b) the abstract `MarkovSemigroup` and `Gross` axioms have been
restructured into the new bundled `DirichletMarkovSemigroup` in
`Abstract/Hypercontractivity.lean` (commits `6e4ad85`, `371780b`).
(c) codex is mid-way through N1 — N1.0–N1.3 plus the N1.4 derivative
bridge are done on branch `feat/bakry-emery-multivariate-gaussian`
(1371 lines, 0 axioms, 0 sorries).*

*The bulk of Stage N (sub-stage N1, originally estimated ~450 lines,
realistically ~2000-2300 lines given the kernel-pushforward
infrastructure codex built) lives in this repo (`markov-semigroups`);
sub-stages N2 + N3 (~90 lines combined) land downstream in
[`gaussian-hilbert`](https://github.com/mrdouglasny/gaussian-hilbert).*

*Companion docs:*
- *gaussian-hilbert `docs/hypercontractivity-discharge-plan.md` — top-level
  multi-route plan (Stage W vs Stage N).*
- *gaussian-hilbert `docs/stage-n-byproducts.md` — rationale for choosing
  Stage N over Stage W (note: byproducts beyond the concrete instance
  itself are deferred to the future-generalization project below).*
- *[`stage-n1-codex-brief.md`](stage-n1-codex-brief.md) (this dir) — codex
  hand-off brief for the N1 work.*

This is the working plan for discharging
`GaussianHilbert.ouSemigroupAct_eLpNorm_hypercontractive` (the last
axiom in gaussian-hilbert) without new axioms, by building the
multivariate Gaussian `BakryEmerySpace (Fin n → ℝ)` instance directly
from the 1D Mehler kernel and Fubini, then routing through
`gross_lsi_implies_hypercontractive`.

## Future generalization (TODO, separate project)

The concrete instance we ship now will eventually want to be a
consequence of a **generic** `BakryEmerySpace.pi` tensorization lemma.
That requires refactoring the `BakryEmerySpace` class to expose either:

- **A kernel mixin** — `HasKernel extends BakryEmerySpace` with
  `kernel : ℝ → MeasureTheory.Kernel X X` and
  `semigroup_eq_kernel : semigroup t f x = ∫ y, f y ∂(kernel t x)`.
  BGL-conventional, aligns with Mathlib's `MeasureTheory.Kernel`,
  works for discrete and continuous instances.
- **A tensor-product structure** — exposes the semigroup, Γ, and
  core via functorial tensor-product constructions, aligned with
  gaussian-field's existing `NuclearTensorProduct` infrastructure
  (see `~/Documents/GitHub/gaussian-field/GaussianField/Nuclear/`).
  More category-theoretic, more native to our codebase.

Both directions are ~2-3 week class refactors with their own
trade-offs. **Recommended sequencing**: ship the concrete instance
first (this plan), let it serve as a motivating example and concrete
sanity check, then revisit the abstraction layer with a focused
design pass. The concrete `stdGaussianFin.bakryEmerySpace n` we build
here will become a ~30-line consequence of the eventual generic
lemma — no rework, just shorter.

When the generalization project starts, consult both this plan and the
gaussian-field nuclear-tensor-product files for design choices and
existing API to leverage.

---

## Status

- **Pre-requisites done**:
  - Stage A — Mehler operator on `L²(γ_n)`, multivariate (2026-05-11) ✅
  - Stage Ag — `mehlerOp = ouSemigroupAct` agreement (2026-05-11) ✅
  - 1D `Gaussian1D.bakryEmerySpace : BakryEmerySpace ℝ`, now in
    `Instances/WorkInProgress/EuclideanEntropyDecay.lean`, **axiom-free**
    (the 4 historical textbook axioms were all discharged by
    2026-05-13, commits `1b3f797`, `6a89298`, `00cd52b`, `ab36ab0`) ✅
  - Bundled `DirichletMarkovSemigroup` in
    `MarkovSemigroups/Abstract/Hypercontractivity.lean:137`
    (commits `6e4ad85`, `371780b`) ✅
  - `gross_lsi_implies_hypercontractive` axiom in
    `MarkovSemigroups/Abstract/Hypercontractivity.lean:215` (now takes
    a `DirichletMarkovSemigroup`) ✅
- **In progress**: N1 on branch `feat/bakry-emery-multivariate-gaussian`.
  N1.0 (IsCoreFin + 9 closures), N1.1 (measure-side fields), N1.2 (Γ/energy +
  `dirichletSpaceFin` instance), N1.3 (semigroup zero/mean/contraction/
  selfAdjoint/compose plus kernel-pushforward infra), and the N1.4
  derivative bridge are all done (1371 lines, 0 axioms, 0 sorries).
- **Remaining**: N1.4 `gradient_decay`, N1.5 L²/entropy fields +
  `IsCore_semigroup`, N1.6 BE-instance wrap (~700-900 more lines),
  then N2 (instance at gaussian-hilbert, ~25 lines, `rfl` measure
  bridge), then N3 (wire-in via `DirichletMarkovSemigroup`, ~80-100
  lines).

---

## Dependency graph

```
       Gaussian1D.bakryEmerySpace (axiom-free)    gross_lsi_implies_hypercontractive
       (EuclideanEntropyDecay.lean)               (axiom in Abstract/Hypercontractivity.lean,
                                                   takes DirichletMarkovSemigroup)
                          │                                   │
                          ▼                                   │
              [N1] BakryEmerySpace.pi                         │
              ~300-400 lines, markov-semigroups               │
                          │                                   │
                          ▼                                   │
              [N2] stdGaussianFin.bakryEmerySpace n           │
              ~25 lines, gaussian-hilbert (μ-bridge is rfl)   │
                          │                                   │
                          ▼                                   │
              stdGaussianFin_satisfiesLogSobolev              │
                          │                                   │
                          └───────────────────┬───────────────┘
                                              ▼
                              [N3] ouSemigroupAct_eLpNorm_hypercontractive
                              ~50-80 lines, gaussian-hilbert
                              (replaces existing axiom)
```

---

## Sub-stage N1 — generic BE tensorization `BakryEmerySpace.pi`

**Location**: `MarkovSemigroups/Diffusion/CarreDuChampPi.lean` (new file).

**Goal**: prove that a finite product of BE spaces with the same curvature
ρ is again a BE space with the same ρ. The lemma signature:

```lean
def BakryEmerySpace.pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    [be : ∀ i, BakryEmerySpace (X i)]
    (ρ₀ : ℝ) (hρ : ∀ i, (be i).ρ = ρ₀) :
    BakryEmerySpace (∀ i, X i) where
  ρ := ρ₀
  μ := Measure.pi (fun i => (be i).μ)
  -- ... 21 more fields
```

### N1.0 — Pi-IsCore (~30 lines)

```lean
def IsCorePi {ι : Type*} [Fintype ι] {X : ι → Type*}
    [be : ∀ i, BakryEmerySpace (X i)] (f : (∀ i, X i) → ℝ) : Prop :=
  -- "Tensor closure" of 1D cores: f is a finite linear combination of
  -- tensor-product functions ∏ᵢ gᵢ(xᵢ) with each gᵢ ∈ (be i).IsCore.
  ...
```

Two design options:
1. **Concrete**: `IsCorePi f` ≡ `∃ s : Finset _, ∃ c : _ → ℝ, ∃ g : _ → ∀ i, X i → ℝ,
   f = ∑ k ∈ s, c k • (∏ᵢ g k i ·) ∧ ∀ k i, IsCore (g k i)`. Closure under
   product, addition, scalar mul is direct.
2. **Generic smooth-with-bounded-derivs**: `f ∈ C^2((∀i, Xᵢ), ℝ)` with bounded
   first/second partial derivatives. Cleaner statement but harder for tensor
   manipulations.

**Choice**: option 1 (concrete tensor closure) — keeps Fubini-style proofs
mechanical. Add helper lemmas: `IsCorePi.add`, `IsCorePi.smul`, `IsCorePi.mul`,
`IsCorePi.tensorMk` (build from 1D cores).

### N1.1 — measure-side fields (~40 lines)

| Field | Definition | Strategy |
|---|---|---|
| `μ` | `Measure.pi (fun i => (be i).μ)` | direct |
| `IsProbabilityMeasure` | `inferInstance` | Mathlib's `Measure.pi` of probability measures is probability |
| `IsCore` | `IsCorePi` (from N1.0) | direct |
| `IsCore_const` | constants are tensor products of 1D constants | trivial |
| `IsCore_add` | `IsCorePi.add` | direct |
| `IsCore_smul` | `IsCorePi.smul` | direct |

### N1.2 — energy / Γ tensor structure (~60 lines)

| Field | Definition | Strategy |
|---|---|---|
| `Γ_pi(f, g)` | `∑ i, ∫_{∏_{j≠i} X_j} Γ_i(f(·, x_{¬i}), g(·, x_{¬i})) d(μ_{¬i})` — coordinate-by-coordinate `Γ` on the "section function" | Direct on tensor cores: if `f = ∏ⱼ fⱼ`, then `Γ_pi(f, f) = ∑ᵢ (∏_{j≠i} fⱼ²) · Γᵢ(fᵢ, fᵢ)`; extend by bilinearity |
| `Γ_pi_symm` | follows from each `Γ_i` symmetric | trivial |
| `Γ_pi_nonneg` | each term is nonneg | trivial |
| `energy_pi(f, g)` | `∫ Γ_pi(f, g) d μ_pi` | def |
| `energy_eq_integral_Γ` | by definition | `rfl` after unfolding |
| `Γ_pi_leibniz` | tensor-of-product expansion + 1D Leibniz | ~20 lines |
| `Γ_pi_const` | `Γ_i(c, ·) = 0` per coord | trivial |
| `IsCore_mul` | `IsCorePi.mul` | direct |

The proper Γ-definition for arbitrary `f, g`:

```lean
Γ := fun f g x => ∑ i : ι, (be i).Γ
       (fun yᵢ => f (Function.update x i yᵢ))
       (fun yᵢ => g (Function.update x i yᵢ))
       (x i)
```

(i.e. fix all coordinates except `i`, treat the function as a 1D function
of `x i`, apply the 1D `Γ`, evaluate at `x i`, sum over `i`).

### N1.3 — semigroup tensor structure (~80 lines)

| Field | Definition | Strategy |
|---|---|---|
| `semigroup` | `(P_t f)(x) := ∫ ... ∫ f(P_t^{(1)} ⊗ ... ⊗ P_t^{(n)})...` (product semigroup) | Fubini |
| `semigroup_zero` | each `P_0^{(i)} = id` | trivial |
| `semigroup_add` | `P^{(i)}_{s+t} = P^{(i)}_s ∘ P^{(i)}_t` per coord + Fubini | ~15 lines |
| `IsCore_semigroup` | `IsCorePi` is preserved by per-coord 1D semigroup on tensor cores | ~10 lines |
| `semigroup_contraction` | tensor-lift of 1D L²-contraction via Fubini-on-tensor-decomposition | ~15 lines |
| `semigroup_mean` | tensor-lift of 1D mean preservation | ~10 lines |
| `semigroup_selfAdjoint` | tensor-lift of 1D self-adjointness | ~15 lines |

Concrete definition for `semigroup`:

```lean
semigroup := fun t f x =>
  -- Apply 1D semigroup to each coordinate in turn (order doesn't matter
  -- because 1D semigroups commute on independent factors).
  let φ : ι → (∀ i, X i) → ℝ := ...
  -- Cleanest formulation: use the product structure via Function.update.
  ...
```

Two formulations to choose between:
- **Per-coordinate iteration**: `Finset.prod` of partial 1D semigroups.
  Cleaner inductively; harder to do Fubini on.
- **Product integral**: `∫ ... ∫ f(...) ∏ⱼ K^{(j)}_t(xⱼ, yⱼ) dy₁ ... dy_n`,
  with `K^{(j)}_t` the 1D Mehler kernel (`(be j).semigroup` integral form).
  Direct Fubini access; needs the 1D semigroup-as-integral form.

**Choice**: product integral. We'll need to prove the 1D semigroup IS in
integral form first — for `Euclidean.bakryEmerySpace`, this is the Mehler
formula `ouSemigroup t f x = ∫ f(e^{-t} x + √(1-e^{-2t}) y) dγ(y)` (already
in `Euclidean.lean`).

### N1.4 — curvature condition (~70 lines)

This is the load-bearing field.

```lean
gradient_decay : ∀ f t ht hf,
  ∫ x, Γ_pi (semigroup_pi t f) (semigroup_pi t f) x ∂μ_pi ≤
  exp(-2 * ρ₀ * t) * ∫ x, Γ_pi f f x ∂μ_pi
```

**Proof strategy**: tensor-decompose both sides by coordinate:
```
LHS = ∑ᵢ ∫_{X_i} ∫_{X_{¬i}} Γᵢ(P_t f|_i, P_t f|_i)(xᵢ) d(μ_{¬i}) dμᵢ
```
For the inner integral with `x_{¬i}` fixed, `P_t f(·, x_{¬i})` is the
1D semigroup `(be i).semigroup t (f(·, x_{¬i}))` (the product semigroup
factors). Apply the 1D `gradient_decay`:
```
inner ≤ exp(-2ρ₀t) · ∫_{X_i} Γᵢ(f|_i, f|_i)(xᵢ) dμᵢ
```
Integrate over `x_{¬i}` and sum over `i`:
```
LHS ≤ exp(-2ρ₀t) · ∑ᵢ ∫ Γᵢ(f|_i, f|_i) ... = exp(-2ρ₀t) · RHS-without-exp.
```

Key sub-lemmas:
- `Γ_pi.section_eq_1d`: if `x_{¬i}` is fixed, the section of `Γ_pi(f, g)` in `x_i`
  equals `(be i).Γ (f(·, x_{¬i})) (g(·, x_{¬i}))`. ~10 lines.
- `semigroup_pi.section_eq_1d_semigroup`: if `x_{¬i}` is fixed, the section
  of `semigroup_pi t f` in `x_i` equals `(be i).semigroup t (f(·, x_{¬i}))`.
  ~15 lines (Fubini).

### N1.5 — L² decay and Fisher information fields (~60 lines)

| Field | Strategy |
|---|---|
| `semigroup_l2_decay_bound` | Tensor-Fubini lift, same pattern as gradient_decay |
| `semigroup_l2_sq_hasDerivWithinAt` | Differentiation under tensor integral; harder, ~25 lines |
| `semigroup_ergodic` | Per-coordinate ergodicity + product → joint ergodicity |
| `semigroup_entropy_sq_decay_bound` | Same pattern, but entropy decomposition over tensor product |
| `semigroup_entropy_sq_ergodic` | Per-coordinate + product |

The entropy-decomposition is delicate: `Ent(f²)` does *not* in general
tensor-decompose as a sum, but the inequality
`Ent_{μ_pi}(g) ≤ Σᵢ E_{μ_{¬i}}[Ent_{μᵢ}(g(·, x_{¬i}))]` does hold
(this is essentially LSI tensorization in disguise). For our specific use
(entropy of a non-negative `f²`), Fubini + 1D entropy decay per coordinate
gives the right bound.

Risk: this might secretly invoke an LSI-tensorization-style fact. If so,
we either prove it inline (~30 lines, doable) or factor it as a clearly-named
lemma `entropy_tensorize_le`.

### N1.6 — wrap into instance + theorem (~20 lines)

```lean
instance BakryEmerySpace.pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    [be : ∀ i, BakryEmerySpace (X i)]
    (h_rho_uniform : ∀ i, (be i).ρ = (be (Classical.arbitrary ι)).ρ) :
    BakryEmerySpace (∀ i, X i) := { /- 22 fields -/ }
```

Then `BakryEmerySpace.pi.satisfiesLogSobolev` follows from the existing
`satisfiesLogSobolev` theorem on `BakryEmerySpace` (BGL Thm 5.7.1, already
proved in markov-semigroups).

### N1 totals

| Sub-section | Lines | Days |
|---|---|---|
| N1.0 IsCore | 30 | 0.5 |
| N1.1 measure fields | 40 | 0.5 |
| N1.2 Γ/energy | 60 | 1.5 |
| N1.3 semigroup | 80 | 2 |
| N1.4 gradient_decay | 70 | 1.5 |
| N1.5 L²/entropy fields | 60 | 1.5 |
| N1.6 wrap | 20 | 0.5 |
| **N1 total** | **~360** | **~7-8** |

---

## Sub-stage N2 — instantiate at `stdGaussianFin n`

**Location**: `GaussianHilbert/BakryEmeryInstance.lean` (new file).

**The μ-bridge is `rfl`.** `stdGaussianFin n` is already *defined* as a
product measure in `GaussianHilbert/HermitePolynomials.lean:73`:

```lean
noncomputable def stdGaussianFin (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)
```

So the `μ` field of `BakryEmerySpace.pi (fun _ => Euclidean.bakryEmerySpace)`
reduces (defeq) to `stdGaussianFin n`. No characteristic-function uniqueness,
no Dynkin π-system argument, no measure-bridge lemma needed.

```lean
import GaussianHilbert.HermitePolynomials  -- for stdGaussianFin
import MarkovSemigroups.Diffusion.CarreDuChampPi  -- N1
import MarkovSemigroups.Instances.WorkInProgress.Euclidean  -- 1D BE

namespace GaussianHilbert

instance stdGaussianFin.bakryEmerySpace (n : ℕ) :
    BakryEmerySpace (Fin n → ℝ) :=
  BakryEmerySpace.pi (ρ₀ := 1)
    (fun _ : Fin n => MarkovSemigroups.Instances.Euclidean.bakryEmerySpace)
    (fun _ => rfl)

-- Sanity check that the μ field really does reduce to stdGaussianFin n.
example (n : ℕ) :
    (stdGaussianFin.bakryEmerySpace n).μ = stdGaussianFin n := rfl

theorem stdGaussianFin_satisfiesLogSobolev (n : ℕ) :
    DirichletSpace.SatisfiesLogSobolev
      (ds := (stdGaussianFin.bakryEmerySpace n).toDirichletSpace) 1 :=
  BakryEmerySpace.satisfiesLogSobolev (be := stdGaussianFin.bakryEmerySpace n)
```

### N2 totals

| Item | Lines | Days |
|---|---|---|
| Instance + LSI theorem + smoke test | 25 | 0.5 |
| **N2 total** | **~25** | **~0.5** |

---

## Sub-stage N3 — wire `ouSemigroupAct_eLpNorm_hypercontractive`

**Location**: `GaussianHilbert/OUEigenfunctions.lean` (replace existing axiom).

```lean
theorem ouSemigroupAct_eLpNorm_hypercontractive {n : ℕ}
    (p : ℝ) (hp : 2 ≤ p) (t : ℝ) (ht : 0 ≤ t)
    (h_nelson : p - 1 ≤ Real.exp (2 * t))
    (f : MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) :
    MeasureTheory.eLpNorm
        ((ouSemigroupAct n t f : (Fin n → ℝ) → ℝ))
        (ENNReal.ofReal p) (stdGaussianFin n) ≤
      MeasureTheory.eLpNorm
        ((f : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) := by
  -- Step 1: replace ouSemigroupAct with mehlerOp (Stage Ag).
  rw [mehlerOp_eq_ouSemigroupAct.symm]
  -- Now goal is about mehlerOp.
  -- Step 2: identify mehlerOp with the BE-instance's semigroup (pointwise a.e.).
  -- Step 3: apply gross_lsi_implies_hypercontractive with the BE-LSI.
  have h_lsi := stdGaussianFin_satisfiesLogSobolev n
  -- ... bridge the abstract HC statement to the concrete eLpNorm form
  exact gross_lsi_implies_hypercontractive
    (be := stdGaussianFin.bakryEmerySpace n)
    ... p hp t ht h_nelson f ...
```

The bridge involves three small adapters:
1. `ouSemigroupAct = mehlerOp` (Stage Ag, ✅ done).
2. `mehlerOp n t ht f` (an `Lp` element) corresponds to the pointwise
   `(stdGaussianFin.bakryEmerySpace n).semigroup t f₀` where `f₀ : (Fin n → ℝ) → ℝ`
   is a representative of `f`. ~15 lines.
3. The abstract `IsHypercontractive` predicate from
   `MarkovSemigroups.Abstract.Hypercontractivity` re-expressed as an
   `eLpNorm` inequality on `Lp` elements. ~20 lines.

Adapter 3 may require lemma migration if the abstract predicate uses
`∫ |f|^p` rather than `eLpNorm`. Trivial conversion, but mechanical.

### N3 totals

| Item | Lines | Days |
|---|---|---|
| Bridge adapter 1 (`ouSemigroupAct = mehlerOp`) | 0 (done) | 0 |
| Bridge adapter 2 (`mehlerOp` vs BE semigroup) | 15 | 0.5 |
| Bridge adapter 3 (abstract HC → eLpNorm) | 20 | 0.5 |
| Wiring theorem | 30 | 0.5 |
| **N3 total** | **~65** | **~1.5** |

---

## Overall effort

| Sub-stage | Lines | Days |
|---|---|---|
| N1 — `BakryEmerySpace.pi` (markov-semigroups) | ~360 | 7-8 |
| N2 — `stdGaussianFin.bakryEmerySpace n` | ~25 | 0.5 |
| N3 — Stage E wire-in | ~65 | 1.5 |
| **Total** | **~450** | **~9-10** |

Under **2 weeks active work**, lower than the original ~600/14-day estimate
because (a) the 1D infrastructure is already in place, (b) Stage Ag is done,
and (c) `stdGaussianFin n` is *already* defined as `Measure.pi`, so N2's
measure bridge is `rfl`. Aim for ~2-2.5 weeks wall-clock allowing for
review cycles.

---

## Cross-repo task ordering

1. **Open a markov-semigroups branch** `feat/bakry-emery-tensorization`.
2. **N1.0–N1.6**: build `CarreDuChampPi.lean` incrementally, sub-section by
   sub-section. Build clean after each. Verify with `#print axioms` per field
   — all should reduce to `Classical.choice`, `propext`, `Quot.sound`, plus
   the four 1D BE axioms in `Euclidean.lean`.
3. **PR + merge** N1 into markov-semigroups `main`.
4. **Bump markov-semigroups pin** in gaussian-hilbert (`lake-manifest.json`).
5. **Open gaussian-hilbert branch** `feat/stage-n-hypercontractivity`.
6. **N2**: create `BakryEmeryInstance.lean`. `stdGaussianFin_eq_pi` bridge
   first, then instance, then LSI theorem.
7. **N3**: in `OUEigenfunctions.lean`, convert
   `axiom ouSemigroupAct_eLpNorm_hypercontractive` to a `theorem` with
   the wire-in proof.
8. **Verify** with `#print axioms ouSemigroupAct_eLpNorm_hypercontractive`
   — expect Mathlib + 1D BE axioms + Gross HC axiom, no new symbols.
9. **Update** `AXIOM_AUDIT.md` to mark the axiom discharged.
10. **PR + merge** into gaussian-hilbert `main`.

---

## Verification checkpoints

After each sub-stage, run:
- `lake build` (full project clean)
- `#print axioms <theorem>` (axiom closure check)
- For N1: each filled field should compile + a sample instance
  (e.g. `Fin 2 → ℝ`) should typecheck and the LSI theorem evaluates.

After Stage N3:
- `#print axioms ouSemigroupAct_eLpNorm_hypercontractive` should yield
  exactly:
  ```
  [propext, Classical.choice, Quot.sound,
   MarkovSemigroups.gross_lsi_implies_hypercontractive,
   MarkovSemigroups.Instances.Euclidean.ouSemigroup_preserves_IsCore,
   MarkovSemigroups.Instances.Euclidean.ouSemigroup_gradient_decay,
   MarkovSemigroups.Instances.Euclidean.ouSemigroup_l2_sq_hasDerivWithinAt,
   MarkovSemigroups.Instances.Euclidean.ouSemigroup_entropy_sq_decay_bound]
  ```
  i.e. the 4 1D BE axioms + the Gross HC axiom + standard Mathlib core.
- All downstream consumers (`bonami_nelson_chaos`, `polynomial_chaos_concentration`)
  rebuild successfully.

---

## Risks and exit ramps

### Risk 1: N1.4 (`gradient_decay`) Fubini gets stuck

The section-function manipulations (`f(·, x_{¬i})` as a 1D function with the
rest fixed) need careful measurability and integrability tracking. Mathlib's
Fubini API (`MeasureTheory.integral_prod` etc.) is robust but the explicit
section-via-`Function.update` formulation may need helper lemmas.

**Exit ramp**: introduce **one** clean helper axiom `section_function_isCore`
(if `f` is `IsCorePi` and we fix all coordinates but `i`, the resulting 1D
function is `(be i).IsCore`) — gemini-vet it as a standard fact. Saves
~2 days.

### Risk 2: N1.5 entropy tensorization

If `Ent_{μ_pi}(g) ≤ Σᵢ E_{μ_{¬i}}[Ent_{μᵢ}(g(·, x_{¬i}))]` turns out to be
load-bearing and harder than expected, retreat to **Stage W** for just this
field: postulate `lsi_tensorize` as an axiom, prove the other 21 fields,
state the entropy field as a consequence.

This is a degenerate version where Stage N is "Stage W with the structural
pieces from Stage N". Adds 1 axiom but keeps the BE instance and the
~8 byproducts.

### Risk 3 (retired): N2 measure bridge

Eliminated by inspection: `stdGaussianFin n` is already defined as
`Measure.pi (fun _ : Fin n => gaussianReal 0 1)`
(`GaussianHilbert/HermitePolynomials.lean:73`), so the μ field of
`BakryEmerySpace.pi` reduces defeq and the bridge is `rfl`.

### Risk 4: N3 abstract-HC adapter mismatches

If the abstract `IsHypercontractive` predicate uses an integral-pairing
form incompatible with `eLpNorm`, an `eLpNorm`-bridge lemma may need to
go upstream into markov-semigroups. ~20 extra lines, ~0.5 days.

---

## Test plan

- **Per-field unit test**: in N1, after filling each field, write a
  `#check` and `#print axioms` for the partial instance to confirm no
  accidental new axioms.
- **N2 sanity check**: `example : (stdGaussianFin.bakryEmerySpace 1).ρ = 1
  := rfl` and similar.
- **End-to-end test**: build `pphi2/Pphi2/...` (if it consumes
  hypercontractivity) successfully after the bump.

---

## Out of scope

- Discharging the 4 existing 1D BE axioms in
  `MarkovSemigroups.Instances.WorkInProgress.Euclidean.lean`. Those remain
  the "textbook axioms" the BGL framework rests on. Discharging them is a
  separate effort (~2-3 weeks per axiom, BGL Ch. 2 proofs).
- Discharging `gross_lsi_implies_hypercontractive`. Same — the abstract
  Gross 1975 LSI ⇒ HC theorem is its own ~600-line effort.
- The Mehler-derivative commutation lemma as a *standalone* result.
  Stage N doesn't need it directly because the 1D BE axioms encode it
  implicitly; if we want a standalone Lean proof of
  `∂ᵢ ∘ M_t = e^{-t} · M_t ∘ ∂ᵢ`, that's a separate ~150-line effort
  (see [`stage-n-byproducts.md`](stage-n-byproducts.md) §"Mehler-derivative
  commutation lemma" for why it's independently valuable).
