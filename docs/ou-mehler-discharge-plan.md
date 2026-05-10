# OU / Mehler-kernel discharge plan

*Drafted 2026-05-09. Plan for discharging the three placeholder axioms in
`Gaussian/OUEigenfunctions.lean` (`ouSemigroupAct`,
`ouSemigroupAct_eq_smul_of_mem_wienerChaos`,
`ouSemigroupAct_eLpNorm_hypercontractive`) via the Mehler kernel +
Bakry-Émery + Gross route. Companion to
[polynomial-chaos-roadmap.md](polynomial-chaos-roadmap.md), which lists
the Mehler infrastructure as the principal remaining work item.*

## Goal

Replace the three placeholder axioms with proved theorems, defined
through the explicit Mehler integral on `L²(γ_n)`, with hypercontractivity
inherited from `gross_lsi_implies_hypercontractive` (existing axiom in
`Abstract/Hypercontractivity.lean`).

After this work, the polynomial-chaos pipeline
(`polynomial_chaos_concentration` and the Bonami-Nelson `bonami_nelson_*`
theorems) transitively rests only on:
- `polynomial_dense_L2_of_subGaussian` (gaussian-field, Janson Thm 2.6)
- `gross_lsi_implies_hypercontractive` (existing axiom, Gross 1975)
- the 4 BGL Ch. 2 textbook axioms in `Instances/WorkInProgress/Euclidean.lean` (1D Mehler-kernel facts)

All four are well-cited textbook items.

## Background

The OU semigroup `T_t` on `L²(γ_n)` is `e^{-tL}` for the OU generator
`L = Δ - x · ∇`. Its closed-form representation is the **Mehler kernel**:
$$
(T_t f)(x) \;=\; \int_{\mathbb{R}^n} f\!\left(e^{-t}\,x \,+\, \sqrt{1 - e^{-2t}}\;y\right)\, d\gamma_n(y).
$$

Janson Theorem 5.10 (the Bonami-Beckner-Nelson hypercontractive bound)
needs three OU-side facts:

1. The semigroup operator `T_t` itself, as a CLM `Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n)`.
2. The eigenvalue action: `T_t H_α = e^{-|α|t} H_α` for any multivariate Hermite polynomial `H_α`, extended by linearity + density to all of `wienerChaos n |α|`.
3. The hypercontractive bound: `‖T_t f‖_{L^p} ≤ ‖f‖_{L^q}` whenever `e^{2t}(p-1) ≥ q-1` (Nelson's bound).

These are the three placeholder axioms in `Gaussian/OUEigenfunctions.lean`.

## Architecture

```
                                                         ┌──────────────────────────────────────────────┐
                                                         │ Existing: gross_lsi_implies_hypercontractive │
                                                         │  (axiom in Abstract/Hypercontractivity)      │
                                                         └────────────────────┬─────────────────────────┘
                                                                              │
                                                                              ▼
┌──────────────────┐    ┌─────────────────────┐    ┌─────────────────────────┐    ┌─────────────────────────┐
│  Stage A         │    │  Stage B            │    │  Stage C                │    │  Stage E                │
│  Mehler operator │───▶│  Markov semigroup   │───▶│  BakryEmerySpace        │───▶│  hypercontractivity     │
│  on L²(γ_n)      │    │  laws (semigroup,   │    │  (Fin n → ℝ)            │    │  on ouSemigroupAct      │
│                  │    │  contraction, mean) │    │  with curvature ρ = 1   │    │  via Gross              │
└──────────────────┘    └─────────────────────┘    └─────────────────────────┘    └─────────────────────────┘
        │                                                     ▲
        │                                                     │
        ▼                                       ┌─────────────────────────────┐
┌──────────────────┐                            │ Existing: Gaussian1D.       │
│  Stage C′        │                            │ bakryEmerySpace (1D, ρ = 1, │
│  Hermite eigen-  │                            │ 4 BGL Ch. 2 axioms +        │
│  values via 1D   │                            │ proven scaffolding)         │
│  Mehler-Hermite  │                            └─────────────────────────────┘
│  identity        │
└──────────────────┘
```

Stages A + B + C′ are independent of Bakry-Émery and discharge
`ouSemigroupAct` + `ouSemigroupAct_eq_smul_of_mem_wienerChaos` on their
own. Stages C + E gate the hypercontractivity discharge.

## Stage A — Mehler operator on L² (~250 lines, ~5-7 days, no new axioms)

Create `MarkovSemigroups/Gaussian/MehlerKernel.lean`:

```lean
/-- The Mehler operator on functions:
    `(M_t f)(x) := ∫ f(e^{-t}·x + √(1-e^{-2t})·y) dγ_n(y)`. -/
noncomputable def mehlerFun (n : ℕ) (t : ℝ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x =>
    ∫ y, f (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2*t)) • y)
      ∂(stdGaussianFin n)

/-- Measurability of the integrand pre-Fubini. -/
lemma mehlerFun_measurable (n : ℕ) (t : ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) :
    Measurable (mehlerFun n t f) := ...

/-- L²-contraction: `∫ (M_t f)² ≤ ∫ f²` by Jensen's inequality, plus
    invariance of `γ_n × γ_n` under the linear map
    `(x, y) ↦ (e^{-t}x + √(1-e^{-2t})y, ·)`. -/
lemma mehlerFun_memLp (n : ℕ) (t : ℝ) (ht : 0 ≤ t) {f}
    (hf : MemLp f 2 (stdGaussianFin n)) :
    MemLp (mehlerFun n t f) 2 (stdGaussianFin n) ∧
    ∫ x, (mehlerFun n t f x)^2 ∂(stdGaussianFin n) ≤
      ∫ x, (f x)^2 ∂(stdGaussianFin n) := ...

/-- The Mehler operator descends to a CLM on L². -/
noncomputable def mehlerOp (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n) := ...
```

**Nontrivial bits:**
- The change-of-variables `(x, y) ↦ e^{-t}x + √(1-e^{-2t})y` is
  measure-preserving on `γ_n` when `y ~ γ_n`. This is the concrete
  Gaussian fact behind L²-contraction and the closure under L².
- Descent from a function-level operator to an `Lp` CLM. Mathlib has
  `Lp.boundedContinuousLp_of_*` patterns for similar cases.

## Stage B — Markov semigroup laws (~200 lines, ~3-5 days, no new axioms)

Same file or `Gaussian/MehlerSemigroup.lean`:

```lean
/-- Semigroup property: `M_s ∘ M_t = M_{s+t}`, by collapsing the double
    Mehler integral via the variance identity
    `e^{-2s}(1 - e^{-2t}) + (1 - e^{-2s}) = 1 - e^{-2(s+t)}`. -/
theorem mehlerOp_comp (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (mehlerOp n s hs).comp (mehlerOp n t ht) =
      mehlerOp n (s + t) (by linarith) := ...

/-- `M_0 = id`. -/
theorem mehlerOp_zero (n : ℕ) :
    mehlerOp n 0 (le_refl _) = ContinuousLinearMap.id _ _ := ...

/-- `M_t` preserves constants: `M_t 1 = 1`. -/
theorem mehlerOp_const_one (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    mehlerOp n t ht (constLp 1) = constLp 1 := ...

/-- `M_t` preserves the integral (mean): `∫ M_t f = ∫ f`. -/
theorem mehlerOp_integral (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (stdGaussianFin n)) :
    ∫ x, (mehlerOp n t ht f) x ∂(stdGaussianFin n) =
      ∫ x, f x ∂(stdGaussianFin n) := ...
```

**Nontrivial bit:** the semigroup property. The variance-collapse
identity is one line of arithmetic, but lifting it through the Lp /
Fubini layers takes care.

## Stage C′ — Hermite eigenvalues (~250 lines, ~5-7 days, no new axioms)

Either a new file `Gaussian/MehlerHermite.lean` or extension of
`Gaussian/OUEigenfunctions.lean`:

```lean
/-- **Mehler-Hermite identity (1D).**
    `∫ He_k(e^{-t}·x + √(1-e^{-2t})·y) dγ(y) = e^{-kt} · He_k(x)`.

    Reference: Janson, *Gaussian Hilbert Spaces*, §3.4 formula (3.5);
    Nualart, *The Malliavin Calculus*, §1.4.

    Proof: substitute the Hermite generating function
    `∑ He_n(x) z^n / n! = exp(zx - z²/2)` into the LHS, exchange sum and
    integral (justified by absolute convergence on a strip), perform the
    Gaussian integral in `y`, and read off the coefficient of `z^k`. -/
theorem mehler_hermite_identity_1d (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    ∫ y, hermiteEval k (Real.exp (-t) * x +
                         Real.sqrt (1 - Real.exp (-2*t)) * y)
        ∂(gaussianReal 0 1) =
      Real.exp (-(k : ℝ) * t) * hermiteEval k x := ...

/-- **Multivariate Mehler-Hermite identity.** Tensor product of the 1D
    identity over coordinates, by Fubini on the pi-measure. -/
theorem mehlerOp_hermiteMultiLp (n : ℕ) (α : Fin n → ℕ) (t : ℝ) (ht : 0 ≤ t) :
    mehlerOp n t ht (hermiteMultiLp α) =
      Real.exp (-(MultiIndex.totalDegree α : ℝ) * t) • hermiteMultiLp α := ...

/-- Discharges `ouSemigroupAct_eq_smul_of_mem_wienerChaos`: every
    `f ∈ wienerChaos n k` is an L² limit of finite Hermite combinations
    with all multi-indices of total degree `k`; by continuity of `M_t`
    and linearity, `M_t` acts by `e^{-kt}` on the whole closure. -/
theorem mehlerOp_smul_of_mem_wienerChaos (n k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (stdGaussianFin n)) (hf : f ∈ wienerChaos n k) :
    mehlerOp n t ht f = Real.exp (-(k : ℝ) * t) • f := ...
```

**Nontrivial bit:** the 1D Mehler-Hermite identity. The generating-function
proof is the cleanest formalization path; alternatives (induction on `k` +
integration by parts; direct Rodrigues-formula manipulation) are also
viable but typically longer.

## Stage C — multivariate BakryEmerySpace (~600 lines, ~10-14 days, no new axioms)

Create `MarkovSemigroups/Gaussian/BakryEmeryInstance.lean`:

```lean
/-- The standard Gaussian on `Fin n → ℝ` as a Bakry-Émery space with
    curvature ρ = 1. Filled fields:

    - **Γ_n(f, g) = ∑ᵢ ∂ᵢf · ∂ᵢg** (Euclidean carré du champ)
    - **semigroup = mehlerOp** (Stage A)
    - **IsCore_mul, Γ_leibniz, Γ_const**: direct multivariate calculus.
    - **gradient_decay** (the BE curvature condition):
      `∫ ‖∇(M_t f)‖² ≤ e^{-2t} ∫ ‖∇f‖²`.
      Proved from the **Mehler-derivative commutation lemma**
      `∂ᵢ ∘ M_t = e^{-t} · M_t ∘ ∂ᵢ` (chain rule + dominated convergence
      to differentiate under the Gaussian integral) plus L²-contraction
      of `M_t` per coordinate.
    - **semigroup_l2_decay_bound, semigroup_l2_sq_hasDerivWithinAt,
      semigroup_entropy_sq_decay_bound**: tensor-lift from 1D via Fubini.
      The 1D versions are exactly the 4 BGL Ch. 2 axioms in
      `Instances/WorkInProgress/Euclidean.lean`; the n-D version becomes
      a proved theorem dependent on those (no new axioms). -/
noncomputable def stdGaussianFin.bakryEmerySpace (n : ℕ) :
    BakryEmerySpace (Fin n → ℝ) where
  ρ := 1
  hρ := one_pos
  Γ := fun f g x => ∑ i, fderiv ℝ f x (Pi.single i 1) *
                          fderiv ℝ g x (Pi.single i 1)
  semigroup := fun t f => if h : 0 ≤ t then mehlerFun n t f else f
  -- ... 14 more fields ...

/-- Standard Gaussian satisfies LSI(1) (Bakry-Émery + curvature 1). -/
theorem stdGaussianFin_satisfiesLogSobolev (n : ℕ) :
    SatisfiesLogSobolev (stdGaussianFin n) 1 :=
  (stdGaussianFin.bakryEmerySpace n).satisfiesLogSobolev
```

**Nontrivial bits:**
- The BakryEmerySpace class has 16 fields. Most are routine but tedious.
- The **Mehler-derivative commutation lemma** is the load-bearing new
  fact: `∂ᵢ((M_t f)(x)) = e^{-t} · (M_t (∂ᵢ f))(x)`. Proved by
  differentiating the Mehler integral under the integral sign (DCT) and
  using the chain rule `∂ᵢ f(e^{-t}·x + √(1-e^{-2t})·y) = e^{-t} · (∂ᵢ f)(...)`.
  ~50-100 lines in Lean.
- Tensor-lift of the 1D entropy/L²-decay axioms. Coordinate-wise integration
  by Fubini; each coordinate uses the 1D fact. The cleanest formulation
  uses the fact that the OU semigroup tensorizes:
  `M_t^{(n)} = M_t^{(1)} ⊗ ... ⊗ M_t^{(1)}` (n copies), but a direct
  proof avoiding Hilbert tensor products is possible by working
  pointwise with the n-D Mehler integral.

### Optional shortcut: Stage C-β (no full BE instance, +1 axiom)

If building the full BakryEmerySpace instance is too expensive, a
shortcut: postulate the LSI tensorization fact directly.

```lean
/-- **LSI tensorizes** with the same constant: if each `μᵢ` satisfies
    LSI(c), then `Measure.pi μ` satisfies LSI(c).

    Reference: Gross (1975), main tensorization argument; BGL §5.2.4
    Proposition 5.2.7. Currently absent from Mathlib.

    (NOT VERIFIED) -/
axiom lsi_tensorize {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] {μ : ∀ i, Measure (α i)}
    [∀ i, IsProbabilityMeasure (μ i)] {c : ℝ}
    (h : ∀ i, SatisfiesLogSobolev (μ i) c) :
    SatisfiesLogSobolev (Measure.pi μ) c

/-- Standard Gaussian satisfies LSI(1) via tensorization of the 1D fact. -/
theorem stdGaussianFin_satisfiesLogSobolev (n : ℕ) :
    SatisfiesLogSobolev (stdGaussianFin n) 1 :=
  lsi_tensorize (fun _ => Gaussian1D.bakryEmerySpace.satisfiesLogSobolev)
```

**Trade-off:** +1 well-cited axiom (LSI tensorization), but eliminates
the need for the full multivariate BakryEmerySpace instance. ~250 lines
of work instead of ~600. Saves ~7 days.

## Stage E — wire into ouSemigroupAct (~50 lines, ~3-5 days)

In `MarkovSemigroups/Gaussian/OUEigenfunctions.lean`, replace the three
axioms:

```lean
/-- The OU semigroup acting on L²(γ_n). Defined as the Mehler operator. -/
noncomputable def ouSemigroupAct (n : ℕ) (t : ℝ) :
    Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n) :=
  if h : 0 ≤ t then mehlerOp n t h else ContinuousLinearMap.id _ _

/-- Eigenvalue action — direct from Stage C′. -/
theorem ouSemigroupAct_eq_smul_of_mem_wienerChaos {n : ℕ} (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (stdGaussianFin n)) (hf : f ∈ wienerChaos n k) :
    ouSemigroupAct n t f = Real.exp (-(k : ℝ) * t) • f := by
  unfold ouSemigroupAct
  rw [dif_pos ht]
  exact mehlerOp_smul_of_mem_wienerChaos n k t ht f hf

/-- Hypercontractivity — Gross applied to LSI(1) for the Mehler semigroup. -/
theorem ouSemigroupAct_eLpNorm_hypercontractive {n : ℕ}
    (p : ℝ) (hp : 2 ≤ p) (t : ℝ) (ht : 0 ≤ t)
    (h_nelson : p - 1 ≤ Real.exp (2 * t))
    (f : Lp ℝ 2 (stdGaussianFin n)) :
    eLpNorm ((ouSemigroupAct n t f : (Fin n → ℝ) → ℝ))
            (ENNReal.ofReal p) (stdGaussianFin n) ≤
      eLpNorm ((f : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) := by
  -- Translate gross_lsi_implies_hypercontractive applied to the Mehler
  -- semigroup with LSI constant 1; the Nelson bound `e^{2t} ≥ p - 1`
  -- with q = 2 reads off as the abstract HC predicate.
  ...
```

**Nontrivial bit:** the abstract `IsHypercontractive` predicate from
`Abstract/Hypercontractivity.lean` is in terms of the abstract
`MarkovSemigroup`'s associated `eLpNorm`. The bridge to our explicit
`ouSemigroupAct` may need a small adapter — typically a `simp`-able
restatement showing `mehlerOp ↔ MarkovSemigroup.act` for the BE-derived
semigroup.

## Effort summary

| Stage | Lines | Days | New axioms |
|---|---|---|---|
| A — Mehler operator | ~250 | 5-7 | 0 |
| B — semigroup laws | ~200 | 3-5 | 0 |
| C′ — Hermite eigenvalues | ~250 | 5-7 | 0 |
| **Subtotal A+B+C′ (discharges 2 of 3 axioms)** | **~700** | **~2 wk** | **0** |
| C-α — full BE instance | ~600 | 10-14 | 0 |
| C-β — LSI tensorization shortcut | ~250 | 5-7 | +1 (`lsi_tensorize`) |
| E — wire in HC | ~50 | 3-5 | 0 |

**Total via D-ii.α (full BE):** ~1350 lines, ~3-4 weeks. Drops the 3 OU
placeholder axioms with no new axioms; pipeline rests on existing 4
Gaussian1D BGL + `polynomial_dense_L2_of_subGaussian` + `gross_lsi_implies_hypercontractive`.

**Total via D-ii.β (LSI tensorization shortcut):** ~1000 lines, ~2.5-3 weeks.
Drops the 3 OU axioms but adds 1 well-cited axiom (`lsi_tensorize`).

## Recommended order

1. **Phase 1 (Stages A + B + C′, ~2 weeks).** Discharges
   `ouSemigroupAct` and `ouSemigroupAct_eq_smul_of_mem_wienerChaos` as
   independent, self-contained Mehler-kernel work. No new axioms, no
   dependence on Bakry-Émery machinery. After this, `polynomial_chaos_concentration`
   has 1 OU axiom remaining (`ouSemigroupAct_eLpNorm_hypercontractive`)
   instead of 3.

2. **Pause and reassess.** The hypercontractivity discharge is the
   load-bearing piece for `polynomial_chaos_concentration`'s
   Bonami-Nelson. Whether to commit to Phase 2 depends on whether the
   1-axiom residual is acceptable for downstream consumers (pphi2N's
   Cluster A wiring), or whether full discharge is required.

3. **Phase 2 (Stages C/E, ~2 weeks for D-ii.β / ~3 weeks for D-ii.α).**
   Build the BE instance (or shortcut to LSI tensorization) and wire HC
   through Gross. Discharges the third axiom.

## Reusable infrastructure

The Mehler-kernel machinery built here is reusable for several other
projects:

- **pphi2N** (O(N) sigma model): same OU-on-Gaussian structure for
  vector-valued fields.
- **gaussian-field**: the Mehler operator on L²(γ_C) for general
  covariance C is the abstract counterpart; a future extension would
  generalize from `stdGaussianFin n` to arbitrary positive-trace-class C.
- **Schwartz / nuclear OU**: the infinite-dimensional Mehler kernel on
  Schwartz space is the natural setting for the QFT side of this work
  (Glimm-Jaffe Ch. 8); the finite-dim case here is the lattice
  approximation that all rigorous estimates pass through.

## Risks

- **Mehler-derivative commutation lemma** (`∂ᵢ ∘ M_t = e^{-t} · M_t ∘ ∂ᵢ`,
  needed for Stage C-α): differentiating under the Gaussian integral
  sign requires DCT with explicit dominating function. The Mathlib
  pattern is `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_*`;
  if no convenient version exists for the Gaussian density's exponential
  decay, this could expand by ~100 lines.
- **Lp / function bridge** in Stage E: the abstract `IsHypercontractive`
  is in terms of an abstract Markov semigroup's `act` operator; if the
  signature mismatch with our explicit `ouSemigroupAct` is severe, a
  small bridge layer (~50 lines) may be needed.
- **Lift of 1D BGL axioms to nD** (Stage C-α): the 1D axioms are stated
  pointwise on smooth `f : ℝ → ℝ`; lifting to multivariate requires
  Fubini applied to integrands like `Γ_n(M_t f, M_t f) = ∑ᵢ (∂ᵢ M_t f)²`,
  which decomposes coordinate-wise *only* if `f` factorizes — for general
  `f` the lift goes through a denseness argument (smooth tensor products
  are dense in `L²`-with-gradient).

## Exit ramps

- If Stage C-α's BE instance turns out to be a 4+ week project (not 2
  weeks), retreat to Stage C-β's LSI tensorization shortcut. Adds 1
  axiom but cuts ~7 days.
- If Stage C′'s 1D Mehler-Hermite identity proves harder than expected
  (the generating-function approach can run into power-series
  convergence subtleties), fall back to a direct induction-on-`k` proof
  via integration by parts — longer but avoids analytic-function
  machinery.
- If the entire Mehler infrastructure stalls, the existing 3 OU
  placeholder axioms can stay; downstream consumers (pphi2N) can be
  configured to acknowledge them as well-cited textbook items rather
  than pursuing the full Lean discharge.
