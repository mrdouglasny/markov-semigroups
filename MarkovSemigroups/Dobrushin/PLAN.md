# Combined Plan: Dobrushin Theory Completion

*Updated 2026-04-15 after Gemini 3 Pro review*

## Current state

- ✅ `influenceCoeff` correctly uses marginal TV (fixed)
- ✅ `marginalTvDist_contraction`: marginalTvDist ≤ α · tvDist (proved)
- ✅ `TVCoupling`: coupling characterization, maximal coupling, Lipschitz-TV (all proved)
- ✅ `StrongCoupling`: nearest-neighbor verification for ℤ^d (fully proved)
- ❌ `hMargToFull`: FALSE hypothesis — needs removal (Gemini 3 Pro)
- ⚠️ `dobrushin_uniqueness`: conditional on false bridge — needs restructuring
- ⚠️ `dobrushin_correlation_decay`: currently a bridge hypothesis — the real target

## Key insight from Gemini 3 Pro review

**For finite lattices, uniqueness is TRIVIAL** (DLR at Λ = univ makes μ = γ(univ, ·)).
Dobrushin's condition is only needed for:
1. **Infinite-lattice uniqueness** (requires Wasserstein or π-λ)
2. **Correlation decay** (the physical mass gap, works on finite lattice)

Our lgt application needs only (2). The `hMargToFull` dead-end is a
non-issue: we don't need full-TV uniqueness, we need correlation decay.

## Phase B: Local observables + π-λ → Correlation decay (IMMEDIATE)

**Goal:** Prove `dobrushin_correlation_decay` without bridge hypothesis:
```lean
|∫ f·g dμ - (∫f dμ)(∫g dμ)| ≤ C · α^{dist(x,y)}
```
for local observables f at x, g at y.

### B1: Neumann series bound (~200 lines)

```lean
/-- The Neumann series ((I-C)⁻¹)_{xy} bound. For Dobrushin condition
with ‖C‖ ≤ α < 1: (I-C)⁻¹_{xy} ≤ α^{dist(x,y)} / (1-α). -/
lemma influence_neumann_bound (hD : DobrushinCondition γ)
    (x y : I) (dist : I → I → ℕ) (h_local : influence has finite support) :
    ∑' n, (iterateInfluence γ n x y) ≤ hD.α ^ dist x y / (1 - hD.α)
```

The key observation: for nearest-neighbor specs, `(C^n)_{xy} = 0` unless
paths of length ≤ n connect x and y. So iterates are zero for n < dist(x,y).

Uses: `Matrix.inv` or explicit Neumann series, `Summable` from `row_summable`.

### B2: Covariance bound via iterated DLR (~250 lines)

For local observables f at x, g at y:
```lean
theorem dobrushin_covariance_bound (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) (hμ : IsGibbsMeasure γ μ)
    (f g : SpinConfig I S → ℝ) (hf_local_x : ...) (hg_local_y : ...)
    ... :
    |∫ f·g dμ - (∫f dμ)(∫g dμ)| ≤
      2·‖f‖∞·‖g‖∞ · ((I-C)⁻¹)_{xy}
```

Proof: iterated DLR creates a Neumann-series expansion. Each DLR application
at site z introduces factor bounded by influence at z, and the paths from x to y
have weight bounded by the matrix inverse.

### B3: Exponential decay (~50 lines)

Combining B1 + B2:
```lean
|cov(f, g)| ≤ 2·‖f‖∞·‖g‖∞ · α^{dist(x,y)} / (1-α)
```

Exponential decay with rate `-log α > 0`.

### Total for Phase B: ~500 lines

This is the PRIMARY DELIVERABLE for lgt's mass gap. Everything else
follows from this via Faddeev-Popov.

## Phase C: Cleanup false hypothesis (~50 lines)

Remove `hMargToFull` from `dobrushin_uniqueness`. Replace with:

**Option C1 (finite lattice):** For `[Fintype I]`, uniqueness is automatic:
```lean
theorem finite_lattice_uniqueness [Fintype I] (γ : GibbsSpec I S)
    (μ₁ μ₂ : Measure (SpinConfig I S)) (h₁ h₂ : IsGibbsMeasure γ μᵢ) :
    μ₁ = μ₂ := by
  -- Apply DLR at Λ = Finset.univ.
  -- γ(univ, σ) doesn't depend on σ (Λᶜ = ∅).
  -- So μᵢ = γ(univ, σ₀) for any σ₀.
  -- Hence μ₁ = μ₂.
```

**Option C2 (infinite lattice, conditional):** Keep `hMargToFull` as an axiom
flagged with clear documentation that it's conjectural — "marginals determine
Gibbs measure" holds in some framework we haven't formalized.

## Phase A: Wasserstein (LATER, infinite-lattice uniqueness)

Needed only for infinite-lattice uniqueness (not for lgt's mass gap).

### A1: Wasserstein distance on probability measures (~300 lines)

Define:
```lean
def wassersteinDistance (μ ν : ProbabilityMeasure X) (d : X → X → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ P : coupling μ ν, ∫⁻ p, d p.1 p.2 ∂P
```

For weighted lattice metric on configurations:
```lean
def weightedLatticeDist (a : I → ℝ≥0) (σ τ : SpinConfig I S) : ℝ≥0∞ :=
  ∑' x, a x · 𝟙[σ x ≠ τ x]
```

### A2: Contraction theorem (~200 lines)

```lean
theorem wasserstein_contraction (γ : GibbsSpec I S)
    (hD : DobrushinCondition γ) (a : I → ℝ≥0) (ha_summable : ...) :
    ∀ μ₁ μ₂ : Gibbs γ,
      wassersteinDistance μ₁ μ₂ (weightedLatticeDist a) ≤
      α · wassersteinDistance μ₁ μ₂ (weightedLatticeDist a)
```

### A3: Uniqueness from Wasserstein = 0 (~100 lines)

Wasserstein 0 → measures agree on all cylinder sets → π-λ → full agreement.

### Total for Phase A: ~600 lines

## Dependency graph

```
existing TVCoupling + marginalTvDist_contraction
  ↓
Phase B1: Neumann series bound (immediate, self-contained)
  ↓
Phase B2: Covariance bound via iterated DLR
  ↓
Phase B3: Exponential decay = correlation decay
  ↓
lgt's dobrushin_correlation_bound (bridges: done)
  ↓
lgt's dobrushin_correlation_bound_2d (bridges: remaining)
  ↓
lgt's mass_gap_2d via FP + correlation decay

SEPARATELY:
Phase C1: finite lattice uniqueness (easy, ~50 lines)

LATER:
Phase A1-A3: Wasserstein for infinite-lattice uniqueness
```

## Execution order

1. **Phase C1** (easy, 50 lines): Add `finite_lattice_uniqueness`. This
   covers our lgt application fully.
2. **Phase B1** (200 lines): Neumann series bound.
3. **Phase B2** (250 lines): Iterated DLR covariance bound.
4. **Phase B3** (50 lines): Wire together → exponential decay.
5. Deprecate `hMargToFull`-using `dobrushin_uniqueness`, replace with
   `finite_lattice_uniqueness` for finite case.
6. **Phase A** (future): Infinite-lattice uniqueness if/when needed.

## Scope estimate

| Phase | Content | Lines | Priority |
|-------|---------|-------|----------|
| C1 | Finite lattice uniqueness | 50 | IMMEDIATE |
| B1 | Neumann series bound | 200 | HIGH |
| B2 | Iterated DLR covariance | 250 | HIGH |
| B3 | Exponential decay wiring | 50 | HIGH |
| A1-A3 | Wasserstein uniqueness | 600 | LATER |

Phase B + C1 is ~550 lines to complete the lgt mass gap pipeline.
Phase A adds ~600 for infinite-lattice uniqueness (optional).

## References

- Dobrushin (1968), "Description of random field..."
- Georgii (1988), *Gibbs Measures and Phase Transitions*, §8
- Chatterjee (2026), *Gauge Theory Lecture Notes*, Ch 16
- BUG2.md — the hMargToFull counterexample
