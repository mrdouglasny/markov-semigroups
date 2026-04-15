# Second bug: `hMargToFull` is mathematically false

*Discovered 2026-04-15 via Gemini 3 Pro review*

## The claim under `hMargToFull`

```lean
(hMargToFull : ∀ x, tvDist μ₁ μ₂ ≤ marginalTvDist μ₁ μ₂ x)
```

For two Gibbs measures μ₁, μ₂, the full TV distance is bounded above
by the marginal TV distance at any single site.

## Counterexample (Gemini 3 Pro)

**2D Ising just below the critical temperature Tc**:
- Plus-state μ⁺ (extremal Gibbs measure, spontaneous magnetization +m)
- Minus-state μ⁻ (extremal Gibbs measure, magnetization -m)

Properties:
- μ⁺ and μ⁻ are **mutually singular** (supported on disjoint events in the
  tail σ-algebra via the mean spontaneous magnetization)
- Therefore `tvDist(μ⁺, μ⁻) = 1`
- Single-site marginals: Dirac-like at +m and -m, with
  `marginalTvDist(μ⁺, μ⁻, x) = 2m`
- As T → Tc, m → 0, so `marginalTvDist → 0` while `tvDist = 1`

This gives `1 = tvDist ≤ 2m → 0`, which is **false** for T near Tc.

## Consequence

`hMargToFull` is not a dischargeable hypothesis — it's essentially
equivalent to the conclusion `tvDist = 0`. Users will never be able
to supply it except by already knowing uniqueness.

## The true uniqueness argument

The correct Dobrushin argument uses either:

### Option A: Wasserstein distance (Dobrushin 1968, Chatterjee Ch 16)

Use `W(μ₁, μ₂)` with a macroscopic weighted metric
`d(σ, τ) = Σ_x a_x 𝟙[σ_x ≠ τ_x]`. Prove `W ≤ α · W`, conclude `W = 0`
since W separates points. This requires Wasserstein machinery.

### Option B: Local observables + π-λ (Georgii 1988 Thm 8.2)

For any local observable f (depending on finite Δ), prove
`∫f dμ₁ = ∫f dμ₂` via DLR equations + Neumann series
`Σ_{n≥0} C^n < ∞`. Then π-λ gives full measures agree.

## Status

The current formalization has:
- ✅ Correct `influenceCoeff` definition (marginal TV)
- ✅ Correct `marginalTvDist_contraction`: marginalTvDist ≤ α · tvDist
- ❌ Invalid `hMargToFull` bridge

To obtain actual `dobrushin_uniqueness`, need Option A or B.

## What we CAN conclude

- `marginalTvDist → 0` under iteration (valid physics content)
- For FINITE lattice with explicit construction: uniqueness via finite
  product sigma-algebra (but we need Option B for infinite-volume)
- The physical content (exponential decay of spin-spin correlations)
  is preserved even without full uniqueness

## Recommendation

1. Mark `hMargToFull` as conjectural / unprovable in general
2. State `dobrushin_uniqueness` with the understanding it's
   "conditional on a marginal-to-full bridge that requires Wasserstein or π-λ"
3. For the lgt application: the marginal contraction alone gives
   correlation decay, which is the physical mass gap content
