# Plan: Proving `dobrushin_single_site_contraction`

*Updated 2026-04-13 — incorporates Gemini 2.5 Pro review*

## The goal

```lean
lemma dobrushin_single_site_contraction :
    |(μ₁ A).toReal - (μ₂ A).toReal| ≤ ∑' y, influenceCoeff γ x y * δ y
```

After DLR rewriting, the goal reduces to:

```
|∫ h(σ) dμ₁ - ∫ h(σ) dμ₂| ≤ Σ_y C(x,y) · δ(y)
```

where `h(σ) = γ({x}, σ)(A).toReal` is [0,1]-valued and has coordinate-wise
Lipschitz bound: for σ, τ differing only at y, `|h(σ) - h(τ)| ≤ C(x,y)`.

## Recommended approach: Optimal coupling

Per Gemini review, the correct approach is:

### The argument

1. Let P be an **optimal coupling** of μ₁, μ₂: a joint measure on
   (SpinConfig d S) × (SpinConfig d S) with marginals μ₁, μ₂ and
   `P(σ ≠ τ) = tvDist(μ₁, μ₂)`.

2. Then: `∫h dμ₁ - ∫h dμ₂ = E_P[h(σ) - h(τ)]`

3. Pointwise telescoping: `|h(σ) - h(τ)| ≤ Σ_y C(x,y) · 1(σ(y) ≠ τ(y))`

4. Take expectation: `|E_P[h(σ)-h(τ)]| ≤ Σ_y C(x,y) · P(σ(y) ≠ τ(y))`

5. Key bound: `P(σ(y) ≠ τ(y)) ≤ P(σ ≠ τ) = tvDist(μ₁, μ₂)`

6. Therefore: `|∫h dμ₁ - ∫h dμ₂| ≤ (Σ_y C(x,y)) · tvDist(μ₁, μ₂)`

With the row sum bound `Σ_y C(x,y) ≤ α`, this gives `tvDist ≤ α · tvDist`.

### Mathlib status (checked 2026-04-13)

**Optimal coupling / TV coupling characterization: NOT IN MATHLIB.**

- Mathlib has `SignedMeasure.totalVariation` (Jordan decomposition) but
  NO coupling characterization of TV distance.
- No `ProbabilityTheory.totalVariation_eq_inf_prob_ne` (Gemini hallucinated this).
- No coupling infrastructure at all in `Mathlib.Probability`.
- RemyDegenne's repos don't have it either.

**What IS available:**
- Product measures: `MeasureTheory.Measure.prod` (Fubini, etc.)
- Signed measures: `MeasureTheory.SignedMeasure`, Jordan decomposition
- Disintegration: `Mathlib.Probability.Kernel.Disintegration`

## Revised plan: avoid optimal coupling

Since optimal coupling isn't in Mathlib, we need an alternative route.

### Alternative: Direct signed measure argument

Instead of coupling, use the signed measure μ₁ - μ₂ directly.

For any bounded measurable h: [0,1]-valued:
```
|∫ h dμ₁ - ∫ h dμ₂| = |∫ h d(μ₁ - μ₂)|
                      ≤ ‖h‖_∞ · |μ₁ - μ₂|(Ω)   (signed measure bound)
                      = tvDist(μ₁, μ₂)
```

This is the TRIVIAL bound. To get the IMPROVED bound ≤ (Σ C(x,y)) · tvDist,
we need to exploit that h has small oscillation in each coordinate.

**Key idea:** Decompose h into a sum of "one-coordinate" functions.

For h with coordinate Lipschitz constants c(y), define:
```
h(σ) = h(σ₀) + Σ_y [h(σ with σ(y) at y) - h(σ with σ₀(y) at y)]
```
where σ₀ is a fixed reference configuration. Each term in the sum depends
on σ only through σ(y) and has oscillation ≤ c(y).

Then:
```
|∫ h dμ₁ - ∫ h dμ₂| = |Σ_y ∫ [h_y(σ(y)) - const_y] d(μ₁-μ₂)|
                      ≤ Σ_y c(y) · tvDist(π_y(μ₁), π_y(μ₂))
                      ≤ Σ_y c(y) · tvDist(μ₁, μ₂)
```

**Problem:** The decomposition h = const + Σ one-coord-functions is only
valid if the telescoping converges and the cross-terms vanish. The cross-terms
DON'T vanish in general — this decomposition is wrong.

### Alternative: Build the coupling lemma ourselves

The coupling characterization of TV distance is:

```lean
/-- For probability measures μ, ν on a measurable space X,
    tvDist(μ, ν) = inf over couplings P of P(fst ≠ snd). -/
theorem tvDist_eq_inf_coupling ...
```

This is a fundamental result that should exist. The proof:
- **Upper bound** (easy): construct a specific coupling achieving P(≠) = tvDist.
  Use the "maximal coupling": on the overlap region, couple identically;
  on the non-overlap, couple independently from the residual measures.
- **Lower bound** (easy): for any coupling P and measurable A,
  μ(A) - ν(A) = P(σ ∈ A) - P(τ ∈ A) = P(σ ∈ A, τ ∉ A) - P(σ ∉ A, τ ∈ A)
  ≤ P(σ ≠ τ). Take sup over A.

For the formalization, we only need the UPPER bound:
```lean
/-- There exists a coupling P of μ₁, μ₂ such that
    P(σ(y) ≠ τ(y)) ≤ tvDist(μ₁, μ₂) for all y. -/
```

Actually, we don't even need optimal coupling. We need:

**For any two probability measures μ, ν and any [0,1]-valued measurable h:**
```
|∫ h dμ - ∫ h dν| ≤ tvDist(μ, ν)
```

This is ALREADY PROVED in our codebase as `abs_toReal_sub_le_tvDist`
(for indicator functions) and extends to [0,1]-valued functions by
approximation with simple functions.

The improvement to `≤ (Σ c(y)) · tvDist` requires more.

### SIMPLEST VIABLE APPROACH

**Skip the general Lipschitz-TV lemma. Prove uniqueness directly
using the constant-δ version.**

```lean
/-- For any A and any x, using DLR:
    |(μ₁ A) - (μ₂ A)| ≤ (Σ_y C(x,y)) · tvDist(μ₁, μ₂). -/
lemma tvDist_contraction_at_site ...
```

**Proof:** By DLR, |(μ₁ A) - (μ₂ A)| = |∫ h d(μ₁-μ₂)| where
h(σ) = γ({x},σ)(A).toReal.

Use the fact that h doesn't depend on σ(x) and apply DLR AGAIN
at another site y₁, pushing the dependence further.

After applying DLR at sites y₁,...,yₙ, the effective function depends
only on sites outside {x, y₁,...,yₙ} and the accumulated bound is
Σᵢ C(x,yᵢ) · tvDist.

For nearest-neighbor models with C having finite support, after d(x)
steps (where d(x) = number of neighbors), ALL dependence is removed
and the bound is (Σ_y C(x,y)) · tvDist ≤ α · tvDist.

**Why this works for finite-support C:** If C(x,y) = 0 for all but
finitely many y, then h depends on only finitely many coordinates.
The DLR cascade terminates in finitely many steps.

## Phase plan (revised)

### Phase 0: Prove for finite-support influence (IMMEDIATE)

Prove `tvDist_contraction` under the ADDITIONAL hypothesis that
`influenceCoeff γ x y` has finite support in y for each x.

This covers all nearest-neighbor models and is sufficient for lgt.

```lean
/-- When influence has finite support, TV contraction holds. -/
lemma tvDist_contraction_finsupp (γ : GibbsSpec d S)
    (hD : DobrushinCondition γ)
    (hfinsupp : ∀ x, (Function.support (influenceCoeff γ x ·)).Finite)
    ... : tvDist μ₁ μ₂ ≤ hD.α * tvDist μ₁ μ₂
```

**Proof strategy:**
1. For h(σ) = γ({x},σ)(A).toReal, h depends on finitely many coords
2. Apply DLR iteratively at each coord in the support
3. Each step contributes C(x,y) · tvDist to the bound
4. Total: (Σ_y C(x,y)) · tvDist ≤ α · tvDist

**Infrastructure needed:**
- `Function.update` for changing one coordinate of SpinConfig
- Finite induction on the support set
- `abs_toReal_sub_le_tvDist` (already proved)
- DLR equation (already in IsGibbsMeasure)

**Estimated:** 200-300 lines

### Phase 1: Build optimal coupling (LATER)

For the general (infinite-support) case, build:
- `tvDist_eq_inf_coupling`: coupling characterization of TV
- Maximal coupling construction
- `integral_lipschitz_le_rowsum_tvDist`: general Lipschitz-TV lemma

**Estimated:** 400-500 lines, can be a standalone module

### Phase 2: Generalize (OPTIONAL)

Prove `dobrushin_single_site_contraction` with general δ(y) using
site-wise optimal couplings (not just the global coupling).

## Dependency graph (revised)

```
DLR + Function.update + finite induction
           │
           v
tvDist_contraction_finsupp  [Phase 0, immediate target]
           │
           v
tvDist_contraction  [specialize to finsupp case]
           │
           v
dobrushin_uniqueness  [already proved from tvDist_contraction]
```

Later:
```
Optimal coupling construction  [Phase 1]
           │
           v
integral_lipschitz_le_rowsum_tvDist  [general case]
           │
           v
tvDist_contraction  [remove finsupp hypothesis]
```

## Key insight

**For all current applications (lgt, pphi2, nearest-neighbor models),
the influence matrix has finite support per row.** So Phase 0 is
sufficient. The infinite-support case is a generalization for future
use but not blocking any current goals.
