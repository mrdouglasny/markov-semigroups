# Plan: Proving `dobrushin_single_site_contraction`

*2026-04-13*

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

This is the **core analytical content** of Dobrushin's theorem.

## The abstract lemma needed

The proof factors through a general result about functions on product spaces:

**Lipschitz-TV lemma.** Let Ω = Π_i S_i be a product space with probability
measures μ, ν. Let h: Ω → [0,1] satisfy the coordinate-wise Lipschitz condition:

  for σ, τ differing only at site y: |h(σ) - h(τ)| ≤ c(y)

where Σ_y c(y) < ∞. Then:

  |∫ h dμ - ∫ h dν| ≤ Σ_y c(y) · tvDist(π_y(μ), π_y(ν))

where π_y is the projection to site y.

Our application: c(y) = C(x,y) and Σ c(y) ≤ α < 1 by row sum bound.

## Three approaches

### Approach A: Product coupling (RECOMMENDED)

**Idea:** Use the product measure μ₁ ⊗ μ₂ and pointwise telescoping.

**Steps:**
1. Write `∫h dμ₁ - ∫h dμ₂ = ∫∫ [h(σ) - h(τ)] dμ₂(τ) dμ₁(σ)` (Fubini)
2. Fix (σ, τ). Enumerate sites y₁, y₂, ... Define hybrid configs:
   `ωⁿ(yₖ) = σ(yₖ) if k ≤ n, τ(yₖ) if k > n`
3. Telescoping: `h(σ) - h(τ) = Σₙ [h(ωⁿ) - h(ωⁿ⁻¹)]`
4. Each term: `|h(ωⁿ) - h(ωⁿ⁻¹)| ≤ c(yₙ) · 1(σ(yₙ) ≠ τ(yₙ))`
5. Take expectation: `|E[h(σ)-h(τ)]| ≤ Σ_y c(y) · P_{μ₁⊗μ₂}(σ(y)≠τ(y))`
6. For independent draws: `P(σ(y)≠τ(y)) ≤ 1`, giving `≤ Σ c(y) ≤ α`

But this gives ≤ α, not ≤ Σ c(y)·δ(y). For the δ(y) version:

6'. We need `P(σ(y)≠τ(y)) ≤ f(tvDist_marginal_y)`.
   Under product coupling: `P(σ(y)≠τ(y)) = 1 - Σ_s π_y(μ₁)(s)·π_y(μ₂)(s)`
   
   This is ≤ 1 but not directly ≤ tvDist_y. However, since hδ_bound gives
   δ(y) ≥ tvDist(μ₁,μ₂) ≥ tvDist_y for all y, we can use the CRUDE bound:
   
   `Σ c(y) · P(disagree at y) ≤ Σ c(y) · 1 ≤ α ≤ α · (something involving δ)`

**Problem:** The product coupling gives P(disagree) ≤ 1, not ≤ tvDist_y.
With constant δ(y) = tvDist, the bound becomes Σ c(y) · tvDist ≤ α · tvDist. ✓

**Conclusion:** This approach works if we specialize δ(y) = tvDist(μ₁,μ₂) (constant).
The current lemma statement with general δ may be too strong for this approach.

**Infrastructure needed:**
- Fubini for product measures on SpinConfig (Mathlib has this)
- Pointwise telescoping as infinite series (needs convergence of Σ c(y))
- Product topology on SpinConfig (Mathlib: `Pi.instTopologicalSpace`)

**Estimated effort:** 300-500 lines

### Approach B: Conditional expectation iteration (DLR cascade)

**Idea:** Apply DLR one site at a time to "wash out" dependence.

**Steps:**
1. Start: `∫h dμ₁ - ∫h dμ₂` where h depends on all sites ≠ x
2. Apply DLR at {y₁}: `∫h dμᵢ = ∫ E_{γ({y₁},·)}[h] dμᵢ`
3. The function `g₁(σ) = E_{γ({y₁},σ)}[h]` no longer depends on σ(y₁)
   Error: `|∫h dμᵢ - ∫g₁ dμᵢ| = 0` (exact by DLR, no error)
   But `g₁` still depends on other sites. The key: g₁ has same Lipschitz
   constants as h except `osc_{y₁}(g₁) = 0`.
4. The difference `∫h dμ₁ - ∫h dμ₂ = ∫g₁ dμ₁ - ∫g₁ dμ₂`
   Now g₁ is independent of y₁. Repeat at y₂, y₃, ...
5. After n steps: `gₙ` is independent of y₁,...,yₙ. As n→∞, gₙ → const.
   The constant is the same for both μ₁ and μ₂ (by DLR), so the difference → 0.

**Problem:** This shows the difference is 0, but doesn't give the quantitative
bound involving c(y)·δ(y). Also, the convergence gₙ → const requires
that removing coordinates makes the function converge — this is a tail
sigma-algebra argument (Kolmogorov 0-1 law flavor).

**Infrastructure needed:**
- Iterated conditional expectation
- Convergence of conditional expectations (martingale convergence?)
- Disintegration of measures on product spaces

**Estimated effort:** 500+ lines, heavy Mathlib dependency

### Approach C: Finite-volume approximation

**Idea:** Prove the bound for finite lattice (Λ_n = [-n,n]^d), then take n → ∞.

**Steps:**
1. On finite lattice: telescoping is a FINITE sum — straightforward
2. The bound holds with finite sums: `≤ Σ_{y∈Λ_n} c(y) · δ(y)`
3. Pass to limit: `Σ_{y∈Λ_n} → Σ'_y` as n → ∞

**Problem:** The measures μ₁, μ₂ live on the FULL lattice. Restricting to
a finite box requires marginalizing, and the DLR equation relates to the
full specification. Need to show: the finite-volume bound approximates
the infinite-volume one.

**Infrastructure needed:**
- Finite product measure theory (easier than infinite)
- Marginals and their convergence
- Monotone convergence for the bound

**Estimated effort:** 400-600 lines

## Recommended path

### Phase 1: Simplify the lemma statement (immediate)

Refactor `dobrushin_single_site_contraction` to use δ(y) = tvDist(μ₁,μ₂)
(constant for all y). This is sufficient for `tvDist_contraction` and
`dobrushin_uniqueness`, and is much easier to prove.

```lean
lemma tvDist_contraction_step (γ : GibbsSpec d S)
    (μ₁ μ₂ : Measure (SpinConfig d S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : IsGibbsMeasure γ μ₁) (h₂ : IsGibbsMeasure γ μ₂)
    (x : LatticeSite d)
    (A : Set (SpinConfig d S)) (hA : MeasurableSet A) :
    |(μ₁ A).toReal - (μ₂ A).toReal| ≤
      (∑' y, influenceCoeff γ x y) * tvDist μ₁ μ₂
```

This says: each measurable set difference is bounded by (row sum at x) · tvDist.
Taking sup over A and then inf over x:
  tvDist ≤ (inf_x Σ_y C(x,y)) · tvDist ≤ α · tvDist

### Phase 2: Prove the Lipschitz-TV lemma (core infrastructure)

The key abstract result, independent of Gibbs measures:

```lean
/-- For h: SpinConfig → [0,1] with coordinate Lipschitz constants c(y),
    |∫ h dμ₁ - ∫ h dμ₂| ≤ (Σ_y c(y)) · tvDist(μ₁, μ₂). -/
lemma integral_diff_le_lipschitz_tv ...
```

**Proof via product coupling + telescoping:**
1. `∫h dμ₁ - ∫h dμ₂ = ∫∫ [h(σ)-h(τ)] dμ₂ dμ₁`
2. Pointwise: `|h(σ)-h(τ)| ≤ Σ_y c(y)` (finite or convergent telescoping)
3. Therefore: `|∫∫ [h(σ)-h(τ)] dμ₂ dμ₁| ≤ Σ_y c(y)`

Wait — this gives ≤ Σ c(y), not ≤ (Σ c(y)) · tvDist. The tvDist factor
comes from the fact that h doesn't vary in ALL directions, only in
the directions where μ₁ and μ₂ differ.

Actually, the simpler bound ≤ Σ c(y) is ALREADY useful if Σ c(y) ≤ α < 1,
because tvDist ≤ 1. So:
  tvDist ≤ Σ c(y) ≤ α < 1
  
But this just says tvDist < 1, which is trivial.

We need the MULTIPLICATIVE contraction tvDist ≤ α · tvDist.

For that, the coupling approach gives:
  |∫h dμ₁ - ∫h dμ₂| ≤ Σ_y c(y) · P_{coupling}(σ(y) ≠ τ(y))

With OPTIMAL marginal coupling at each y: P ≤ tvDist_y ≤ tvDist.
So: ≤ Σ c(y) · tvDist = (row sum) · tvDist ≤ α · tvDist ✓

The question is whether we need the GLOBAL optimal coupling or just
MARGINAL optimal couplings (one per site).

### Phase 3: Infrastructure lemmas

#### 3a. Telescoping on product spaces
```lean
/-- Pointwise telescoping: for configs σ, τ and h with coord Lipschitz c(y),
    |h(σ) - h(τ)| ≤ Σ_y c(y) · 1(σ(y) ≠ τ(y)). -/
lemma pointwise_lipschitz_telescope ...
```

For FINITE support of c (only finitely many y with c(y) > 0), this is
a finite sum — completely standard. For the general case, need convergence
of the telescoping series.

For nearest-neighbor models, c has FINITE support (only 2d neighbors).
So the finite case suffices for all applications.

#### 3b. Marginal coupling lemma
```lean
/-- For any coupling (σ,τ) of μ₁, μ₂:
    P(σ(y) ≠ τ(y)) ≥ tvDist(π_y(μ₁), π_y(μ₂)).
    The optimal coupling achieves equality. -/
```

This is the coupling characterization of TV distance. It might be in Mathlib
for countable spaces. For general measurable spaces, it requires the
existence of optimal transport couplings.

#### 3c. Product Fubini
```lean
/-- ∫ h dμ₁ - ∫ h dμ₂ = ∫∫ [h(σ) - h(τ)] dμ₂(τ) dμ₁(σ) -/
```

Standard Fubini — should be in Mathlib via `integral_prod`.

## Dependency graph

```
pointwise_lipschitz_telescope  [Phase 3a]
    │
    ├──→ integral_diff_le_row_sum  [Phase 2]
    │         │
    │         └──→ tvDist_contraction_step  [Phase 1]
    │                   │
    │                   └──→ tvDist_contraction  [exists]
    │                             │
    │                             └──→ dobrushin_uniqueness  [proved]
    │
    └──→ integral_diff_le_lipschitz_tv  [Phase 2, refined]
              │
              └──→ dobrushin_single_site_contraction  [general form]
```

## Recommended order

1. **Now:** Refactor to add `tvDist_contraction_step` with the simpler
   constant-δ statement. Prove `tvDist_contraction` from it + row_bound.

2. **Next session:** Prove `pointwise_lipschitz_telescope` for finite
   support (covers all nearest-neighbor models). This is pure combinatorics
   on `Function.update` and `Finset.sum`.

3. **Then:** Prove `integral_diff_le_row_sum` using product Fubini +
   the pointwise telescope. This completes `tvDist_contraction_step`.

4. **Later:** Generalize to infinite support via convergence arguments.

## Estimated total: 400-600 lines across Phases 1-3
