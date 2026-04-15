# Critical bug in Dobrushin influenceCoeff

*Discovered 2026-04-15 via Gemini review + formalization attempt*

## The bug

Current definition in `Uniqueness.lean` line 71:
```lean
def influenceCoeff (γ : GibbsSpec I S) (x y : I) : ℝ :=
  sSup {c : ℝ | ∃ (σ τ : SpinConfig I S),
    (∀ z, z ≠ y → σ z = τ z) ∧
    c = tvDist (γ.condDist {x} σ) (γ.condDist {x} τ)}
```

`tvDist` is on `Measure (SpinConfig I S)` — the **full configuration space**.

## The problem

Combined with `GibbsSpec.proper`:
```lean
proper : condDist Λ σ {τ | ∀ x, x ∉ Λ → τ x = σ x} = 1
```

For Λ = {x} and σ, τ differing at y ≠ x:
- condDist {x} σ supports configs with value σ(y) at y
- condDist {x} τ supports configs with value τ(y) at y
- These supports are **disjoint** (if σ(y) ≠ τ(y))
- So tvDist(condDist {x} σ, condDist {x} τ) = 1

Therefore `influenceCoeff γ x y = 1` whenever the spin space has ≥ 2 points, regardless of x, y, γ.

This **breaks the Dobrushin condition**: column sums are ≥ (number of sites), never < 1.

## The fix

Dobrushin's original definition (Dobrushin 1968, Georgii 1988, Chatterjee 2026 Ch 16) uses the **marginal TV distance at site x**:

```
C(x, y) = sup_{σ, τ differ at y}
    d_TV(π_x · γ({x}, σ), π_x · γ({x}, τ))
```

where `π_x : Measure (SpinConfig I S) → Measure S` is `μ ↦ μ.map (fun ω => ω x)`.

With this, changing σ at y (y ≠ x) does NOT force the marginals to be singular, because the marginal only cares about the x-coordinate.

## Proposed fix

Redefine `influenceCoeff`:
```lean
def marginalAtSite (μ : Measure (SpinConfig I S)) (x : I) : Measure S :=
  μ.map (fun σ => σ x)

def influenceCoeff (γ : GibbsSpec I S) (x y : I) : ℝ :=
  sSup {c : ℝ | ∃ (σ τ : SpinConfig I S),
    (∀ z, z ≠ y → σ z = τ z) ∧
    c = tvDist (marginalAtSite (γ.condDist {x} σ) x)
               (marginalAtSite (γ.condDist {x} τ) x)}
```

## Impact

All proofs that use `influenceCoeff`:
- `condDist_lipschitz_at_site`
- `dobrushin_single_site_contraction`
- `condDist_integral_bound`
- `tvDist_contraction`
- `dobrushin_uniqueness`

Need review. Most arguments should carry through — the contraction only requires that influenceCoeff measures some form of "how much the conditional changes". But the specific measure-theoretic details will change.

## Scope

This is a **substantial refactor** across Specification.lean, Uniqueness.lean, and StrongCoupling.lean. The consequences for YMSpec.lean and YMDobrushin.lean in lgt are favorable: the influenceCoeff becomes meaningful for YM once fixed.

## Status

Documented. Fix in progress.
