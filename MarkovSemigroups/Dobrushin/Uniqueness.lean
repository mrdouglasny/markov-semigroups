/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dobrushin's Uniqueness Condition

## Overview

Dobrushin's uniqueness condition is a criterion for a Gibbs
specification to have a unique Gibbs measure with exponentially
decaying correlations. It bounds the influence of boundary
conditions at each site on the conditional distribution at
another site, via a matrix of total-variation influence coefficients.

If the supremum over columns of the influence matrix is strictly
less than 1, the specification has a unique Gibbs measure, and
correlations between spatially separated observables decay
exponentially in distance.

## Main definitions

- `influenceCoeff` — C(x,y): TV distance of conditional at x when
  boundary at y changes (sup over all boundary conditions)
- `DobrushinCondition` — sup_y Σ_x C(x,y) < 1
- `dobrushin_uniqueness` — unique Gibbs measure under Dobrushin condition
- `dobrushin_correlation_decay` — exponential correlation decay

## References

- Dobrushin, "The description of a random field by means of conditional
  probabilities and conditions of its regularity," Theor. Prob. Appl. 13
  (1968), 197--224
- Chatterjee, *Gauge Theory Lecture Notes* (2026), Ch 16, Thm 16.2.1
- Georgii, *Gibbs Measures and Phase Transitions*, de Gruyter, 2011, Ch 8
- Simon, *The Statistical Mechanics of Lattice Gases*, Princeton, 1993, Ch III
-/

import MarkovSemigroups.Dobrushin.Specification
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open MeasureTheory Finset

noncomputable section

variable {d : ℕ} {S : Type*} [MeasurableSpace S]

/-! ## Influence coefficients -/

/-- Total variation distance between two probability measures:
d_TV(μ, ν) = sup_A |μ(A) - ν(A)|.
TODO: replace with Mathlib's TV distance once available. -/
def tvDist {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : ℝ :=
  sSup {c : ℝ | ∃ A : Set X, MeasurableSet A ∧
    c = |(μ A).toReal - (ν A).toReal|}

/-- The influence coefficient C(x, y) for a Gibbs specification γ.

This measures how much the conditional distribution at site x can
change (in total variation) when the boundary condition at site y
is modified, with all other boundary sites held fixed.

C(x, y) = sup over all boundary conditions σ, τ that differ only
at y, of d_TV(γ({x}, σ), γ({x}, τ)). -/
def influenceCoeff (γ : GibbsSpec d S) (x y : LatticeSite d) : ℝ :=
  sSup {c : ℝ | ∃ (σ τ : SpinConfig d S),
    (∀ z, z ≠ y → σ z = τ z) ∧
    c = tvDist (γ.condDist {x} σ) (γ.condDist {x} τ)}

/-- Dobrushin's condition: the influence matrix has column sums < 1.

Formally: there exists α < 1 such that for all y,
  Σ_x C(x, y) ≤ α.

In practice we work with a finite box and take limits, but the
condition is stated for the full lattice specification. -/
structure DobrushinCondition (γ : GibbsSpec d S) where
  /-- The contraction constant α < 1. -/
  α : ℝ
  hα_pos : 0 ≤ α
  hα_lt : α < 1
  /-- The influence coefficients are summable in x for each y. -/
  summable : ∀ (y : LatticeSite d),
    Summable (fun x => influenceCoeff γ x y)
  /-- Column sum bound: for all y, Σ_x C(x,y) ≤ α < 1. -/
  column_bound : ∀ (y : LatticeSite d),
    ∑' x, influenceCoeff γ x y ≤ α

/-! ## Main theorems -/

/-- **Dobrushin's uniqueness theorem.**

Under Dobrushin's condition, the Gibbs specification has at most
one Gibbs measure.

Proof strategy (Chatterjee Ch 16, Thm 16.2.1):
1. Take two Gibbs measures μ₁, μ₂.
2. For any local observable f depending on site x,
   |E_{μ₁}[f] - E_{μ₂}[f]| ≤ C · Σ_y influence(x,y) · |E_{μ₁}[g_y] - E_{μ₂}[g_y]|
   by the DLR equation + TV bound on single-site conditionals.
3. Iterate: the operator norm of the influence matrix is ≤ α < 1,
   so the fixed point is unique.
-/
theorem dobrushin_uniqueness (γ : GibbsSpec d S)
    (hD : DobrushinCondition γ)
    (μ₁ μ₂ : Measure (SpinConfig d S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : IsGibbsMeasure γ μ₁) (h₂ : IsGibbsMeasure γ μ₂) :
    μ₁ = μ₂ := by
  sorry

/-- **Dobrushin's correlation decay.**

Under Dobrushin's condition, correlations between single-site
observables decay exponentially. The decay constant involves the
influence propagation matrix (I - C)⁻¹, not simply α^dist.

For single-site observables f at x, g at y:
|cov_μ(f, g)| ≤ 2 · ‖f‖∞ · ‖g‖∞ · ((I-C)⁻¹)_{xy}

Since ‖C‖₁ ≤ α < 1, the Neumann series gives
  ((I-C)⁻¹)_{xy} = Σ_{n≥0} (C^n)_{xy}
which decays exponentially in dist(x,y) for short-range C.

For nearest-neighbor interactions with C(x,y) ≤ β for neighbors,
this gives decay like (const·β)^{dist(x,y)}, which is sharper
than the naive α^{dist} = (2dβ)^{dist} bound.
-/
theorem dobrushin_correlation_decay (γ : GibbsSpec d S)
    (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig d S))
    [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (f g : SpinConfig d S → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (Bf Bg : ℝ) (hBf : ∀ σ, |f σ| ≤ Bf) (hBg : ∀ σ, |g σ| ≤ Bg)
    (x y : LatticeSite d)
    (hf_local : ∀ σ τ, σ x = τ x → f σ = f τ)
    (hg_local : ∀ σ τ, σ y = τ y → g σ = g τ) :
    -- The bound involves the (x,y) entry of (I-C)⁻¹ = Σ_n C^n,
    -- which we express via the Neumann series.
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)| ≤
      2 * Bf * Bg * hD.α ^ latticeDist x y / (1 - hD.α) := by
  sorry
  -- Note: the bound α^dist/(1-α) is a crude but correct upper bound
  -- on ((I-C)⁻¹)_{xy} via ‖C^n‖₁ ≤ α^n and summing the geometric
  -- series. For nearest-neighbor models, sharper bounds exist using
  -- the local interaction strength rather than the global column sum.

/-- **Existence under Dobrushin's condition.**

If the single-site spin space is compact metrizable and the
specification is Feller (continuous in the boundary condition),
then Dobrushin's condition implies existence of at least one
(hence exactly one) Gibbs measure.

The Feller property ensures that the Dobrushin iteration
Tμ = ∫ γ(Λ, σ) dμ(σ) maps tight measures to tight measures,
and a fixed-point argument (Schauder or Banach contraction)
yields existence.
-/
theorem dobrushin_existence [TopologicalSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (γ : GibbsSpec d S)
    (hD : DobrushinCondition γ)
    -- Feller property: the conditional distribution is continuous
    -- in the boundary condition (weak topology on measures).
    (hFeller : ∀ (Λ : Finset (LatticeSite d))
      (A : Set (SpinConfig d S)) (hA : MeasurableSet A),
      Continuous (fun σ : SpinConfig d S => (γ.condDist Λ σ A).toReal)) :
    ∃ (μ : Measure (SpinConfig d S)) (_ : IsProbabilityMeasure μ),
      IsGibbsMeasure γ μ := by
  sorry

end
