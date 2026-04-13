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
import Mathlib.MeasureTheory.Integral.Bochner.Basic

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

/-! ## Total variation distance properties -/

/-- tvDist is nonneg: every element of the defining set is nonneg. -/
lemma tvDist_set_nonneg {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {c : ℝ} (hc : c ∈ {c : ℝ | ∃ A : Set X, MeasurableSet A ∧
      c = |(μ A).toReal - (ν A).toReal|}) : 0 ≤ c := by
  obtain ⟨A, _, hcA⟩ := hc
  rw [hcA]; exact abs_nonneg _

/-- The defining set of tvDist is nonempty. -/
lemma tvDist_set_nonempty {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (({c : ℝ | ∃ A : Set X, MeasurableSet A ∧
      c = |(μ A).toReal - (ν A).toReal|} : Set ℝ)).Nonempty :=
  ⟨|(μ Set.univ).toReal - (ν Set.univ).toReal|,
    Set.univ, MeasurableSet.univ, rfl⟩

/-- The defining set of tvDist is bounded above by 1. -/
lemma tvDist_set_bddAbove {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    BddAbove {c : ℝ | ∃ A : Set X, MeasurableSet A ∧
      c = |(μ A).toReal - (ν A).toReal|} := by
  refine ⟨1, fun c hc => ?_⟩
  obtain ⟨A, _, hcA⟩ := hc
  rw [hcA]
  have h1 : (μ A).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal one_pos.le (by simp [prob_le_one])
  have h2 : (ν A).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal one_pos.le (by simp [prob_le_one])
  have h3 : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have h4 : 0 ≤ (ν A).toReal := ENNReal.toReal_nonneg
  rw [abs_le]; constructor <;> linarith

/-- tvDist is nonneg. -/
lemma tvDist_nonneg {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ tvDist μ ν :=
  le_csSup_of_le (tvDist_set_bddAbove μ ν)
    (tvDist_set_nonempty μ ν).some_mem
    (tvDist_set_nonneg μ ν (tvDist_set_nonempty μ ν).some_mem)

/-- tvDist is at most 1 for probability measures. -/
lemma tvDist_le_one {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ 1 :=
  csSup_le (tvDist_set_nonempty μ ν) (fun c hc => by
    obtain ⟨A, _, hcA⟩ := hc
    rw [hcA]
    have h1 : (μ A).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal one_pos.le (by simp [prob_le_one])
    have h2 : (ν A).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal one_pos.le (by simp [prob_le_one])
    have h3 : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
    have h4 : 0 ≤ (ν A).toReal := ENNReal.toReal_nonneg
    rw [abs_le]; constructor <;> linarith)

/-- Each measurable set difference is bounded by tvDist. -/
lemma abs_toReal_sub_le_tvDist {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set X) (hA : MeasurableSet A) :
    |(μ A).toReal - (ν A).toReal| ≤ tvDist μ ν :=
  le_csSup (tvDist_set_bddAbove μ ν) ⟨A, hA, rfl⟩

/-- If tvDist μ ν = 0, then μ and ν agree on all measurable sets. -/
lemma eq_of_tvDist_eq_zero {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : tvDist μ ν = 0) : μ = ν := by
  ext A hA
  have habsle := abs_toReal_sub_le_tvDist μ ν A hA
  rw [h] at habsle
  have heq : (μ A).toReal = (ν A).toReal := by
    have h1 := abs_nonneg ((μ A).toReal - (ν A).toReal)
    have h2 : |(μ A).toReal - (ν A).toReal| = 0 := le_antisymm habsle h1
    linarith [abs_eq_zero.mp h2]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) (measure_ne_top ν A)).mp heq

/-- The conditional distribution integrand takes values in [0, 1]. -/
lemma condDist_toReal_nonneg (γ : GibbsSpec d S)
    (x : LatticeSite d) (σ : SpinConfig d S)
    (A : Set (SpinConfig d S)) :
    0 ≤ (γ.condDist {x} σ A).toReal :=
  ENNReal.toReal_nonneg

lemma condDist_toReal_le_one (γ : GibbsSpec d S)
    (x : LatticeSite d) (σ : SpinConfig d S)
    (A : Set (SpinConfig d S)) :
    (γ.condDist {x} σ A).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal one_pos.le (by simp [prob_le_one])

/-- The conditional distribution integrand changes by at most
influenceCoeff(γ, x, y) when the boundary condition is modified
at a single site y.

This is essentially the definition of influenceCoeff: it is the
supremum of tvDist(γ({x}, σ), γ({x}, τ)) over pairs (σ, τ)
differing only at y. Since tvDist bounds the difference on each
measurable set, we get this pointwise bound. -/
lemma condDist_lipschitz_at_site (γ : GibbsSpec d S)
    (x y : LatticeSite d)
    (σ τ : SpinConfig d S) (hdiff : ∀ z, z ≠ y → σ z = τ z)
    (A : Set (SpinConfig d S)) (hA : MeasurableSet A) :
    |(γ.condDist {x} σ A).toReal - (γ.condDist {x} τ A).toReal| ≤
      influenceCoeff γ x y := by
  -- influenceCoeff is the sup of tvDist over pairs differing at y.
  -- tvDist bounds each |μ(A) - ν(A)|.
  -- So we need: |γ({x},σ)(A) - γ({x},τ)(A)| ≤ tvDist(γ({x},σ), γ({x},τ))
  --            ≤ influenceCoeff(γ, x, y)
  -- Step 1: bound by tvDist
  have htvA : |(γ.condDist {x} σ A).toReal - (γ.condDist {x} τ A).toReal| ≤
      tvDist (γ.condDist {x} σ) (γ.condDist {x} τ) :=
    abs_toReal_sub_le_tvDist _ _ A hA
  -- Step 2: bound tvDist by influenceCoeff
  have htv_le : tvDist (γ.condDist {x} σ) (γ.condDist {x} τ) ≤
      influenceCoeff γ x y := by
    apply le_csSup
    · -- bddAbove: influenceCoeff is a sSup of a bounded set
      refine ⟨1, fun c hc => ?_⟩
      obtain ⟨σ', τ', _, hc_eq⟩ := hc
      rw [hc_eq]
      exact tvDist_le_one _ _
    · exact ⟨σ, τ, hdiff, rfl⟩
  linarith

/-- **Dobrushin single-site contraction.**

For each site x, the single-site "marginal disagreement" between
two Gibbs measures is bounded by a weighted sum of the marginal
disagreements at other sites, with weights given by the influence
coefficients.

More precisely, for any measurable set B ⊆ S (a single-site event),
define the cylinder set Cyl(x, B) = {σ | σ(x) ∈ B}. Then:

|(μ₁ Cyl(x,B)) - (μ₂ Cyl(x,B))| ≤ Σ_y C(x,y) · δ(y)

where δ(y) = sup_B |(μ₁ Cyl(y,B)) - (μ₂ Cyl(y,B))| is the
marginal TV distance at site y.

Proof sketch:
- By DLR with Λ = {x}: μᵢ(Cyl(x,B)) = ∫ γ({x},σ)(Cyl(x,B)) dμᵢ(σ)
- The integrand h(σ) = γ({x},σ)(Cyl(x,B)) depends on σ at sites y ≠ x
- For σ, τ agreeing except at y: |h(σ)-h(τ)| ≤ C(x,y)
- Telescoping: |∫h dμ₁ - ∫h dμ₂| ≤ Σ_y C(x,y) · δ(y)

The telescoping step uses: for any [0,1]-valued function g on
SpinConfig that changes by at most c(y) when σ changes at y,
|∫g dμ₁ - ∫g dμ₂| ≤ Σ_y c(y) · δ(y). This is proved by
writing g as a telescoping sum over sites y, replacing σ(y)
one coordinate at a time, and bounding each term.

This is the key analytical step of Dobrushin's theorem. -/
lemma dobrushin_single_site_contraction (γ : GibbsSpec d S)
    (μ₁ μ₂ : Measure (SpinConfig d S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : IsGibbsMeasure γ μ₁) (h₂ : IsGibbsMeasure γ μ₂)
    (x : LatticeSite d)
    (A : Set (SpinConfig d S)) (hA : MeasurableSet A)
    -- δ(y) bounds the single-site marginal disagreement at site y
    (δ : LatticeSite d → ℝ) (hδ_nn : ∀ y, 0 ≤ δ y)
    (hδ_bound : ∀ (y : LatticeSite d) (B : Set (SpinConfig d S)),
      MeasurableSet B → |(μ₁ B).toReal - (μ₂ B).toReal| ≤ δ y) :
    |(μ₁ A).toReal - (μ₂ A).toReal| ≤
      ∑' y, influenceCoeff γ x y * δ y := by
  -- Step 1: Rewrite using DLR
  rw [h₁.dlr {x} A hA, h₂.dlr {x} A hA]
  -- Now need: |∫ γ({x},σ)(A) dμ₁ - ∫ γ({x},σ)(A) dμ₂|
  --         ≤ Σ_y C(x,y) · δ(y)
  -- The integrand h(σ) = γ({x},σ)(A).toReal is [0,1]-valued
  -- and changes by ≤ C(x,y) at each site y (by condDist_lipschitz).
  --
  -- The telescoping argument:
  -- Fix an enumeration y₁, y₂, ... of all sites except x.
  -- Define σⁿ by: σⁿ agrees with τ at sites y₁,...,yₙ and with σ
  -- at all other sites. Then:
  -- h(σ) - h(τ) = Σₙ [h(σⁿ) - h(σⁿ⁻¹)]
  -- |h(σⁿ) - h(σⁿ⁻¹)| ≤ C(x, yₙ) since σⁿ and σⁿ⁻¹ differ at yₙ.
  --
  -- Then: |∫h dμ₁ - ∫h dμ₂|
  --     = |∫∫ [h(σ) - h(τ)] dμ₁(σ) dμ₂(τ)|
  --     ≤ Σₙ ∫∫ |h(σⁿ) - h(σⁿ⁻¹)| dμ₁(σ) dμ₂(τ)
  --     ≤ Σₙ C(x, yₙ) · ...
  -- The precise bound requires marginal-level coupling.
  sorry

/-- **L¹ contraction on marginal disagreements.**

Using the column sum bound and single-site contraction, the total
marginal disagreement Σ_x δ(x) satisfies:

  Σ_x δ(x) ≤ α · Σ_x δ(x)

Proof: Sum the single-site contraction over x, then exchange the
order of summation and apply the column bound Σ_x C(x,y) ≤ α. -/
lemma l1_contraction (γ : GibbsSpec d S)
    (hD : DobrushinCondition γ)
    (δ : LatticeSite d → ℝ) (hδ_nn : ∀ y, 0 ≤ δ y)
    (hδ_sum : Summable δ)
    -- The single-site contraction: δ(x) ≤ Σ_y C(x,y) · δ(y)
    (hcontract : ∀ x, δ x ≤ ∑' y, influenceCoeff γ x y * δ y) :
    ∑' x, δ x ≤ hD.α * ∑' x, δ x := by
  -- Proof sketch:
  -- Σ_x δ(x) ≤ Σ_x Σ_y C(x,y) · δ(y)           (by hcontract)
  --           = Σ_y Σ_x C(x,y) · δ(y)             (Fubini / tsum_comm)
  --           = Σ_y [Σ_x C(x,y)] · δ(y)           (factor out δ(y))
  --           ≤ Σ_y α · δ(y)                       (column_bound)
  --           = α · Σ_y δ(y)                        (factor out α)
  -- Each step requires summability hypotheses (the double sum
  -- Σ_x Σ_y C(x,y)·δ(y) must be absolutely convergent for Fubini).
  sorry

/-- **Key contraction lemma**: Under Dobrushin's condition, the total
variation distance between any two Gibbs measures contracts.

This follows from the single-site contraction and L¹ contraction:
1. Define δ(x) = tvDist(μ₁, μ₂) for all x (crude but sufficient).
2. By `dobrushin_single_site_contraction`: for any A,
   |(μ₁ A) - (μ₂ A)| ≤ Σ_y C(x,y) · δ(y) = tvDist · Σ_y C(x,y).
3. Taking sup over A: tvDist ≤ tvDist · Σ_y C(x,y).

For the column-sum Dobrushin condition, the direct contraction
tvDist ≤ α · tvDist requires the more refined L¹ approach via
marginal disagreements. See `l1_contraction` above. -/
lemma tvDist_contraction (γ : GibbsSpec d S)
    (hD : DobrushinCondition γ)
    (μ₁ μ₂ : Measure (SpinConfig d S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : IsGibbsMeasure γ μ₁) (h₂ : IsGibbsMeasure γ μ₂) :
    tvDist μ₁ μ₂ ≤ hD.α * tvDist μ₁ μ₂ := by
  sorry

/-! ## Main theorems -/

/-- **Dobrushin's uniqueness theorem.**

Under Dobrushin's condition, the Gibbs specification has at most
one Gibbs measure.

Proof outline:
1. By `tvDist_contraction`, tvDist(μ₁, μ₂) ≤ α · tvDist(μ₁, μ₂).
2. Since α < 1 and tvDist ≥ 0, this forces tvDist(μ₁, μ₂) = 0.
3. By `eq_of_tvDist_eq_zero`, μ₁ = μ₂.
-/
theorem dobrushin_uniqueness (γ : GibbsSpec d S)
    (hD : DobrushinCondition γ)
    (μ₁ μ₂ : Measure (SpinConfig d S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : IsGibbsMeasure γ μ₁) (h₂ : IsGibbsMeasure γ μ₂) :
    μ₁ = μ₂ := by
  apply eq_of_tvDist_eq_zero
  -- We have tvDist ≤ α * tvDist with α < 1.
  -- This means (1 - α) * tvDist ≤ 0.
  -- Since 1 - α > 0 and tvDist ≥ 0, we get tvDist = 0.
  have hcontract := tvDist_contraction γ hD μ₁ μ₂ h₁ h₂
  have hα_lt := hD.hα_lt
  have hα_pos := hD.hα_pos
  have hnn := tvDist_nonneg μ₁ μ₂
  nlinarith

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
