/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dobrushin Coupling Existence (Classical Axiom)

The Dobrushin iterated coupling theorem: for probability measures μ₁, μ₂
on a product space SpinConfig I S that both satisfy DLR at sites in T,
there exists a joint coupling P with per-site contraction.

This is a classical result from Dobrushin (1968), Lemma 2; see also
Georgii (1988), Proposition 8.7. The construction proceeds by:
1. Define a "coupled specification" γ̄ on (SpinConfig × SpinConfig)
   whose site-z component is the maximal coupling of γ({z}, σ) and
   γ({z}, τ) for each boundary pair (σ, τ).
2. The maximal coupling achieves P{σ_z ≠ τ_z | σ_{-z}, τ_{-z}} =
   tvNorm(marg_z(γ({z},σ)), marg_z(γ({z},τ))) ≤ Σ C(z,w)·1_{σ_w≠τ_w}.
3. A DLR measure P for γ̄ with marginals μ₁, μ₂ exists by Prokhorov's
   theorem (weak compactness of probability measures on a Polish space).
4. Integrating the pointwise inequality (2) against P yields the
   self-consistency contraction.

The full formalization requires:
- Parametric measurability of the maximal coupling kernel (solved for
  [Countable S] by the canonical formula P = (μ⊓ν).map(diag) + ...).
- Existence of DLR measures for the coupled specification on general
  (possibly uncountable) product spaces (Prokhorov's theorem).
- Neither is currently available in Mathlib v4.29.0.

We axiomatize this classical result here, replacing the `sorry` that
was previously in `CondTVBridge.lean`. The axiom is used by:
- `condSingleSiteMeasure_marginalTvDist_le_neumannSeriesCoeff`
- `condFiniteSupportMeasure_marginalTvDist_le_neumannSeriesSum`
and their `_nocount` variants.

References:
- Dobrushin (1968), "Description of a random field by means of
  conditional probabilities and conditions of its regularity", Lemma 2.
- Georgii (1988), *Gibbs Measures and Phase Transitions*, Prop 8.7.
-/

import MarkovSemigroups.Coupling.TVCoupling
import MarkovSemigroups.Dobrushin.Specification
import MarkovSemigroups.Dobrushin.Uniqueness

open MeasureTheory

noncomputable section

/-- **Dobrushin iterated coupling existence (axiom).**

For probability measures μ₁, μ₂ on SpinConfig I S that both satisfy
the DLR equation at all singleton sites {z} for z ∈ T, there exists
a joint coupling P of μ₁ and μ₂ on (SpinConfig I S) × (SpinConfig I S)
such that for every z ∈ T, the coupling-disagreement probability at z
satisfies the contraction inequality:

  P{σ_z ≠ τ_z} ≤ Σ_w C(z,w) · P{σ_w ≠ τ_w}

where C(z,w) = influenceCoeff γ z w.

This is the classical Dobrushin (1968) result. The construction uses
an iterated maximal coupling at each site. The full Lean proof requires
parametric measurability of the maximal-coupling kernel in the Giry
σ-algebra, which for countable S follows from the canonical formula
`P = (μ ⊓ ν).map(diag) + c⁻¹ • (μ-μ⊓ν).prod(ν-μ⊓ν)`
and for general S requires Prokhorov compactness. -/
axiom dobrushin_coupling_axiom
    {I S : Type*} [DecidableEq I] [MeasurableSpace S]
    [MeasurableSingletonClass S] [MeasurableEq (SpinConfig I S)]
    (γ : GibbsSpec I S)
    (μ₁ μ₂ : Measure (SpinConfig I S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (T : Set I)
    (hμ₁ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)),
      MeasurableSet A →
      (μ₁ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₁)
    (hμ₂ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)),
      MeasurableSet A →
      (μ₂ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₂)
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    ∃ (P : Measure (SpinConfig I S × SpinConfig I S))
      (_ : IsCoupling P μ₁ μ₂),
      ∀ z ∈ T,
        (P {p : SpinConfig I S × SpinConfig I S | p.1 z ≠ p.2 z}).toReal ≤
          ∑' w, influenceCoeff γ z w *
            (P {p : SpinConfig I S × SpinConfig I S | p.1 w ≠ p.2 w}).toReal

end
