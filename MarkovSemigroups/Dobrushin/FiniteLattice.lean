/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniqueness of Gibbs Measures on Finite Lattices

On a finite lattice (`[Fintype I]`), a Gibbs measure for a specification
is UNIQUE — no Dobrushin condition needed. This is because DLR applied
to Λ = Finset.univ forces μ = γ(univ, σ) for any σ.

For Λ = Finset.univ, the complement Λᶜ = ∅, so by `consistent`, the
conditional `γ(univ, σ)` does not depend on σ. Call this single measure
ν. Then DLR gives:
  μ(A) = ∫ γ(univ, σ)(A) dμ(σ) = ∫ ν(A) dμ(σ) = ν(A) · μ(univ) = ν(A).

So every Gibbs measure equals ν; hence at most one Gibbs measure exists.

This covers the main use case: lattice gauge theory on finite tori
(`LatticeLink d N` with `[Fintype]`). Dobrushin's condition is only
needed for infinite lattices or for correlation decay bounds.

## References

- Georgii (1988), §1 (uniqueness on finite Λ is immediate from DLR)
- Chatterjee (2026), §15.2 (finite-lattice Gibbs measures)
-/

import MarkovSemigroups.Dobrushin.Specification

set_option linter.unusedSimpArgs false

open MeasureTheory Finset

noncomputable section

variable {I : Type*} [DecidableEq I] {S : Type*} [MeasurableSpace S]

/-- On a finite lattice, the conditional distribution at Λ = univ
does not depend on the boundary σ (since Λᶜ = ∅). -/
theorem condDist_univ_const [Fintype I] (γ : GibbsSpec I S)
    (σ τ : SpinConfig I S) :
    γ.condDist Finset.univ σ = γ.condDist Finset.univ τ :=
  γ.consistent Finset.univ σ τ (fun x hx => by
    simp [Finset.mem_univ] at hx)

/-- **Uniqueness of Gibbs measures on a finite lattice.**

For a Gibbs specification on a finite lattice (Fintype I), there is
at most one Gibbs measure: any two Gibbs measures μ₁, μ₂ are equal.

This requires NO Dobrushin condition. The proof uses DLR at Λ = univ
and the fact that `γ(univ, σ)` is constant in σ on a finite lattice. -/
theorem finite_lattice_uniqueness [Fintype I] [Nonempty I]
    (γ : GibbsSpec I S)
    (μ₁ μ₂ : Measure (SpinConfig I S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : IsGibbsMeasure γ μ₁) (h₂ : IsGibbsMeasure γ μ₂) :
    μ₁ = μ₂ := by
  -- Pick any configuration σ₀ (needs Nonempty I to pick a spin at each site,
  -- but actually we need a default spin — use Classical).
  classical
  -- We show μ₁ = μ₂ by showing they agree on all measurable sets.
  ext A hA
  -- By DLR at Λ = univ, (μᵢ A).toReal = ∫ (γ(univ, σ)(A)).toReal dμᵢ.
  have hdlr₁ := h₁.dlr Finset.univ A hA
  have hdlr₂ := h₂.dlr Finset.univ A hA
  -- The integrand γ(univ, σ)(A) is constant in σ (by condDist_univ_const).
  -- So ∫ ... dμ₁ = ∫ ... dμ₂, both equal the constant value.
  -- Pick σ₀ arbitrarily via Classical.inhabited_of_nonempty.
  -- Actually, to prove the integrand is constant, we need a default σ to
  -- compare with. Any σ works; use an arbitrary choice.
  -- The key: γ(univ, σ)(A) = γ(univ, τ)(A) for all σ, τ.
  -- So the function σ ↦ (γ(univ, σ)(A)).toReal is constant.
  -- Hence the integral = constant · μᵢ(univ) = constant.
  -- And both equal γ(univ, σ₀)(A).toReal.
  -- To handle this: convert μ₁ A and μ₂ A via toReal equalities.
  have hμ₁_fin : μ₁ A ≠ ⊤ := measure_ne_top _ _
  have hμ₂_fin : μ₂ A ≠ ⊤ := measure_ne_top _ _
  -- Both (μ A).toReal equal ∫ γ(univ, σ)(A).toReal dμ. We show the integral
  -- equals γ(univ, σ₀)(A).toReal for any σ₀.
  -- Reduce to (μ₁ A).toReal = (μ₂ A).toReal then ENNReal injectivity.
  rw [← ENNReal.ofReal_toReal hμ₁_fin, ← ENNReal.ofReal_toReal hμ₂_fin]
  congr 1
  -- Goal: (μ₁ A).toReal = (μ₂ A).toReal
  -- We show both equal the constant c = (γ.condDist univ σ₀ A).toReal
  -- for any σ₀ we pick.
  -- Pick σ₀ arbitrary (uses Nonempty I + Nonempty S).
  -- Actually, we can avoid picking σ₀ by using DLR equality directly.
  rw [hdlr₁, hdlr₂]
  -- Now goal: ∫ σ, (γ(univ, σ)(A)).toReal dμ₁ = ∫ σ, (γ(univ, σ)(A)).toReal dμ₂
  -- Both integrands are the SAME CONSTANT function (by condDist_univ_const).
  -- So both integrals equal the constant value times the total mass (= 1).
  -- Set the constant.
  have h_const : ∀ σ τ : SpinConfig I S,
      (γ.condDist Finset.univ σ A).toReal = (γ.condDist Finset.univ τ A).toReal := by
    intro σ τ
    rw [condDist_univ_const γ σ τ]
  -- The function σ ↦ (γ.condDist univ σ A).toReal is constant. Integration
  -- of a constant against a probability measure gives the constant.
  -- Need a canonical σ₀ to evaluate. Use Classical.arbitrary on Nonempty.
  obtain ⟨i⟩ := (inferInstance : Nonempty I)
  -- Actually, we need a Nonempty S or a default spin. Let's just pick any
  -- function σ : I → S. If S is empty, SpinConfig I S is empty iff I nonempty.
  -- To avoid this case analysis, use that both integrals equal each other
  -- by function extensionality.
  -- Actually the cleanest: both integrands are EQUAL as functions.
  have h_eq_fn :
      (fun σ : SpinConfig I S => (γ.condDist Finset.univ σ A).toReal) =
      (fun σ : SpinConfig I S => (γ.condDist Finset.univ σ A).toReal) := rfl
  -- The two integrals have the same integrand. But different measures.
  -- For a constant function, both integrals equal const · measure(univ) = const.
  -- Let c = (γ.condDist univ σ₀ A).toReal for an arbitrary σ₀.
  -- Case on whether SpinConfig I S is empty.
  by_cases hemp : IsEmpty (SpinConfig I S)
  · -- If configs are empty, both integrals are 0.
    have h1 : ∫ σ, (γ.condDist Finset.univ σ A).toReal ∂μ₁ = 0 := by
      apply integral_of_isEmpty
    have h2 : ∫ σ, (γ.condDist Finset.univ σ A).toReal ∂μ₂ = 0 := by
      apply integral_of_isEmpty
    rw [h1, h2]
  · rw [not_isEmpty_iff] at hemp
    obtain ⟨σ₀⟩ := hemp
    -- The function is constant equal to (γ(univ, σ₀)(A)).toReal.
    set c := (γ.condDist Finset.univ σ₀ A).toReal with hc_def
    have hf_eq : ∀ σ, (γ.condDist Finset.univ σ A).toReal = c :=
      fun σ => h_const σ σ₀
    calc ∫ σ, (γ.condDist Finset.univ σ A).toReal ∂μ₁
        = ∫ _, c ∂μ₁ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hf_eq
      _ = c := by simp [integral_const, IsProbabilityMeasure.measure_univ]
      _ = ∫ _, c ∂μ₂ := by
          simp [integral_const, IsProbabilityMeasure.measure_univ]
      _ = ∫ σ, (γ.condDist Finset.univ σ A).toReal ∂μ₂ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun σ => (hf_eq σ).symm)

end
