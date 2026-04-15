/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gibbs Specifications on Lattice Spin Systems

## Overview

A Gibbs specification assigns to each finite region Λ ⊂ Z^d and boundary
condition σ_{Λᶜ} a conditional probability measure on spin configurations
in Λ. A Gibbs measure is a probability measure consistent with all these
conditional distributions.

## Main definitions

- `LatticeSite` — sites in Z^d
- `SpinConfig` — spin configuration Λ → S (spins at each site)
- `GibbsSpec` — Gibbs specification: conditional distributions given boundary
- `IsGibbsMeasure` — consistency: μ(·|σ_{Λᶜ}) = spec(Λ, σ_{Λᶜ})(·) a.s.

## References

- Chatterjee, *Gauge Theory Lecture Notes* (2026), Ch 16
- Georgii, *Gibbs Measures and Phase Transitions*, de Gruyter, 2011
- Friedli and Velenik, *Statistical Mechanics of Lattice Systems*, Cambridge, 2017
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Topology.MetricSpace.Basic

open MeasureTheory

noncomputable section

/-! ## Lattice sites and spin configurations -/

/-- A spin configuration assigns a spin value to each site `I`.
The site type `I` is left abstract; the canonical example for lattice
spin systems is `I = LatticeSite d := Fin d → ℤ`. -/
abbrev SpinConfig (I : Type*) (S : Type*) := I → S

/-- A lattice in Z^d. We work with `Fin d → ℤ` as sites.
Kept as an alias for backward compatibility and as the canonical
example of a site type; the abstract `GibbsSpec` and `IsGibbsMeasure`
no longer hardcode this choice. -/
abbrev LatticeSite (d : ℕ) := Fin d → ℤ

/-- Lattice distance (ℓ¹ norm) on `Z^d`. Specific to the canonical
ℤ^d site type; not used by the abstract Gibbs specification API. -/
def latticeDist {d : ℕ} (x y : LatticeSite d) : ℕ :=
  ∑ i, (x i - y i).natAbs

/-- `latticeDist` is reflexive: `d(x, x) = 0`. -/
lemma latticeDist_self {d : ℕ} (x : LatticeSite d) : latticeDist x x = 0 := by
  simp [latticeDist]

/-- `latticeDist` satisfies the triangle inequality. -/
lemma latticeDist_triangle {d : ℕ} (x y z : LatticeSite d) :
    latticeDist x y ≤ latticeDist x z + latticeDist z y := by
  unfold latticeDist
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  -- (x i - y i).natAbs ≤ (x i - z i).natAbs + (z i - y i).natAbs
  have : x i - y i = (x i - z i) + (z i - y i) := by ring
  rw [this]
  exact Int.natAbs_add_le _ _

/-! ## Gibbs specification -/

/-- A Gibbs specification on a generic site set `I` with spin space `S`.

For each finite region `Λ : Finset I` and boundary condition (a
configuration on `Λᶜ`), it gives a probability measure on
configurations restricted to `Λ`.

The site type `I` is fully generic; canonical examples include
`LatticeSite d = Fin d → ℤ` (infinite lattice) or any finite index
type for finite-volume specifications. The `[DecidableEq I]`
instance is needed for `Finset I` operations. -/
structure GibbsSpec (I : Type*) [DecidableEq I] (S : Type*)
    [MeasurableSpace S] where
  /-- The conditional distribution on Λ given boundary σ. -/
  condDist : (Λ : Finset I) →
    SpinConfig I S → Measure (SpinConfig I S)
  /-- Each conditional distribution is a probability measure. -/
  isProb : ∀ Λ σ, IsProbabilityMeasure (condDist Λ σ)
  /-- Consistency: the specification only depends on σ outside Λ.
      If σ and τ agree on Λᶜ, the conditional distributions agree. -/
  consistent : ∀ (Λ : Finset I) (σ τ : SpinConfig I S),
    (∀ x, x ∉ Λ → σ x = τ x) → condDist Λ σ = condDist Λ τ
  /-- Properness: condDist(Λ, σ) is concentrated on configurations
      that agree with σ outside Λ. Without this, the specification
      could assign mass to configs violating the boundary condition. -/
  proper : ∀ (Λ : Finset I) (σ : SpinConfig I S),
    condDist Λ σ {τ | ∀ x, x ∉ Λ → τ x = σ x} = 1
  /-- Measurability: σ ↦ condDist(Λ, σ)(A) is measurable.
      Required for the DLR integral to be well-defined. -/
  measurable_condDist : ∀ (Λ : Finset I)
    (A : Set (SpinConfig I S)) (hA : MeasurableSet A),
    Measurable (fun σ : SpinConfig I S => (condDist Λ σ A).toReal)

attribute [instance] GibbsSpec.isProb

/-- A probability measure μ on spin configurations is a Gibbs measure
for specification γ if it is consistent with all conditional distributions:
for every finite Λ, the conditional distribution of μ given the
configuration outside Λ equals γ(Λ, ·) μ-a.s. -/
structure IsGibbsMeasure {I : Type*} [DecidableEq I] {S : Type*}
    [MeasurableSpace S]
    (γ : GibbsSpec I S) (μ : Measure (SpinConfig I S))
    [IsProbabilityMeasure μ] : Prop where
  /-- DLR consistency condition. -/
  dlr : ∀ (Λ : Finset I)
    (A : Set (SpinConfig I S)) (hA : MeasurableSet A),
    (μ A).toReal = ∫ σ, (γ.condDist Λ σ A).toReal ∂μ

end
