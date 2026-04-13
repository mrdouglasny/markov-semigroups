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

/-- A lattice in Z^d. We work with `Fin d → ℤ` as sites. -/
abbrev LatticeSite (d : ℕ) := Fin d → ℤ

/-- Lattice distance (ℓ¹ norm). -/
def latticeDist {d : ℕ} (x y : LatticeSite d) : ℕ :=
  ∑ i, (x i - y i).natAbs

/-- A spin configuration assigns a spin value to each site in a region. -/
abbrev SpinConfig (d : ℕ) (S : Type*) := LatticeSite d → S

/-! ## Gibbs specification -/

/-- A Gibbs specification on Z^d with spin space S.

For each finite region Λ (given as `Finset (LatticeSite d)`) and
boundary condition (configuration on Λᶜ), it gives a probability
measure on configurations restricted to Λ. -/
structure GibbsSpec (d : ℕ) (S : Type*) [MeasurableSpace S] where
  /-- The conditional distribution on Λ given boundary σ. -/
  condDist : (Λ : Finset (LatticeSite d)) →
    SpinConfig d S → Measure (SpinConfig d S)
  /-- Each conditional distribution is a probability measure. -/
  isProb : ∀ Λ σ, IsProbabilityMeasure (condDist Λ σ)
  /-- Consistency: the specification only depends on σ outside Λ.
      If σ and τ agree on Λᶜ, the conditional distributions agree. -/
  consistent : ∀ (Λ : Finset (LatticeSite d)) (σ τ : SpinConfig d S),
    (∀ x, x ∉ Λ → σ x = τ x) → condDist Λ σ = condDist Λ τ
  /-- Properness: condDist(Λ, σ) is concentrated on configurations
      that agree with σ outside Λ. Without this, the specification
      could assign mass to configs violating the boundary condition. -/
  proper : ∀ (Λ : Finset (LatticeSite d)) (σ : SpinConfig d S),
    condDist Λ σ {τ | ∀ x, x ∉ Λ → τ x = σ x} = 1
  /-- Measurability: σ ↦ condDist(Λ, σ)(A) is measurable.
      Required for the DLR integral to be well-defined. -/
  measurable_condDist : ∀ (Λ : Finset (LatticeSite d))
    (A : Set (SpinConfig d S)) (hA : MeasurableSet A),
    Measurable (fun σ : SpinConfig d S => (condDist Λ σ A).toReal)

attribute [instance] GibbsSpec.isProb

/-- A probability measure μ on spin configurations is a Gibbs measure
for specification γ if it is consistent with all conditional distributions:
for every finite Λ, the conditional distribution of μ given the
configuration outside Λ equals γ(Λ, ·) μ-a.s. -/
structure IsGibbsMeasure {d : ℕ} {S : Type*} [MeasurableSpace S]
    (γ : GibbsSpec d S) (μ : Measure (SpinConfig d S))
    [IsProbabilityMeasure μ] : Prop where
  /-- DLR consistency condition. -/
  dlr : ∀ (Λ : Finset (LatticeSite d))
    (A : Set (SpinConfig d S)) (hA : MeasurableSet A),
    (μ A).toReal = ∫ σ, (γ.condDist Λ σ A).toReal ∂μ

end
