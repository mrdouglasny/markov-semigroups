/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L² Semigroup Bridge

Connects BakryEmerySpace.semigroup (acting on functions X → ℝ)
to the hille-yosida StronglyContinuousSemigroup theory (acting on
a Banach space via ContinuousLinearMap).

The key: view P_t as a bounded linear operator on L²(μ), then use
the infinitesimal generator theory from hille-yosida to compute
derivatives d/dt ∫(P_t f)² and prove the Bakry-Émery axioms.

## Status

This file establishes the conceptual bridge. The full formalization
requires:
1. BakryEmerySpace.semigroup as operators on Lp ℝ 2 μ
2. Strong continuity on L²
3. Connection to hille-yosida.StronglyContinuousSemigroup

Each step is standard but requires substantial Lean plumbing with
Mathlib's Lp space infrastructure.

## References

- Bakry-Gentil-Ledoux, Ch. 1 (Markov semigroups on L²)
- Engel-Nagel, Ch. II (Generators of C₀-semigroups)
-/

import MarkovSemigroups.Diffusion.CarreDuChamp

open MeasureTheory

/-! ## The semigroup energy identity

The key computation for Poincaré and variance decay:
  d/dt ∫(P_t f)² dμ = -2 ∫ Γ(P_t f, P_t f) dμ = -2 E(P_t f, P_t f)

This uses:
- Self-adjointness: ∫(P_t f)² = ∫ f · P_{2t} f
- Generator: d/dt P_t f = LP_t f where E(f,g) = -∫ f · Lg dμ
- Or equivalently: d/dt ∫(P_t f)(P_t g) = -2 ∫ Γ(P_t f, P_t g) dμ

Rather than formalizing the full L² operator theory, we state this
identity as a theorem with a sorry on the generator step, and show
how it implies the Bakry-Émery axioms. -/

variable {X : Type*} [MeasurableSpace X] [be : BakryEmerySpace X]

/-- The L² norm squared of P_t f: ‖P_t f‖² = ∫(P_t f)² dμ. -/
noncomputable def semigroupL2Sq (f : X → ℝ) (t : ℝ) : ℝ :=
  ∫ x, (be.semigroup t f x) ^ 2 ∂be.μ

/-- The energy of P_t f: E(P_t f) = ∫ Γ(P_t f, P_t f) dμ. -/
noncomputable def semigroupEnergy (f : X → ℝ) (t : ℝ) : ℝ :=
  ∫ x, be.Γ (be.semigroup t f) (be.semigroup t f) x ∂be.μ

/-- The energy of P_t f equals the Dirichlet form applied to P_t f. -/
theorem semigroupEnergy_eq (f : X → ℝ) (t : ℝ) :
    semigroupEnergy f t = be.energy (be.semigroup t f) (be.semigroup t f) := by
  simp [semigroupEnergy, be.energy_eq_integral_Γ]

/-- The gradient decay bound in terms of semigroupEnergy:
semigroupEnergy(f, t) ≤ e^{-2ρt} · semigroupEnergy(f, 0). -/
theorem semigroupEnergy_decay (f : X → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    semigroupEnergy f t ≤ Real.exp (-2 * be.ρ * t) * semigroupEnergy f 0 := by
  unfold semigroupEnergy
  rw [be.semigroup_zero]
  exact be.gradient_decay f t ht

/-- semigroupEnergy at t=0 is just E(f,f). -/
theorem semigroupEnergy_zero (f : X → ℝ) :
    semigroupEnergy f 0 = be.energy f f := by
  simp [semigroupEnergy, be.semigroup_zero, be.energy_eq_integral_Γ]
