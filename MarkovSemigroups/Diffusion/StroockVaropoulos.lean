/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stroock–Varopoulos for diffusion (carré-du-champ) forms

For a `BakryEmerySpace` whose carré-du-champ `Γ` satisfies the **rpow chain rule**
`Γ(uʳ, g) = r·u^{r-1}·Γ(u, g)` (the diffusion property specialized to power
functions), the Stroock–Varopoulos comparison is in fact an **equality**

  `(4(q-1)/q²) · E(u^{q/2}, u^{q/2}) = E(u, u^{q-1})`   (for `u > 0`, `q > 1`).

This is the "level B" of the Stroock–Varopoulos hierarchy: it holds for every
diffusion form (gradient / carré-du-champ with the chain rule), strictly more
general than the concrete Gaussian instance and strictly less general than the
abstract `stroock_varopoulos` axiom (which covers all Markovian Dirichlet forms,
where S–V is only an *inequality*, proved via Beurling–Deny convexity against the
jump kernel).

## Main results

* `BakryEmerySpace.RpowChainRule` — the diffusion chain rule for power functions.
* `BakryEmerySpace.stroockVaropoulos_eq` — S–V equality from `RpowChainRule`.

## Extending to more general forms

A non-diffusion Markovian Dirichlet form satisfies S–V only as an inequality
`(4(q-1)/q²)·E(u^{q/2},u^{q/2}) ≤ E(u,u^{q-1})`, proved from the Beurling–Deny
representation and convexity of `(a,b) ↦ (a^{q/2}-b^{q/2})² · …`. Such a proof
would be added here as `…stroockVaropoulos_le` against the appropriate weaker
structural hypothesis (a jump-kernel/Beurling–Deny field on the form), and the
diffusion `…_eq` below is the special case where the jump part vanishes.

## References

* Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion Operators*
  (2014), §1.7 (Stroock–Varopoulos), §3.1 (the chain rule `Γ(φ(f),g)=φ'(f)Γ(f,g)`
  for diffusion operators).
-/

import MarkovSemigroups.Diffusion.CarreDuChamp

open MeasureTheory

namespace BakryEmerySpace

variable {X : Type*} [MeasurableSpace X]

/-- **Diffusion chain rule for power functions.** A carré-du-champ satisfies the
`rpow` chain rule if, for strictly positive core `u`, any core `g`, and any real
exponent `r`,
  `Γ(uʳ, g) = r · u^{r-1} · Γ(u, g)`.
This is the diffusion property `Γ(φ(u), g) = φ'(u)·Γ(u, g)` specialized to
`φ = (·)ʳ` — exactly what Stroock–Varopoulos needs. It holds for any gradient form
`Γ(f, g) = ⟨∇f, ∇g⟩` by the pointwise chain rule. -/
def RpowChainRule (be : BakryEmerySpace X) : Prop :=
  ∀ {u : X → ℝ}, be.IsCore u → (∀ x, 0 < u x) → ∀ {g : X → ℝ}, be.IsCore g →
    ∀ (r : ℝ) (x : X),
      be.Γ (fun y => u y ^ r) g x = r * u x ^ (r - 1) * be.Γ u g x

/-- **Stroock–Varopoulos equality for diffusion forms.** When the carré-du-champ
satisfies the `rpow` chain rule, for strictly positive core `u` and `q > 1` (with
`u^{q/2}`, `u^{q-1}` again core),
  `(4(q-1)/q²) · E(u^{q/2}, u^{q/2}) = E(u, u^{q-1})`.
Both sides reduce pointwise to `(q-1)·u^{q-2}·Γ(u,u)`. -/
theorem stroockVaropoulos_eq (be : BakryEmerySpace X) (hchain : be.RpowChainRule)
    {u : X → ℝ} (hu : be.IsCore u) (hu_pos : ∀ x, 0 < u x)
    (q : ℝ) (hq : 1 < q)
    (hu_half : be.IsCore (fun x => u x ^ (q / 2)))
    (hu_one : be.IsCore (fun x => u x ^ (q - 1))) :
    (4 * (q - 1) / q ^ 2) *
        be.energy (fun x => u x ^ (q / 2)) (fun x => u x ^ (q / 2))
      = be.energy u (fun x => u x ^ (q - 1)) := by
  have hq0 : q ≠ 0 := by positivity
  -- Pointwise identity: both integrands equal `(q-1)·u^{q-2}·Γ(u,u)`.
  have hpt : ∀ x, (4 * (q - 1) / q ^ 2) *
        be.Γ (fun y => u y ^ (q / 2)) (fun y => u y ^ (q / 2)) x
      = be.Γ u (fun y => u y ^ (q - 1)) x := by
    intro x
    -- `Γ(u^{q/2}, u^{q/2}) = (q/2)·u^{q/2-1} · Γ(u, u^{q/2})`, and
    -- `Γ(u, u^{q/2}) = (q/2)·u^{q/2-1} · Γ(u,u)` (symmetry + chain rule).
    have hΓhalf : be.Γ u (fun y => u y ^ (q / 2)) x
        = (q / 2) * u x ^ (q / 2 - 1) * be.Γ u u x := by
      rw [be.Γ_symm u (fun y => u y ^ (q / 2)), hchain hu hu_pos hu (q / 2) x]
    have h1 : be.Γ (fun y => u y ^ (q / 2)) (fun y => u y ^ (q / 2)) x
        = (q / 2) * u x ^ (q / 2 - 1) *
            ((q / 2) * u x ^ (q / 2 - 1) * be.Γ u u x) := by
      rw [hchain hu hu_pos hu_half (q / 2) x, hΓhalf]
    -- `Γ(u, u^{q-1}) = (q-1)·u^{q-1-1} · Γ(u,u)`.
    have hΓone : be.Γ u (fun y => u y ^ (q - 1)) x
        = (q - 1) * u x ^ (q - 1 - 1) * be.Γ u u x := by
      rw [be.Γ_symm u (fun y => u y ^ (q - 1)), hchain hu hu_pos hu (q - 1) x]
    -- Combine the two `u^{q/2-1}` factors into `u^{q-1-1}`.
    have hexp : u x ^ (q / 2 - 1) * u x ^ (q / 2 - 1) = u x ^ (q - 1 - 1) := by
      rw [← Real.rpow_add (hu_pos x)]
      congr 1
      ring
    rw [h1, hΓone, ← hexp]
    field_simp
    ring
  -- Integrate the pointwise identity.
  rw [be.energy_eq_integral_Γ, be.energy_eq_integral_Γ, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ hpt)

end BakryEmerySpace
