/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dirichlet Forms and Markov Semigroups

Layer 1 of the abstraction hierarchy. A `DirichletSpace` bundles a
probability measure μ with a symmetric energy form E(f,g), providing the
minimal structure for Poincaré and log-Sobolev inequalities.

No gradient, metric, or manifold structure is assumed.

## Main definitions

- `DirichletSpace` — probability measure + symmetric energy form
- `DirichletSpace.variance` — Var_μ(f) = E[f²] - E[f]²
- `DirichletSpace.entropy` — Ent_μ(f) = ∫ f log f dμ - (∫ f dμ) log(∫ f dμ)

## References

- Fukushima, Oshima, and Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, de Gruyter, 2011
- Ma and Röckner, *Introduction to the Theory of (Non-Symmetric)
  Dirichlet Forms*, Springer, 1992
- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 1
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory

noncomputable section

/-- A Dirichlet space: a probability space equipped with a symmetric
energy form (Dirichlet form).

This is the minimal structure for stating Poincaré and log-Sobolev
inequalities. No gradient or geometry is assumed.

The energy form `E(f,g)` abstracts the integral `∫ ⟨∇f, ∇g⟩ dμ` that
appears on the right side of these inequalities. On ℝⁿ with the
Gaussian measure, `E(f,g) = ∫ ⟨∇f, ∇g⟩ dγ`. On a finite graph,
`E(f,g) = ½ Σ_{x~y} (f(x)-f(y))(g(x)-g(y)) μ(x)`. The abstract
formulation covers both. -/
class DirichletSpace (X : Type*) [MeasurableSpace X] where
  /-- Reference probability measure. -/
  μ : Measure X
  /-- The measure is a probability measure. -/
  hμ : IsProbabilityMeasure μ
  /-- Symmetric energy form (Dirichlet form): E(f, g). -/
  energy : (X → ℝ) → (X → ℝ) → ℝ
  /-- Energy is symmetric. -/
  energy_symm : ∀ f g, energy f g = energy g f
  /-- Energy is nonneg on the diagonal. -/
  energy_nonneg : ∀ f, 0 ≤ energy f f
  /-- Energy is bilinear (left). -/
  energy_add_left : ∀ f₁ f₂ g, energy (f₁ + f₂) g = energy f₁ g + energy f₂ g
  /-- Energy is bilinear (scalar left). -/
  energy_smul_left : ∀ (c : ℝ) f g, energy (c • f) g = c * energy f g
  /-- Constants have zero energy (Markov property consequence). -/
  energy_const : ∀ c : ℝ, energy (fun _ => c) (fun _ => c) = 0

attribute [instance] DirichletSpace.hμ

namespace DirichletSpace

variable {X : Type*} [MeasurableSpace X] [ds : DirichletSpace X]

/-- Variance of f under the reference measure. -/
def variance (f : X → ℝ) : ℝ :=
  ∫ x, (f x) ^ 2 ∂ds.μ - (∫ x, f x ∂ds.μ) ^ 2

/-- Entropy of a nonneg function f under the reference measure. -/
def entropy (f : X → ℝ) : ℝ :=
  ∫ x, f x * Real.log (f x) ∂ds.μ -
  (∫ x, f x ∂ds.μ) * Real.log (∫ x, f x ∂ds.μ)

/-- Poincaré inequality with constant ρ:
  Var_μ(f) ≤ (1/ρ) E(f, f) -/
def SatisfiesPoincare (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ f : X → ℝ, variance f ≤ (1 / ρ) * ds.energy f f

/-- Log-Sobolev inequality with constant ρ:
  Ent_μ(f²) ≤ (2/ρ) E(f, f) -/
def SatisfiesLogSobolev (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ f : X → ℝ, entropy (f · f) ≤ (2 / ρ) * ds.energy f f

/-- LSI implies Poincaré with the same constant. -/
theorem logSobolev_implies_poincare {ρ : ℝ} (h : SatisfiesLogSobolev (ds := ds) ρ) :
    SatisfiesPoincare (ds := ds) ρ := by
  sorry

end DirichletSpace

end
