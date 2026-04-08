/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Carré du Champ and Bakry-Émery Spaces

Layer 2 of the abstraction hierarchy. A `BakryEmerySpace` extends a
`DirichletSpace` with a carré du champ operator Γ (abstract "squared
gradient") and a curvature lower bound ρ > 0.

No manifold or metric is assumed. On a Riemannian manifold (M, g) with
generator L = Δ - ∇U · ∇:
  Γ(f, g) = ⟨∇f, ∇g⟩_g
  Γ₂(f, f) = ‖Hess f‖² + (Ric + Hess U)(∇f, ∇f)
  curvature ρ ↔ Ric + Hess U ≥ ρ g

But the abstract definition works for any diffusion generator where Γ
and Γ₂ make sense.

## Main definitions

- `BakryEmerySpace` — DirichletSpace + Γ + curvature bound
- `BakryEmerySpace.Γ₂` — iterated carré du champ

## Main theorems

- `BakryEmerySpace.satisfiesLogSobolev` — curvature ρ ⟹ LSI(ρ)
- `BakryEmerySpace.satisfiesPoincare` — curvature ρ ⟹ Poincaré(ρ)

## References

- Bakry and Émery, "Diffusions hypercontractives," Séminaire de
  probabilités XIX, Springer LNM 1123 (1985), 177–206
- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 1, 3, and 5
-/

import MarkovSemigroups.Abstract.DirichletForm

open MeasureTheory

noncomputable section

/-- A Bakry-Émery space: a Dirichlet space equipped with a carré du
champ operator Γ and a curvature lower bound ρ > 0.

The carré du champ Γ(f, g)(x) is the abstract "pointwise squared
gradient." It satisfies:
- E(f, g) = ∫ Γ(f, g) dμ  (energy = integral of Γ)
- Γ(f, f) ≥ 0  (nonneg)
- Γ(fg, h) = f Γ(g, h) + g Γ(f, h)  (Leibniz / diffusion property)

The curvature condition Γ₂(f, f) ≥ ρ Γ(f, f) (where Γ₂ is defined
from Γ and the generator) implies both the Poincaré inequality and the
log-Sobolev inequality with constant ρ. This is the Bakry-Émery
criterion.

On ℝⁿ with standard Gaussian: Γ(f, g) = ⟨∇f, ∇g⟩, ρ = 1.
On T^d with GFF (mass m): Γ(f, g) = ⟨∇f, ∇g⟩, ρ = m².
On a finite graph: Γ(f, f)(x) = ½ Σ_{y~x} (f(y) - f(x))², ρ depends
on the graph. -/
class BakryEmerySpace (X : Type*) [MeasurableSpace X]
    extends DirichletSpace X where
  /-- Carré du champ: abstract pointwise "squared gradient." -/
  Γ : (X → ℝ) → (X → ℝ) → (X → ℝ)
  /-- Γ is symmetric. -/
  Γ_symm : ∀ f g, Γ f g = Γ g f
  /-- Γ is nonneg on the diagonal. -/
  Γ_nonneg : ∀ f x, 0 ≤ Γ f f x
  /-- Energy is the integral of Γ. -/
  energy_eq_integral_Γ : ∀ f g, energy f g = ∫ x, Γ f g x ∂μ
  /-- Leibniz rule (diffusion property):
    Γ(fg, h) = f · Γ(g, h) + g · Γ(f, h) -/
  Γ_leibniz : ∀ f g h x,
    Γ (f * g) h x = f x * Γ g h x + g x * Γ f h x
  /-- Γ of a constant is zero. -/
  Γ_const : ∀ (c : ℝ) f, Γ (fun _ => c) f = 0
  /-- The associated Markov semigroup P_t. -/
  semigroup : ℝ → (X → ℝ) → (X → ℝ)
  /-- Curvature lower bound ρ > 0. -/
  ρ : ℝ
  hρ : 0 < ρ
  /-- The Bakry-Émery curvature condition: Γ₂(f, f) ≥ ρ · Γ(f, f).

  Here Γ₂ is defined implicitly: if L is the generator of the semigroup
  (with E(f,g) = -∫ f Lg dμ), then
    Γ₂(f, g) = ½(L Γ(f,g) - Γ(f, Lg) - Γ(Lf, g)).

  Rather than formalizing L and Γ₂ separately, we axiomatize the
  consequence directly: the semigroup interpolation inequality
    ∫ Γ(P_t f, P_t f) dμ ≤ e^{-2ρt} ∫ Γ(f, f) dμ
  which is equivalent to Γ₂ ≥ ρΓ by differentiation at t = 0.

  This avoids needing the generator domain and is more directly usable. -/
  gradient_decay : ∀ (f : X → ℝ) (t : ℝ), 0 ≤ t →
    ∫ x, Γ (semigroup t f) (semigroup t f) x ∂μ ≤
    Real.exp (-2 * ρ * t) * ∫ x, Γ f f x ∂μ
  /-- P_0 = id. -/
  semigroup_zero : ∀ f, semigroup 0 f = f
  /-- Semigroup property: P_{s+t} = P_s ∘ P_t. -/
  semigroup_add : ∀ s t f, 0 ≤ s → 0 ≤ t →
    semigroup (s + t) f = semigroup s (semigroup t f)
  /-- P_t is a contraction on L²(μ). -/
  semigroup_contraction : ∀ (f : X → ℝ) (t : ℝ), 0 ≤ t →
    ∫ x, (semigroup t f x) ^ 2 ∂μ ≤ ∫ x, (f x) ^ 2 ∂μ
  /-- P_t preserves the mean. -/
  semigroup_mean : ∀ (f : X → ℝ) (t : ℝ), 0 ≤ t →
    ∫ x, semigroup t f x ∂μ = ∫ x, f x ∂μ
  /-- P_t is self-adjoint on L²(μ). -/
  semigroup_selfAdjoint : ∀ (f g : X → ℝ) (t : ℝ), 0 ≤ t →
    ∫ x, semigroup t f x * g x ∂μ = ∫ x, f x * semigroup t g x ∂μ

/-! ## Postulated textbook results for Bakry-Émery theory -/

/-- **Postulated (Bakry-Émery 1985).** Curvature Γ₂ ≥ ρΓ implies Poincaré(ρ).
Proof: Var(f) = 2∫₀^∞ E(P_t f, P_t f) dt ≤ 2∫₀^∞ e^{-2ρt} E(f,f) dt = (1/ρ)E(f,f).
Reference: BGL Theorem 4.8.4. -/
axiom bakryEmery_poincare {X : Type*} [MeasurableSpace X] [be : BakryEmerySpace X] :
    DirichletSpace.SatisfiesPoincare (ds := be.toDirichletSpace) be.ρ

/-- **Postulated (Bakry-Émery 1985).** Curvature Γ₂ ≥ ρΓ implies LSI(ρ).
Proof: semigroup interpolation — define Φ(t) = Ent(P_t f) and show
Φ'(t) ≤ -2ρΦ(t) using the curvature condition. Grönwall gives
Ent(f) ≤ Φ(0) ≤ (1/2ρ)(-Φ'(0)) = (1/2ρ)E(f,f).
Reference: BGL Theorem 5.5.2. -/
axiom bakryEmery_logSobolev {X : Type*} [MeasurableSpace X] [be : BakryEmerySpace X] :
    DirichletSpace.SatisfiesLogSobolev (ds := be.toDirichletSpace) be.ρ

/-- **Postulated.** Exponential variance decay from curvature bound.
Var(P_t f) ≤ e^{-2ρt} Var(f) follows from gradient_decay axiom
via the identity Var(f) = ∫ Γ(f,f) dμ - (energy contribution).
Reference: BGL Proposition 4.8.1. -/
axiom bakryEmery_variance_decay {X : Type*} [MeasurableSpace X] [be : BakryEmerySpace X]
    (f : X → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    DirichletSpace.variance (ds := be.toDirichletSpace) (be.semigroup t f) ≤
    Real.exp (-2 * be.ρ * t) *
    DirichletSpace.variance (ds := be.toDirichletSpace) f

namespace BakryEmerySpace

variable {X : Type*} [MeasurableSpace X] [be : BakryEmerySpace X]

/-- The Bakry-Émery curvature condition implies Poincaré(ρ).

Proof sketch: From gradient_decay and the spectral decomposition of P_t,
  Var_μ(f) = ∫₀^∞ d/dt [-Var_μ(P_t f)] dt = 2 ∫₀^∞ E(P_t f, P_t f) dt
           ≤ 2 ∫₀^∞ e^{-2ρt} E(f,f) dt = (1/ρ) E(f,f). -/
theorem satisfiesPoincare :
    DirichletSpace.SatisfiesPoincare (ds := be.toDirichletSpace) be.ρ :=
  bakryEmery_poincare

/-- The Bakry-Émery curvature condition implies LSI(ρ).

This is the main theorem of Bakry-Émery (1985). The proof uses the
semigroup interpolation method: define Φ(t) = Ent_μ(P_t f) and show
Φ'(t) ≤ -2ρ Φ(t) using the curvature condition. Integrating gives
Ent_μ(f) ≤ (1/ρ) ∫ Γ(√f, √f) dμ = (1/2ρ) ∫ Γ(f,f)/f dμ, which
is the Bakry-Émery form of the LSI. -/
theorem satisfiesLogSobolev :
    DirichletSpace.SatisfiesLogSobolev (ds := be.toDirichletSpace) be.ρ :=
  bakryEmery_logSobolev

/-- Exponential variance decay: Var_μ(P_t f) ≤ e^{-2ρt} Var_μ(f). -/
theorem variance_decay (f : X → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    DirichletSpace.variance (ds := be.toDirichletSpace) (be.semigroup t f) ≤
    Real.exp (-2 * be.ρ * t) *
    DirichletSpace.variance (ds := be.toDirichletSpace) f :=
  bakryEmery_variance_decay f t ht

end BakryEmerySpace

end
