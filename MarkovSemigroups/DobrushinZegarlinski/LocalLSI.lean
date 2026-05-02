/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Local Log-Sobolev Hypothesis (Zegarlinski)

A thin, fderiv-based formulation of the log-Sobolev inequality on a
finite-dimensional inner-product space, decoupled from the Dirichlet
form / semigroup machinery in `Abstract/DirichletForm.lean`. This is
the predicate used in the Zegarlinski hypothesis: every conditional
distribution at a single site, *uniformly in the boundary*, satisfies
LSI with the same constant `c`.

## Why a separate predicate

`DirichletSpace.SatisfiesLogSobolev` requires committing to a Dirichlet
space (and thus an `IsCore` smoothness scaffold) ahead of time, which
is far heavier than what the local Zegarlinski hypothesis needs. Here
we just want:

  Ent_μ(f²) ≤ (2/c) ∫ ‖∇f‖² dμ ,    for all `Differentiable ℝ f`.

This is a property of the measure alone, on any inner-product space.
It is provably equivalent to the Dirichlet-form LSI for the standard
constructions (Gaussian, OU, etc.); a bridge lemma can be added later.

## Site-conditional LSI: the spec-side phrasing

The Zegarlinski hypothesis must live at the level of the Gibbs
specification, not of any fixed Gibbs measure — the whole point is
that uniqueness/mass-gap follow from local data. So we phrase
`UniformLocalLSI` over `spec.condDist {x} σ` (single-site conditional
of the specification) for *every* boundary `σ`.

Since `spec.condDist {x} σ` lives on `SpinConfig Λ ℝ = Λ → ℝ` but is
concentrated on configurations agreeing with `σ` outside `{x}` (the
`proper` axiom of `GibbsSpec`), it is effectively a 1D measure
parametrized by the value at site `x`. We push it forward to `ℝ` via
the projection `(· x)` and require the 1D LSI on the resulting marginal.

## References

* Zegarlinski, *Lett. Math. Phys.* 20 (1990).
* Stroock and Zegarlinski, *Comm. Math. Phys.* 144 (1992), Thm. 0.1.
* BGL, *Analysis and Geometry of Markov Diffusion Operators*, §5.7.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import MarkovSemigroups.Dobrushin.Specification

noncomputable section

namespace MarkovSemigroups.DobrushinZegarlinski

open MeasureTheory

/-- Entropy of a function `g : E → ℝ` w.r.t. a probability measure
`μ`: `Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)`.

Used here in the form `Ent_μ(f²)` for the LSI predicate. -/
def entropy {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (g : E → ℝ) : ℝ :=
  (∫ x, g x * Real.log (g x) ∂μ)
    - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)

/-- A measure `μ` on a finite-dimensional inner-product space `E`
satisfies a log-Sobolev inequality with constant `c > 0` if for every
differentiable `f : E → ℝ`:

  Ent_μ(f²) ≤ (2/c) ∫ ‖∇f‖² dμ

where `‖∇f‖² = ‖fderiv ℝ f x‖²` (the operator norm on the dual; for
finite-dim Hilbert `E` this agrees with the Riesz-representative norm).

This is the form most natural for stating the Zegarlinski hypothesis
in a way that does not bind us to a specific Dirichlet form / core.

For `E = ℝ` (the single-site marginal), `fderiv ℝ f x` is just the
derivative `deriv f x` packaged as a continuous linear map, with norm
equal to `|deriv f x|`. -/
def SatisfiesLSI {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) (c : ℝ) : Prop :=
  0 < c ∧ ∀ f : E → ℝ, Differentiable ℝ f →
    Integrable (fun x => (f x) ^ 2) μ →
    Integrable (fun x => (f x) ^ 2 * Real.log ((f x) ^ 2)) μ →
    Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) μ →
    entropy μ (fun x => (f x) ^ 2) ≤
      (2 / c) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ

namespace SatisfiesLSI

variable {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

lemma c_pos {μ : Measure E} {c : ℝ} (h : SatisfiesLSI μ c) : 0 < c := h.1

lemma entropy_le {μ : Measure E} {c : ℝ} (h : SatisfiesLSI μ c)
    {f : E → ℝ} (hf : Differentiable ℝ f)
    (hf_sq_int : Integrable (fun x => (f x) ^ 2) μ)
    (hf_log_int : Integrable (fun x => (f x) ^ 2 * Real.log ((f x) ^ 2)) μ)
    (hgrad_int : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) μ) :
    entropy μ (fun x => (f x) ^ 2) ≤
      (2 / c) * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ :=
  h.2 f hf hf_sq_int hf_log_int hgrad_int

end SatisfiesLSI

/-! ## Site projection and conditional marginal

`spec.condDist {x} σ` lives on `SpinConfig Λ ℝ = Λ → ℝ`. The single-
site marginal at `x` is its pushforward through the projection
`(· x) : (Λ → ℝ) → ℝ`. -/

variable {Λ : Type*} [DecidableEq Λ]

/-- Projection of a configuration to its value at site `x`. Measurable
in the product σ-algebra. -/
def siteProj (x : Λ) : SpinConfig Λ ℝ → ℝ := fun σ => σ x

omit [DecidableEq Λ] in
lemma measurable_siteProj (x : Λ) :
    Measurable (siteProj (Λ := Λ) x) :=
  measurable_pi_apply x

/-- The 1D site-marginal of a single-site Gibbs conditional:
`(spec.condDist {x} boundary).map (· x) : Measure ℝ`. -/
def condSiteMarginal (spec : GibbsSpec Λ ℝ) (x : Λ)
    (boundary : SpinConfig Λ ℝ) : Measure ℝ :=
  (spec.condDist {x} boundary).map (siteProj x)

/-! ## Uniform local LSI

The site-conditional marginal at every site `x`, for every boundary
`σ`, satisfies the same 1D LSI with constant `c > 0`. This is exactly
the input the Zegarlinski theorem requires. -/

/-- A Gibbs specification on `Λ × ℝ` enjoys a *uniform local LSI* with
constant `c > 0` if all single-site conditional marginals satisfy a
log-Sobolev inequality with the same constant `c`, independently of
the boundary configuration.

This is the local restorative-force hypothesis: the conditional
distribution at any one site, no matter what the surrounding spins
are, has spectral gap (via LSI) at least `c`. -/
class UniformLocalLSI (spec : GibbsSpec Λ ℝ) (c : ℝ) : Prop where
  c_pos : 0 < c
  satisfies_lsi : ∀ (x : Λ) (boundary : SpinConfig Λ ℝ),
    SatisfiesLSI (condSiteMarginal spec x boundary) c

end MarkovSemigroups.DobrushinZegarlinski

end
