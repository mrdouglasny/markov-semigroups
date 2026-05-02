/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# EuclideanSpace Transport for Gibbs Measures

The `Dobrushin/Specification.lean` Gibbs framework lives on
`SpinConfig Λ ℝ = Λ → ℝ` with the *product* measurable structure.
The Zegarlinski layer's LSI predicate `SatisfiesLSI` lives on
`EuclideanSpace ℝ Λ = PiLp 2 (fun _ => ℝ)` with the borel structure
of the `ℓ²` norm. The two carry the same underlying functions but
distinguish two different norms / topologies (`L^∞` vs `L²`).

This adapter file packages the type-side bookkeeping once: pushing
forward a Gibbs measure from `SpinConfig Λ ℝ` to `EuclideanSpace ℝ Λ`,
declaring the canonical Borel σ-algebra on `EuclideanSpace ℝ Λ`, and
proving probability preservation under the pushforward.

Downstream callers (e.g. `pphi2N`) need only one line:
`spec.toEuclideanMeasure μ`.

## Main definitions

* `MeasurableSpace (EuclideanSpace ℝ Λ)` — Borel σ-algebra (instance).
* `BorelSpace (EuclideanSpace ℝ Λ)` — agreement of σ-algebra with
  the Borel topology (instance).
* `GibbsSpec.toEuclideanMeasure spec μ` — pushforward of `μ` via
  `(EuclideanSpace.equiv Λ ℝ).symm`. The `spec` argument is included
  for namespacing and method-style dot notation; it is not used in
  the body.

## Main theorems

* `GibbsSpec.isProbabilityMeasure_toEuclideanMeasure` — the
  pushforward of a probability measure is a probability measure.
* `GibbsSpec.toEuclideanMeasure_apply` — explicit formula for the
  pushforward measure on a Borel set.

## Status

* The pushforward is fully defined and probability preservation is
  proved.
* A separate `SatisfiesLSI` ↔ "Pi-norm LSI" bridge is *not* provided
  here: in finite dimensions, the L² and L^∞ Pi-norms generate the
  same topology and Borel σ-algebra (so the *measure* is the same up
  to retyping), but the operator norms `‖fderiv f x‖_{op}` differ in
  general. The Zegarlinski theorem uses the L² norm directly; if
  downstream consumers need to relate to the L^∞ Pi-norm version,
  they should compose with the explicit norm comparison constants.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpace
import MarkovSemigroups.Dobrushin.Specification

noncomputable section

namespace GibbsSpec

open MeasureTheory

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Borel σ-algebra on `EuclideanSpace ℝ Λ`. Required so that
`Measure (EuclideanSpace ℝ Λ)` is a meaningful type. Declared as a
plain `instance` (not `local`) so any importer of this file gets it
for free. -/
instance euclideanMeasurableSpace :
    MeasurableSpace (EuclideanSpace ℝ Λ) := borel _

instance euclideanBorelSpace :
    BorelSpace (EuclideanSpace ℝ Λ) := ⟨rfl⟩

/-- **Pushforward of a Gibbs measure to `EuclideanSpace ℝ Λ`.**

Given a measure `μ` on `SpinConfig Λ ℝ = Λ → ℝ` (Pi-product structure),
push it forward through the (continuous, linear) inverse of
`EuclideanSpace.equiv Λ ℝ` to obtain a measure on
`EuclideanSpace ℝ Λ = PiLp 2 (fun _ => ℝ)`.

At the level of *underlying functions*, this is the identity (PiLp
and Pi share the same set-theoretic carrier); the pushforward only
changes which norm/topology is recorded on the type. The `spec`
argument is unused in the body and serves only to enable
`spec.toEuclideanMeasure μ` dot-notation. -/
def toEuclideanMeasure
    (_spec : GibbsSpec Λ ℝ) (μ : Measure (SpinConfig Λ ℝ)) :
    Measure (EuclideanSpace ℝ Λ) :=
  μ.map (EuclideanSpace.equiv Λ ℝ).symm

omit [DecidableEq Λ] in
/-- The map `(EuclideanSpace.equiv Λ ℝ).symm : (Λ → ℝ) → EuclideanSpace ℝ Λ`
is measurable (it is continuous as a continuous linear equivalence,
and continuous maps between Borel spaces are measurable). -/
lemma measurable_euclideanEquiv_symm :
    Measurable ((EuclideanSpace.equiv Λ ℝ).symm :
      (Λ → ℝ) → EuclideanSpace ℝ Λ) :=
  (EuclideanSpace.equiv Λ ℝ).symm.continuous.measurable

/-- The pushforward of a probability measure is a probability measure. -/
instance isProbabilityMeasure_toEuclideanMeasure
    (spec : GibbsSpec Λ ℝ) (μ : Measure (SpinConfig Λ ℝ))
    [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (spec.toEuclideanMeasure μ) := by
  unfold toEuclideanMeasure
  exact μ.isProbabilityMeasure_map measurable_euclideanEquiv_symm.aemeasurable

/-- Explicit formula for the pushforward measure on a Borel set. -/
lemma toEuclideanMeasure_apply
    (spec : GibbsSpec Λ ℝ) (μ : Measure (SpinConfig Λ ℝ))
    {s : Set (EuclideanSpace ℝ Λ)} (hs : MeasurableSet s) :
    spec.toEuclideanMeasure μ s = μ ((EuclideanSpace.equiv Λ ℝ).symm ⁻¹' s) := by
  unfold toEuclideanMeasure
  rw [Measure.map_apply measurable_euclideanEquiv_symm hs]

end GibbsSpec

end
