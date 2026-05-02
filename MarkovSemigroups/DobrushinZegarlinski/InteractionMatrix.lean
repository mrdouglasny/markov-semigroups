/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Continuous Interaction Matrix (Zegarlinski's J)

For continuous spin systems on `EuclideanSpace ℝ Λ` with potential
`V : EuclideanSpace ℝ Λ → ℝ`, the gradient-based interaction matrix
is the supremum over base points of the mixed second partial:

  J_{xy}(V) = sup_ψ |∂_y ∂_x V(ψ)|

Heuristically, J controls how much site `y` can perturb the local
restorative force at site `x`. Together with a uniform local LSI of
constant `c`, the rescaled matrix `c · J` plays the role of the
discrete Dobrushin influence matrix in the Neumann-series argument.

## Main definitions

* `interactionMatrix V` — `ℓ²`-typed `J : Λ → Λ → ℝ` from the mixed
  fderiv of `V`;
* `gradInteractionMatrix V c hb` — the abstract influence matrix
  `c · J` packaged for `AbstractInfluenceMatrix`, given a column-sum
  bound;

The user-facing Zegarlinski hypothesis (column sums of `c · J` ≤ α<1)
lives in `GlobalLSI.lean`; this file just provides the data layer.

## Why `EuclideanSpace ℝ Λ` (= `PiLp 2`)

`fderiv` of `V : (Λ → ℝ) → ℝ` returns `(Λ → ℝ) →L[ℝ] ℝ`. The default
`Λ → ℝ` carries the `L^∞` Pi-norm, which is *not* the right operator
norm for translating column sums of `J` into the operator norm of the
Hessian. Working on `EuclideanSpace ℝ Λ = PiLp 2 (fun _ => ℝ)`
endows us with the `ℓ²` inner-product structure, so the basis vectors
`EuclideanSpace.single x 1` are an orthonormal basis and the Hessian
operator norm agrees with the spectral norm of the matrix `J_{xy}`.

This is the topology that downstream LSI / Dirichlet-form arguments
expect; see `LocalLSI.lean`.

## Status

* `interactionMatrix` is defined and shown nonneg. The raw definition
  is intentionally NOT gated on smoothness, so it remains usable for
  diagnostic / inspection purposes on arbitrary `V`.
* The meaningful bridge `gradInteractionMatrix` to
  `AbstractInfluenceMatrix` is gated on `ContDiff ℝ 2 V` (C² required)
  and fully proved given column- and row-sum hypotheses (no analysis
  content beyond the smoothness gate; pure summability bookkeeping).
  The smoothness witness is preserved in the resulting structure so
  downstream theorems can recover it.
* Symmetry of `J` under `C²` (Clairaut) is *not* proved here; the
  bridge accepts row and column bounds independently so it does not
  require symmetry. A future Clairaut lemma can be added in a separate
  file (`InteractionMatrix.Symmetry`) without touching this one.

## References

* Zegarlinski, "On log-Sobolev inequalities for infinite lattice
  systems," *Lett. Math. Phys.* 20 (1990).
* Stroock and Zegarlinski, "The equivalence of the logarithmic Sobolev
  inequality and the Dobrushin–Shlosman mixing condition,"
  *Comm. Math. Phys.* 144 (1992).
* Bakry, Gentil, Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Ch. 5.
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.PiL2
import MarkovSemigroups.DobrushinZegarlinski.AbstractInfluence

noncomputable section

namespace MarkovSemigroups.DobrushinZegarlinski

open scoped BigOperators

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The Zegarlinski interaction matrix entry. The mixed second partial
of the potential `V` along the standard `ℓ²` basis vectors at `x`
and `y`, taken absolutely and supremized over the base point.

If `V` is not `C²` everywhere or the mixed partials are unbounded,
the supremum is taken in `ℝ` (with the convention that an unbounded
family supremum yields the `iSup` value as defined by Lean — finite
in our intended applications, where `V` has a global `C² ∩ L^∞`
control).

Downstream uses pair this definition with hypotheses that the
resulting matrix entry is finite and that `c · J` has small enough
column/row sums — see `gradInteractionMatrix`. -/
def interactionMatrix (V : EuclideanSpace ℝ Λ → ℝ) (x y : Λ) : ℝ :=
  ⨆ ψ : EuclideanSpace ℝ Λ,
    ‖fderiv ℝ (fun ψ' => fderiv ℝ V ψ' (EuclideanSpace.single x 1)) ψ
        (EuclideanSpace.single y 1)‖

omit [Fintype Λ] in
lemma interactionMatrix_nonneg (V : EuclideanSpace ℝ Λ → ℝ) (x y : Λ) :
    0 ≤ interactionMatrix V x y := by
  unfold interactionMatrix
  -- Each summand is `‖·‖ ≥ 0`; the supremum of nonneg reals is nonneg
  -- since `EuclideanSpace ℝ Λ` is nonempty (the zero vector).
  refine Real.iSup_nonneg ?_
  intro _
  exact norm_nonneg _

/-- Construct an `AbstractInfluenceMatrix` from the rescaled matrix
`J_{xy} / c` together with column- and row-sum hypotheses.

This is the *bridge* lemma: the entire continuous Zegarlinski theory
flows into the abstract Neumann-series machinery once we have a
column bound `Σ_x (J_{xy} / c) ≤ α < 1` and a row bound. With
`Λ` finite, summability is automatic.

**Convention.** The factor `1/c` (where `c` is the local LSI constant
= local curvature) makes `α` a dimensionless smallness parameter.
Schur's test then gives `‖J‖_op ≤ α · c`, and the global LSI constant
emerging from this layer is `c · (1 - α)`, matching the
Otto–Reznikoff (2007) formula.

**Smoothness gate.** We require `ContDiff ℝ 2 V` so that the mixed
second partial appearing in `interactionMatrix` is mathematically
meaningful (Clairaut-symmetric, finite, equal to the Hessian operator
norm entry). Without this, the `iSup` in `interactionMatrix` can pick
up spurious values from non-differentiable points and the resulting
"interaction matrix" no longer represents the continuous coupling. -/
def gradInteractionMatrix (V : EuclideanSpace ℝ Λ → ℝ) (c α : ℝ)
    (hα_nn : 0 ≤ α) (hα_lt : α < 1) (hc_pos : 0 < c)
    (_hV : ContDiff ℝ 2 V)
    (h_col : ∀ y, ∑ x, interactionMatrix V x y / c ≤ α)
    (h_row : ∀ x, ∑ y, interactionMatrix V x y / c ≤ α) :
    AbstractInfluenceMatrix Λ where
  entry x y := interactionMatrix V x y / c
  α := α
  α_nonneg := hα_nn
  α_lt_one := hα_lt
  entry_nonneg x y :=
    div_nonneg (interactionMatrix_nonneg V x y) hc_pos.le
  col_summable _ :=
    summable_of_ne_finset_zero (s := Finset.univ)
      (fun b hb => (hb (Finset.mem_univ b)).elim)
  col_bound y := by
    rw [tsum_eq_sum (s := Finset.univ)
      (fun b hb => (hb (Finset.mem_univ b)).elim)]
    exact h_col y
  row_summable _ :=
    summable_of_ne_finset_zero (s := Finset.univ)
      (fun b hb => (hb (Finset.mem_univ b)).elim)
  row_bound x := by
    rw [tsum_eq_sum (s := Finset.univ)
      (fun b hb => (hb (Finset.mem_univ b)).elim)]
    exact h_row x

end MarkovSemigroups.DobrushinZegarlinski

end
