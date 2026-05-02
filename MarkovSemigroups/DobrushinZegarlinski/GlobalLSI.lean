/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Zegarlinski's Theorem: Local LSI + Weak Coupling ⇒ Global LSI

The main result of the Dobrushin–Zegarlinski layer for continuous
spin systems on `EuclideanSpace ℝ Λ`: if every single-site conditional
satisfies a log-Sobolev inequality with constant `c > 0` (uniformly in
the boundary), and the gradient interaction matrix `c · J` has column
sums uniformly bounded by some `α < 1`, then the global Gibbs measure
satisfies a log-Sobolev inequality with a constant `C > 0` that depends
only on `c` and `α` — *not* on the volume `|Λ|`.

The proof strategy is the standard *spatial sweeping* / martingale
decomposition of the entropy:

  Ent_μ(f²)  ≤  Σ_x  E_μ [ Ent_{μ_x(·|σ_∖x)}(f²) ]            (chain rule)
              ≤  Σ_x  E_μ [ (2/c) · ∫ ‖∂_x f‖² dμ_x(·|σ_∖x) ]   (local LSI)
              ≤  (2C/c) · ∫ Σ_x ‖∂_x f‖² dμ                    (Neumann)

where the bound at the last step uses the resolvent `(I - c · J)⁻¹`
with operator norm at most `1 / (1 - α)` from the abstract Neumann
series. This gives `C = c · (1 - α)`.

## Status

* `ZegarlinskiCondition` is fully defined; it is the Dobrushin-style
  weak-coupling hypothesis on `c · J`.
* The bridge to `AbstractInfluenceMatrix` is *stated* but its
  finiteness/sum-bookkeeping proof is left as `sorry` (pure
  `Finset.sum_erase` manipulation, no analytic content).
* The main theorem `global_lsi_of_zegarlinski` is *stated* with a
  single sorry placeholder for the entropy chain-rule decomposition;
  this is the only deep piece left, and it is the standard
  measure-theoretic content of BGL §5.7.

The API surface here is what `pphi2N` should consume.

## References

* Zegarlinski, *Lett. Math. Phys.* 20 (1990).
* Stroock and Zegarlinski, *Comm. Math. Phys.* 144 (1992), Thm. 0.1.
* Bakry, Gentil, Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, §5.7.
-/

import MarkovSemigroups.DobrushinZegarlinski.AbstractInfluence
import MarkovSemigroups.DobrushinZegarlinski.EntropyChainRule
import MarkovSemigroups.DobrushinZegarlinski.EuclideanTransport
import MarkovSemigroups.DobrushinZegarlinski.InteractionMatrix
import MarkovSemigroups.DobrushinZegarlinski.LocalLSI

noncomputable section

namespace MarkovSemigroups.DobrushinZegarlinski

open scoped BigOperators
open MeasureTheory

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Dobrushin–Zegarlinski weak coupling hypothesis.**

Given a potential `V` and a local-LSI constant `c > 0`, there exists
`α < 1` such that the (off-diagonal) interaction is small relative
to the local curvature:

* every column `(J_{·, y} / c)` summed over rows `x ≠ y` is bounded by α;
* every row    `(J_{x, ·} / c)` summed over cols `y ≠ x` is bounded by α.

By Schur's test on `ℓ²`, both bounds together imply the operator-norm
bound `‖J‖_op ≤ α · c`. The global LSI constant produced by
`zegarlinski_lsi_inequality` is `c · (1 - α)`; this matches the
Otto–Reznikoff (2007) formula `ρ_global = ρ - ‖W‖_op = c - α·c`.

We keep the column and row bounds as separate hypotheses (no Clairaut
symmetry imposed at the structure level), and gate the structure on
`ContDiff ℝ 2 V` so that the `interactionMatrix` is mathematically
meaningful (Clairaut-symmetric, finite). The smoothness witness is
preserved as a field for downstream theorem use.

The hypothesis `c_pos : 0 < c` is required for the division `J/c` to
make sense; for `c = 0` the LSI hypothesis is vacuous anyway. -/
structure ZegarlinskiCondition (V : EuclideanSpace ℝ Λ → ℝ) (c : ℝ) where
  α : ℝ
  α_nonneg : 0 ≤ α
  α_lt_one : α < 1
  c_pos : 0 < c
  /-- C² smoothness of the potential. Required for the
      `interactionMatrix` entries to be mathematically meaningful;
      see `gradInteractionMatrix` for discussion. -/
  hV : ContDiff ℝ 2 V
  /-- Column sum of `J/c` over rows `x ≠ y` is at most `α`. -/
  col_bound : ∀ y : Λ,
    ∑ x ∈ Finset.univ.erase y, interactionMatrix V x y / c ≤ α
  /-- Row sum of `J/c` over cols `y ≠ x` is at most `α`. -/
  row_bound : ∀ x : Λ,
    ∑ y ∈ Finset.univ.erase x, interactionMatrix V x y / c ≤ α

namespace ZegarlinskiCondition

variable {V : EuclideanSpace ℝ Λ → ℝ} {c : ℝ}

/-- Convert a Zegarlinski condition into the abstract-influence-matrix
data needed to apply the Neumann series.

The off-diagonal entries are `c · J_{xy}`; the diagonal is set to `0`
(the local restorative force lives in the LSI hypothesis on the
conditional at site `x`, not in the interaction matrix). With `Λ`
finite, summability is automatic; the column/row bound reductions
collapse `∑' x : Λ, (if x = y then 0 else f x) = ∑ x ∈ univ.erase y, f x`
via `Finset.sum_erase`. -/
def toAbstract (h : ZegarlinskiCondition V c) :
    AbstractInfluenceMatrix Λ where
  entry x y := if x = y then 0 else interactionMatrix V x y / c
  α := h.α
  α_nonneg := h.α_nonneg
  α_lt_one := h.α_lt_one
  entry_nonneg x y := by
    by_cases hxy : x = y
    · simp [hxy]
    · simp [hxy]
      exact div_nonneg (interactionMatrix_nonneg V x y) h.c_pos.le
  col_summable _ :=
    summable_of_ne_finset_zero (s := Finset.univ)
      (fun b hb => (hb (Finset.mem_univ b)).elim)
  col_bound y := by
    rw [tsum_eq_sum (s := Finset.univ)
      (fun b hb => (hb (Finset.mem_univ b)).elim)]
    rw [show (Finset.univ : Finset Λ) = insert y (Finset.univ.erase y) from
          (Finset.insert_erase (Finset.mem_univ y)).symm,
        Finset.sum_insert (Finset.notMem_erase y _),
        if_pos (rfl : y = y), zero_add]
    rw [Finset.sum_congr rfl
      (fun x hx => if_neg (Finset.ne_of_mem_erase hx))]
    exact h.col_bound y
  row_summable _ :=
    summable_of_ne_finset_zero (s := Finset.univ)
      (fun b hb => (hb (Finset.mem_univ b)).elim)
  row_bound x := by
    rw [tsum_eq_sum (s := Finset.univ)
      (fun b hb => (hb (Finset.mem_univ b)).elim)]
    rw [show (Finset.univ : Finset Λ) = insert x (Finset.univ.erase x) from
          (Finset.insert_erase (Finset.mem_univ x)).symm,
        Finset.sum_insert (Finset.notMem_erase x _),
        if_pos (rfl : x = x), zero_add]
    rw [Finset.sum_congr rfl
      (fun y hy => if_neg (Ne.symm (Finset.ne_of_mem_erase hy)))]
    exact h.row_bound x

end ZegarlinskiCondition

/-! ## Zegarlinski's Theorem -/

/-- **Witness that a Gibbs specification is generated by a potential.**

The single-site conditionals of `spec` coincide with the Boltzmann-
weight measures associated to `V`:

  (`spec.condDist {x} σ`).map (`τ ↦ τ x`)
    = `(1/Z(x, σ)) · e^{-V(σ extended with value a at x)} · da`

as a measure on `ℝ`, where `Z(x, σ)` is the local partition function
(`> 0`) and `da` is Lebesgue measure on `ℝ`. The extension uses
`Function.update σ x a : SpinConfig Λ ℝ` lifted through
`(EuclideanSpace.equiv Λ ℝ).symm` to evaluate `V`.

This Prop is the load-bearing link between `spec` (used in
`UniformLocalLSI` and `IsGibbsMeasure`) and `V` (used in
`ZegarlinskiCondition`). Without a substantive content, one could
pair a frozen-conditional spec with `V = 0` and derive false
covariance bounds; making the Boltzmann identity explicit makes such
pairings impossible. -/
class IsGibbsSpecificationFor (spec : GibbsSpec Λ ℝ)
    (V : EuclideanSpace ℝ Λ → ℝ) : Prop where
  /-- The Boltzmann-density identity. For every site `x` and every
      boundary configuration `σ`, the σ-x marginal of the spec's
      single-site conditional admits a density proportional to
      `e^{-V(extend σ x a)}` with respect to Lebesgue measure on
      the value coordinate `a : ℝ`. -/
  density_eq : ∀ (x : Λ) (σ : SpinConfig Λ ℝ),
    ∃ Z : ℝ, 0 < Z ∧
      (spec.condDist {x} σ).map (fun τ : SpinConfig Λ ℝ => τ x)
        = Measure.withDensity volume (fun a : ℝ =>
            ENNReal.ofReal ((1 / Z) *
              Real.exp (-V ((EuclideanSpace.equiv Λ ℝ).symm
                              (Function.update σ x a)))))

/-- **Zegarlinski's LSI inequality (textbook axiom).**

The functional inequality content of `global_lsi_of_zegarlinski`:
under

* a Gibbs specification generated by `V` (`IsGibbsSpecificationFor spec V`),
* uniform local LSI on each conditional with constant `c > 0`
  (`UniformLocalLSI spec c`),
* a Zegarlinski weak-coupling hypothesis (`ZegarlinskiCondition V c`)
  with `Σ J/c ≤ α < 1` row-and-column,

the Gibbs measure `μ` satisfies the LSI on the L²-Euclidean side:

  Ent_μ(f²) ≤ (2 / (c (1-α))) ∫ ‖∇f‖² dμ_eucl,

provided `f` is differentiable AND the integrals on both sides exist.

The `EntropyIntegrable` and `Integrable` hypotheses are required to
sidestep Lean's "integral of non-integrable function = 0" convention,
which would otherwise let the RHS evaluate to `0` while the LHS is
positive (false inequality from Lean's perspective).

Reference: Otto and Reznikoff, "A new criterion for the logarithmic
Sobolev inequality and two applications," *J. Funct. Anal.* 243 (2007),
Theorem 1; Zegarlinski, "The strong decay to equilibrium for the
stochastic dynamics of unbounded spin systems on a lattice,"
*Comm. Math. Phys.* 175 (1996); Bakry, Gentil, Ledoux, *Analysis and
Geometry of Markov Diffusion Operators*, Springer, 2014, Theorem 5.7.5.

(Note: Stroock–Zegarlinski 1992 is the *finite-spin / total-variation*
form of the same equivalence; for unbounded continuous spins the
Otto–Reznikoff and Zegarlinski 1996 references are the right
provenance.)

Strategy: the proof iterates the *proved* single-site decomposition
`entropy_decomposition_single_site` against the local LSI bound, with
cross-site cross-terms controlled by the resolvent of `(I - J/c)⁻¹`
via Schur's test on `J/c`'s row/col bounds. The `(I - J/c)⁻¹`
operator-norm bound `≤ 1/(1-α)` is supplied by
`AbstractInfluenceMatrix.neumann_series_row_bound` applied to
`h_weak.toAbstract`. Putting it together gives the final constant
`c · (1-α)` matching `ρ - ‖W‖_op = c - α·c` from Otto–Reznikoff.

(NOT VERIFIED — axiom statement stands until peer review.) -/
axiom zegarlinski_lsi_inequality
    {spec : GibbsSpec Λ ℝ} {V : EuclideanSpace ℝ Λ → ℝ} {c : ℝ}
    [hgen : IsGibbsSpecificationFor spec V]
    (h_local : UniformLocalLSI spec c)
    (h_weak : ZegarlinskiCondition V c)
    (μ : Measure (SpinConfig Λ ℝ)) [IsProbabilityMeasure μ]
    (h_gibbs : IsGibbsMeasure spec μ)
    (f : EuclideanSpace ℝ Λ → ℝ) (hf : Differentiable ℝ f)
    (hf_sq_int :
      Integrable (fun x => (f x) ^ 2) (spec.toEuclideanMeasure μ))
    (hf_log_int :
      Integrable (fun x => (f x) ^ 2 * Real.log ((f x) ^ 2))
        (spec.toEuclideanMeasure μ))
    (hgrad_int :
      Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2)
        (spec.toEuclideanMeasure μ)) :
    entropy (spec.toEuclideanMeasure μ) (fun x => (f x) ^ 2) ≤
      (2 / (c * (1 - h_weak.α))) *
        ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂(spec.toEuclideanMeasure μ)

/-- **Zegarlinski's Theorem.**

Under a Gibbs specification generated by `V` (`IsGibbsSpecificationFor`),
uniform local LSI (constant `c > 0`), and a Dobrushin-style weak-
coupling bound (`ZegarlinskiCondition V c` with row/col sums of
`J/c` ≤ α < 1), every Gibbs measure `μ` for the specification gives
rise to a *global* log-Sobolev inequality with constant `c · (1 - α)`,
which is volume-independent.

The positivity of the constant is proved directly. The functional
inequality is the textbook content `zegarlinski_lsi_inequality`
(Otto-Reznikoff 2007 / BGL §5.7.5).

This is the contract `pphi2N` is intended to consume. The LSI
conclusion is stated on the Euclidean pushforward
`spec.toEuclideanMeasure μ` (transport from `EuclideanTransport.lean`). -/
theorem global_lsi_of_zegarlinski
    {spec : GibbsSpec Λ ℝ} {V : EuclideanSpace ℝ Λ → ℝ} {c : ℝ}
    [IsGibbsSpecificationFor spec V]
    (h_local : UniformLocalLSI spec c)
    (h_weak : ZegarlinskiCondition V c)
    (μ : Measure (SpinConfig Λ ℝ)) [IsProbabilityMeasure μ]
    (h_gibbs : IsGibbsMeasure spec μ) :
    SatisfiesLSI (spec.toEuclideanMeasure μ) (c * (1 - h_weak.α)) := by
  refine ⟨?_, ?_⟩
  · -- Positivity: 0 < c · (1 - α). c > 0 from h_local; 1 - α > 0 from α < 1.
    have hc : 0 < c := h_local.c_pos
    have hα : 0 < 1 - h_weak.α := by linarith [h_weak.α_lt_one]
    exact mul_pos hc hα
  · -- The functional inequality is the textbook axiom (Otto-Reznikoff 2007).
    intro f hf hf_sq_int hf_log_int hgrad_int
    exact zegarlinski_lsi_inequality h_local h_weak μ h_gibbs f hf
      hf_sq_int hf_log_int hgrad_int

end MarkovSemigroups.DobrushinZegarlinski

end
