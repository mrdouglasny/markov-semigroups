/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Single-site disintegration

Given a probability measure `μ` on `SpinConfig I S = I → S` and a site
`x : I`, produce the conditional measure `μ(· | σ(x) = a)` as a measurable
family of probability measures, and prove the disintegration identity

```
∫ σ, f σ ∂μ = ∫ a, (∫ σ, f σ ∂(condSingleSiteMeasure μ x a)) ∂(μ.map (· x))
```

This is the module `M1` of `Dobrushin/PLAN_B2.md`. It is a pure
measure-theoretic primitive — nothing Dobrushin-specific — intended to
be consumed by the iterated-DLR covariance bound (`M4`).

## Route

We use the explicit construction (Route B in the plan):

```
condSingleSiteMeasure μ x a :=
  (μ (eval_x ⁻¹' {a}))⁻¹ • μ.restrict (eval_x ⁻¹' {a})
```

with the convention that `0⁻¹ = 0`, so atoms of mass zero give the zero
measure (their `∫ f ∂(cond·)` therefore contributes `0` on the RHS and
is matched by the LHS since the corresponding fiber has measure `0`).

For `[Countable S] [MeasurableSingletonClass S]`, every singleton in
`S` is measurable, so the fibers `eval_x ⁻¹' {a}` are measurable and
`μ` decomposes as a countable sum of its restrictions to fibers:

```
μ = Measure.sum (fun a => μ.restrict (eval_x ⁻¹' {a}))
```

The disintegration identity then follows from `integral_sum_measure`,
`integral_smul_measure`, and `integral_countable` for the pushforward
on the countable space `S`.

## API

- `condSingleSiteMeasure` — the measure family `μ(· | σ(x) = a)`.
- `isProbabilityMeasure_condSingleSiteMeasure` — the rescaled measure
  is a probability measure whenever the atom has positive mass.
- `integral_condSingleSiteMeasure` — disintegration identity for `∫ f ∂μ`.

## References

- `MarkovSemigroups/Dobrushin/PLAN_B2.md`, section M1.
- Georgii (1988), *Gibbs Measures and Phase Transitions*, §1.
-/

import MarkovSemigroups.Dobrushin.Specification
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory Set ENNReal

noncomputable section

namespace SingleSiteDisintegration

variable {I : Type*} {S : Type*} [MeasurableSpace S]

/-- Evaluation of a spin configuration at site `x`. -/
def evalAt (x : I) : SpinConfig I S → S := fun σ => σ x

lemma measurable_evalAt (x : I) : Measurable (evalAt (S := S) (I := I) x) :=
  measurable_pi_apply x

/-- The fiber `{σ | σ x = a}` at site `x` with spin value `a`. -/
def fiber (x : I) (a : S) : Set (SpinConfig I S) := evalAt x ⁻¹' {a}

lemma measurableSet_fiber [MeasurableSingletonClass S] (x : I) (a : S) :
    MeasurableSet (fiber (I := I) (S := S) x a) :=
  (measurable_evalAt x) (measurableSet_singleton a)

omit [MeasurableSpace S] in
lemma iUnion_fiber (x : I) : (⋃ a : S, fiber (I := I) (S := S) x a) = Set.univ := by
  ext σ
  simp [fiber, evalAt]

omit [MeasurableSpace S] in
lemma pairwise_disjoint_fiber (x : I) :
    Pairwise (Function.onFun Disjoint
      (fun a : S => fiber (I := I) (S := S) x a)) := by
  intro a b hab
  rw [Function.onFun, Set.disjoint_iff]
  intro σ hσ
  rcases hσ with ⟨ha, hb⟩
  simp [fiber, evalAt, mem_preimage] at ha hb
  exact hab (ha.symm.trans hb)

/-- The single-site conditional measure `μ(· | σ(x) = a)`.

Defined as the restriction of `μ` to the fiber `{σ | σ x = a}`
rescaled by `(μ (fiber x a))⁻¹`. With the convention `0⁻¹ = 0` in
`ℝ≥0∞`, atoms of mass zero produce the zero measure (consistent
with the disintegration identity, as the zero-mass atom contributes
`0` to the RHS integral). -/
def condSingleSiteMeasure (μ : Measure (SpinConfig I S)) (x : I) (a : S) :
    Measure (SpinConfig I S) :=
  (μ (fiber x a))⁻¹ • μ.restrict (fiber x a)

/-- The conditional measure at site `x` given value `a` is a probability
measure whenever the fiber has positive finite mass. -/
lemma isProbabilityMeasure_condSingleSiteMeasure
    [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) (x : I) (a : S)
    (hpos : μ (fiber x a) ≠ 0) (hne_top : μ (fiber x a) ≠ ∞) :
    IsProbabilityMeasure (condSingleSiteMeasure μ x a) := by
  refine ⟨?_⟩
  simp only [condSingleSiteMeasure, Measure.smul_apply,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    smul_eq_mul]
  rw [ENNReal.inv_mul_cancel hpos hne_top]

/-- Decomposition of `μ` along the fibers of `evalAt x` as a `Measure.sum`. -/
lemma sum_restrict_fiber_eq [Countable S] [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) (x : I) :
    (Measure.sum fun a : S => μ.restrict (fiber (I := I) (S := S) x a)) = μ := by
  have hcov : (⋃ a : S, fiber (I := I) (S := S) x a) = Set.univ := iUnion_fiber x
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun a : S => fiber (I := I) (S := S) x a)) :=
    pairwise_disjoint_fiber x
  have hmeas : ∀ a : S, MeasurableSet (fiber (I := I) (S := S) x a) :=
    fun a => measurableSet_fiber x a
  have := Measure.restrict_iUnion (μ := μ) (s := fun a : S => fiber x a) hdisj hmeas
  rw [hcov, Measure.restrict_univ] at this
  exact this.symm

/-- Pushforward measure of `μ` under `evalAt x` applied to a singleton. -/
lemma map_evalAt_singleton [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) (x : I) (a : S) :
    (μ.map (evalAt x)) {a} = μ (fiber x a) := by
  rw [Measure.map_apply (measurable_evalAt x) (measurableSet_singleton a)]
  rfl

/-- Product of a finite nonzero ℝ≥0∞ value with its inverse, projected to `ℝ`, is `1`. -/
private lemma toReal_mul_toReal_inv {r : ℝ≥0∞} (hpos : r ≠ 0) (hne_top : r ≠ ∞) :
    r.toReal * (r⁻¹).toReal = 1 := by
  rw [ENNReal.toReal_inv]
  exact mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hpos, hne_top⟩)

/-- **Disintegration identity, tsum form.** For an integrable `f`, the
integral of `f` with respect to `μ` decomposes into a countable sum of
conditional expectations weighted by the single-site marginals
`μ(fiber x a) = (μ.map (evalAt x)) {a}`:

```
∫ σ, f σ ∂μ = ∑' a : S,
    (μ (fiber x a)).toReal • ∫ σ, f σ ∂(condSingleSiteMeasure μ x a)
```

Atoms with zero mass contribute `0` to the sum (using `0⁻¹ = 0`),
which matches the fact that `μ` assigns no mass to such fibers.

See `PLAN_B2.md` M1. -/
theorem tsum_integral_condSingleSiteMeasure
    [Countable S] [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) [IsFiniteMeasure μ]
    (x : I) {f : SpinConfig I S → ℝ} (hf : Integrable f μ) :
    ∫ σ, f σ ∂μ
      = ∑' a : S,
          (μ (fiber x a)).toReal • ∫ σ, f σ ∂(condSingleSiteMeasure μ x a) := by
  -- Rewrite LHS using the fiber decomposition of μ.
  have hsum := sum_restrict_fiber_eq (I := I) (S := S) μ x
  have hf' : Integrable f (Measure.sum (fun a : S => μ.restrict (fiber x a))) := by
    rw [hsum]; exact hf
  calc
    ∫ σ, f σ ∂μ
        = ∫ σ, f σ ∂(Measure.sum (fun a : S => μ.restrict (fiber x a))) := by rw [hsum]
    _ = ∑' a : S, ∫ σ, f σ ∂(μ.restrict (fiber x a)) := integral_sum_measure hf'
    _ = ∑' a : S,
          (μ (fiber x a)).toReal • ∫ σ, f σ ∂(condSingleSiteMeasure μ x a) := by
        apply tsum_congr
        intro a
        -- Case split on whether the fiber has positive mass.
        by_cases hmass : μ (fiber x a) = 0
        · -- Zero-mass fiber: both sides vanish.
          have hzero : μ.restrict (fiber x a) = 0 := by
            rw [Measure.restrict_eq_zero]; exact hmass
          rw [hzero]
          simp [condSingleSiteMeasure, hmass]
        · -- Positive-mass fiber: rescale back.
          have hne_top : μ (fiber x a) ≠ ∞ :=
            (measure_lt_top μ (fiber x a)).ne
          have : ∫ σ, f σ ∂(condSingleSiteMeasure μ x a)
                = ((μ (fiber x a))⁻¹).toReal
                    • ∫ σ, f σ ∂(μ.restrict (fiber x a)) := by
            simp [condSingleSiteMeasure, integral_smul_measure]
          rw [this]
          rw [smul_smul]
          rw [show (μ (fiber x a)).toReal * ((μ (fiber x a))⁻¹).toReal = 1 from
                toReal_mul_toReal_inv hmass hne_top]
          simp

/-- **Disintegration identity, integral form.** The single-site disintegration
identity expressed with an outer integral over the pushforward
`μ.map (evalAt x)` on the spin space `S`:

```
∫ σ, f σ ∂μ
  = ∫ a, (∫ σ, f σ ∂(condSingleSiteMeasure μ x a)) ∂(μ.map (evalAt x))
```

This is the form promised by `PLAN_B2.md` M1. Equivalence with the
tsum form `tsum_integral_condSingleSiteMeasure` is via Mathlib's
`integral_countable`.

The hypothesis `hg` requires the inner integral to be integrable
with respect to the pushforward; this holds automatically in the
usual applications (e.g. when `f` is bounded measurable). -/
theorem integral_condSingleSiteMeasure
    [Countable S] [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) [IsFiniteMeasure μ]
    (x : I) {f : SpinConfig I S → ℝ} (hf : Integrable f μ)
    (hg : Integrable (fun a : S => ∫ σ, f σ ∂(condSingleSiteMeasure μ x a))
        (μ.map (evalAt x))) :
    ∫ σ, f σ ∂μ
      = ∫ a, (∫ σ, f σ ∂(condSingleSiteMeasure μ x a)) ∂(μ.map (evalAt x)) := by
  rw [integral_countable hg]
  rw [tsum_integral_condSingleSiteMeasure μ x hf]
  apply tsum_congr
  intro a
  rw [measureReal_def, map_evalAt_singleton]

end SingleSiteDisintegration

end
