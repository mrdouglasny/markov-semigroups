/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dobrushin Covariance Bound — Multi-site-local observables

Generalizes `covariance_bound_gibbs` (in `CondTVBridge.lean`) from
single-site-local observables to observables depending on a finite
*neighborhood* `N_f : Finset I`.

## Main content

1. **Multi-site conditional measure.** `condFiniteSupportMeasure μ N_f a`
   conditions `μ` on the event `σ|_{N_f} = a|_{N_f}`.
2. **Multi-site fibers.** `multiFiber N_f a = {σ | ∀ w ∈ N_f, σ w = a w}`
   and the basic measurability / disjointness / decomposition lemmas.
3. **DLR preservation at z ∉ N_f.** The conditional measure satisfies the
   DLR equation at `{z}` for every `z ∉ N_f`.
4. **Multi-source Neumann iteration.** Abstracts
   `abstract_neumann_iteration` from `CondTVBridge.lean` to a finite
   source *set* rather than a single source point.
5. **Marginal TV bound.** The `y`-marginal TV distance between
   `condFiniteSupportMeasure μ N_f a` and `μ` is bounded by
   `∑ x ∈ N_f, neumannSeriesCoeff γ y x`.
6. **Multi-site-conditioning single-site-g condTV bound.**
   `condTV_bound_multisite_y`: for a Gibbs measure `μ` and an observable
   `g` single-site-local at `y` bounded by `Bg`, the conditional-expectation
   difference at multi-site fiber `(N_f, a)` is bounded by
   `2 · Bg · ∑ x ∈ N_f, neumannSeriesCoeff γ y x`. This is the key bridge
   for multi-site applications: it extends the single-site `condTV_bound`
   to arbitrary finite conditioning supports. Iterating `condTV_bound_multisite_y`
   over a single-site-varying `y` and summing over `y ∈ N_g` suffices for
   lgt's Wilson plaquette use case.
7. **Textbook wiring.** A wrapper specializing the Neumann coefficient to the
   textbook `α^{d(x,y)}/(1−α)` form under a nearest-neighbor distance.

## Strategy

Follows the user-supplied sketch (PLAN_B2 M5+):
- Step 1 (condFiniteSupportMeasure): rescale `μ.restrict` to the
  multi-fiber.
- Step 2 (DLR at z ∉ N_f): proper preservation argument, directly
  adapts the single-site proof in `CondTVBridge.lean`.
- Step 3 (axiom invocation): `dobrushin_iterated_coupling_exists` is
  invoked with `T := (↑N_f)ᶜ` (complement of the conditioned support).
- Step 4 (multi-source Neumann iteration): `abstract_neumann_iteration`
  generalized to a finite source set, producing
  `δ y ≤ ∑ x ∈ N_f, neumannSeriesCoeff γ y x`.
- Step 5 (bridge): `local_integral_sub_le_marginalTvDist` combined with the
  marginal-TV bound yields `condTV_bound_multisite_y`.

## Remaining work (future extension)

A full multi-site-local `f` and multi-site-local `g` covariance bound
can be derived by:
(a) Adding a multi-site disintegration identity for `∫ f dμ` (analog
    of `tsum_integral_condSingleSiteMeasure` but over the N_f-marginal);
(b) Feeding `condTV_bound_multisite_y` as the bridge into a multi-site
    version of `covariance_bound_via_bridge`.
Both steps are mechanical: (a) is a direct finite-fiber generalization
of the existing single-site disintegration (the multi-site fiber system
is a partition indexed by `(N_f → S)`, countable when `S` is), and (b)
repeats the `covariance_bound_via_bridge` calculation with `(N_f → S)`-
indexed fibers. We omit it here in order to keep the current file
self-contained and fully-proved with zero sorries.

## References

- Georgii (1988), *Gibbs Measures and Phase Transitions*, §8
- Dobrushin (1968), uniqueness via influence matrix
-/

import MarkovSemigroups.Dobrushin.CondTVBridge

open MeasureTheory SingleSiteDisintegration Topology Filter Set

noncomputable section

namespace CovarianceBoundMultisite

variable {I : Type*} [DecidableEq I] {S : Type*} [MeasurableSpace S]

/-! ## Multi-site fibers -/

/-- The multi-site fiber `{σ | ∀ w ∈ N_f, σ w = a w}`. -/
def multiFiber (N_f : Finset I) (a : I → S) : Set (SpinConfig I S) :=
  {σ | ∀ w ∈ N_f, σ w = a w}

omit [MeasurableSpace S] in
lemma mem_multiFiber {N_f : Finset I} {a : I → S} {σ : SpinConfig I S} :
    σ ∈ multiFiber N_f a ↔ ∀ w ∈ N_f, σ w = a w := Iff.rfl

omit [MeasurableSpace S] in
/-- The multi-fiber is an intersection of single-site fibers over `N_f`. -/
lemma multiFiber_eq_iInter (N_f : Finset I) (a : I → S) :
    multiFiber (I := I) (S := S) N_f a =
      ⋂ w ∈ (N_f : Set I), fiber w (a w) := by
  ext σ
  simp only [multiFiber, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_coe,
    fiber, evalAt, Set.mem_preimage, Set.mem_singleton_iff]

/-- The multi-fiber is measurable when singletons in `S` are measurable. -/
lemma measurableSet_multiFiber [MeasurableSingletonClass S]
    (N_f : Finset I) (a : I → S) :
    MeasurableSet (multiFiber (I := I) (S := S) N_f a) := by
  rw [multiFiber_eq_iInter]
  refine MeasurableSet.biInter (N_f.countable_toSet) ?_
  intro w _; exact measurableSet_fiber w (a w)

/-! ## The multi-site conditional measure -/

/-- The conditional measure `μ(· | σ|_{N_f} = a|_{N_f})`.

Defined as the restriction of `μ` to the multi-fiber, rescaled by the
inverse of its mass. With the convention `0⁻¹ = 0` in `ℝ≥0∞`,
zero-mass fibers produce the zero measure. -/
def condFiniteSupportMeasure (μ : Measure (SpinConfig I S))
    (N_f : Finset I) (a : I → S) : Measure (SpinConfig I S) :=
  (μ (multiFiber N_f a))⁻¹ • μ.restrict (multiFiber N_f a)

/-- The conditional measure is a probability measure when the multi-fiber
has positive finite mass. -/
lemma isProbabilityMeasure_condFiniteSupportMeasure
    [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) (N_f : Finset I) (a : I → S)
    (hpos : μ (multiFiber N_f a) ≠ 0)
    (hne_top : μ (multiFiber N_f a) ≠ ⊤) :
    IsProbabilityMeasure (condFiniteSupportMeasure μ N_f a) := by
  refine ⟨?_⟩
  simp only [condFiniteSupportMeasure, Measure.smul_apply,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    smul_eq_mul]
  rw [ENNReal.inv_mul_cancel hpos hne_top]

/-- On the conditional measure, the event `σ ∈ multiFiber` holds a.e. -/
lemma ae_mem_multiFiber_condFiniteSupport
    [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) (N_f : Finset I) (a : I → S) :
    ∀ᵐ σ ∂(condFiniteSupportMeasure μ N_f a), σ ∈ multiFiber N_f a := by
  suffices h : condFiniteSupportMeasure μ N_f a (multiFiber N_f a)ᶜ = 0 from h
  simp only [condFiniteSupportMeasure, Measure.smul_apply, smul_eq_mul]
  have h0 : μ.restrict (multiFiber N_f a) (multiFiber N_f a)ᶜ = 0 := by
    rw [Measure.restrict_apply' (measurableSet_multiFiber N_f a)]
    simp
  rw [h0, mul_zero]

/-- If f is N_f-local, then f σ = f σ₀ a.e. under
`condFiniteSupportMeasure μ N_f a` for any σ₀ in the fiber. -/
lemma local_fn_ae_const_multisite
    [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) (N_f : Finset I) (a : I → S)
    (f : SpinConfig I S → ℝ)
    (hf_local : ∀ σ τ : SpinConfig I S,
      (∀ w ∈ N_f, σ w = τ w) → f σ = f τ)
    (σ₀ : SpinConfig I S) (hσ₀ : ∀ w ∈ N_f, σ₀ w = a w) :
    ∀ᵐ σ ∂(condFiniteSupportMeasure μ N_f a), f σ = f σ₀ := by
  filter_upwards [ae_mem_multiFiber_condFiniteSupport μ N_f a] with σ hσ
  apply hf_local
  intro w hw
  rw [hσ w hw, (hσ₀ w hw).symm]

/-! ## DLR preservation at z ∉ N_f -/

/-- γ.condDist {z} σ puts full mass on `multiFiber N_f a` when σ is in the
fiber and `z ∉ N_f`. -/
lemma condDist_measure_multiFiber_eq_one [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z : I) (N_f : Finset I) (hz : z ∉ N_f)
    (σ : SpinConfig I S) (a : I → S) (hσ : ∀ w ∈ N_f, σ w = a w) :
    γ.condDist {z} σ (multiFiber N_f a) = 1 := by
  have hproper := γ.proper {z} σ
  have hsub : {τ : SpinConfig I S | ∀ i, i ∉ ({z} : Finset I) → τ i = σ i} ⊆
      multiFiber N_f a := by
    intro τ hτ
    show ∀ w ∈ N_f, τ w = a w
    intro w hw
    have hwz : w ≠ z := by
      intro hwz'; subst hwz'; exact hz hw
    have : τ w = σ w := hτ w (by simp [Finset.mem_singleton, hwz])
    rw [this, hσ w hw]
  have h1 := measure_mono (μ := γ.condDist {z} σ) hsub
  rw [hproper] at h1
  exact le_antisymm (prob_le_one (μ := γ.condDist {z} σ)
    (s := multiFiber N_f a)) h1

/-- Complement of the multi-fiber has zero γ.condDist mass when σ is in
the fiber and `z ∉ N_f`. -/
lemma condDist_multiFiber_compl_eq_zero [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z : I) (N_f : Finset I) (hz : z ∉ N_f)
    (σ : SpinConfig I S) (a : I → S) (hσ : ∀ w ∈ N_f, σ w = a w) :
    γ.condDist {z} σ (multiFiber N_f a)ᶜ = 0 := by
  have h_full := condDist_measure_multiFiber_eq_one γ z N_f hz σ a hσ
  have hfin : γ.condDist {z} σ (multiFiber N_f a) ≠ ⊤ := by
    rw [h_full]; exact ENNReal.one_ne_top
  rw [measure_compl (measurableSet_multiFiber N_f a) hfin,
      h_full, (γ.isProb {z} σ).measure_univ, tsub_self]

/-- `γ.condDist {z} σ (multiFiber N_f a) = 0` when σ is NOT in the fiber
and `z ∉ N_f`. -/
lemma condDist_multiFiber_eq_zero [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z : I) (N_f : Finset I) (hz : z ∉ N_f)
    (σ : SpinConfig I S) (a : I → S)
    (hσ : ¬ (∀ w ∈ N_f, σ w = a w)) :
    γ.condDist {z} σ (multiFiber N_f a) = 0 := by
  push_neg at hσ
  obtain ⟨w, hwN, hne⟩ := hσ
  have hwz : w ≠ z := by
    intro hwz'; subst hwz'; exact hz hwN
  have h_fib_full : γ.condDist {z} σ (fiber w (σ w)) = 1 :=
    condDist_measure_fiber_eq_one γ z w hwz.symm σ (σ w) rfl
  have h_fib_compl :
      γ.condDist {z} σ (fiber w (σ w))ᶜ = 0 :=
    condDist_fiber_compl_eq_zero γ z w hwz.symm σ (σ w) rfl
  have hsub : multiFiber N_f a ⊆ (fiber w (σ w))ᶜ := by
    intro τ hτ
    show τ ∉ fiber w (σ w)
    intro hτ'
    have h1 : τ w = a w := hτ w hwN
    simp only [fiber, evalAt, Set.mem_preimage, Set.mem_singleton_iff] at hτ'
    rw [hτ'] at h1
    exact hne h1
  exact le_antisymm (measure_mono hsub |>.trans h_fib_compl.le) (zero_le _)

/-- When `z ∉ N_f` and σ is in the multi-fiber:
`γ.condDist {z} σ (A ∩ multiFiber N_f a) = γ.condDist {z} σ A`. -/
lemma condDist_inter_multiFiber_eq [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z : I) (N_f : Finset I) (hz : z ∉ N_f)
    (σ : SpinConfig I S) (a : I → S) (hσ : ∀ w ∈ N_f, σ w = a w)
    (A : Set (SpinConfig I S)) (hA : MeasurableSet A) :
    γ.condDist {z} σ (A ∩ multiFiber N_f a) = γ.condDist {z} σ A := by
  have h_split : γ.condDist {z} σ A =
      γ.condDist {z} σ (A ∩ multiFiber N_f a) +
        γ.condDist {z} σ (A ∩ (multiFiber N_f a)ᶜ) := by
    have hdisj : Disjoint (A ∩ multiFiber N_f a) (A ∩ (multiFiber N_f a)ᶜ) :=
      Set.disjoint_of_subset Set.inter_subset_right Set.inter_subset_right
        disjoint_compl_right
    have hmeas : MeasurableSet (A ∩ (multiFiber N_f a)ᶜ) :=
      hA.inter (measurableSet_multiFiber N_f a).compl
    have hunion : (A ∩ multiFiber N_f a) ∪ (A ∩ (multiFiber N_f a)ᶜ) = A := by
      ext τ; constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro hτ
        by_cases h' : τ ∈ multiFiber N_f a
        · exact Or.inl ⟨hτ, h'⟩
        · exact Or.inr ⟨hτ, h'⟩
    conv_lhs => rw [← hunion]
    exact measure_union hdisj hmeas
  have h_zero : γ.condDist {z} σ (A ∩ (multiFiber N_f a)ᶜ) = 0 :=
    le_antisymm (measure_mono Set.inter_subset_right |>.trans
      (condDist_multiFiber_compl_eq_zero γ z N_f hz σ a hσ).le) (zero_le _)
  rw [h_zero, add_zero] at h_split
  exact h_split.symm

/-- When `z ∉ N_f` and σ is NOT in the multi-fiber, then
`γ.condDist {z} σ (A ∩ multiFiber N_f a) = 0`. -/
lemma condDist_inter_multiFiber_eq_zero [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z : I) (N_f : Finset I) (hz : z ∉ N_f)
    (σ : SpinConfig I S) (a : I → S) (hσ : ¬ (∀ w ∈ N_f, σ w = a w))
    (A : Set (SpinConfig I S)) :
    γ.condDist {z} σ (A ∩ multiFiber N_f a) = 0 :=
  le_antisymm (measure_mono Set.inter_subset_right |>.trans
    (condDist_multiFiber_eq_zero γ z N_f hz σ a hσ).le) (zero_le _)

/-- **DLR for `condFiniteSupportMeasure` at every z ∉ N_f.**

If μ is a Gibbs measure for γ, then `condFiniteSupportMeasure μ N_f a`
satisfies the DLR equation at singleton `{z}` for every `z ∉ N_f`. -/
lemma condFiniteSupportMeasure_dlr_at_site
    [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (N_f : Finset I) (a : I → S) (hpos : μ (multiFiber N_f a) ≠ 0)
    (z : I) (hz : z ∉ N_f)
    (A : Set (SpinConfig I S)) (hA : MeasurableSet A) :
    (condFiniteSupportMeasure μ N_f a A).toReal =
    ∫ σ, (γ.condDist {z} σ A).toReal ∂(condFiniteSupportMeasure μ N_f a) := by
  have hfib := measurableSet_multiFiber (I := I) (S := S) N_f a
  have hAfib : MeasurableSet (A ∩ multiFiber N_f a) := hA.inter hfib
  have dlr_mu := hμ.dlr {z} (A ∩ multiFiber N_f a) hAfib
  set h : SpinConfig I S → ℝ := fun σ => (γ.condDist {z} σ A).toReal with hh_def
  set h_int : SpinConfig I S → ℝ :=
    fun σ => (γ.condDist {z} σ (A ∩ multiFiber N_f a)).toReal with hh_int_def
  have h_agree : ∀ σ, σ ∈ multiFiber N_f a → h_int σ = h σ := by
    intro σ hσ
    have hσ' : ∀ w ∈ N_f, σ w = a w := hσ
    show (γ.condDist {z} σ (A ∩ multiFiber N_f a)).toReal =
        (γ.condDist {z} σ A).toReal
    rw [condDist_inter_multiFiber_eq γ z N_f hz σ a hσ' A hA]
  have h_zero_off : ∀ σ, σ ∉ multiFiber N_f a → h_int σ = 0 := by
    intro σ hσ
    have hσ' : ¬ (∀ w ∈ N_f, σ w = a w) := hσ
    show (γ.condDist {z} σ (A ∩ multiFiber N_f a)).toReal = 0
    rw [condDist_inter_multiFiber_eq_zero γ z N_f hz σ a hσ' A]
    simp
  have h_int_eq : ∫ σ, h_int σ ∂μ = ∫ σ in multiFiber N_f a, h σ ∂μ := by
    rw [← integral_indicator hfib]
    apply integral_congr_ae
    filter_upwards with σ
    by_cases hσ : σ ∈ multiFiber N_f a
    · rw [h_agree σ hσ, Set.indicator_of_mem hσ]
    · rw [h_zero_off σ hσ, Set.indicator_of_notMem hσ]
  have hkey : (μ (A ∩ multiFiber N_f a)).toReal =
      ∫ σ in multiFiber N_f a, h σ ∂μ := by
    rw [dlr_mu]; exact h_int_eq
  have hLHS : (condFiniteSupportMeasure μ N_f a A).toReal =
      ((μ (multiFiber N_f a))⁻¹).toReal * (μ (A ∩ multiFiber N_f a)).toReal := by
    simp only [condFiniteSupportMeasure, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hA, ENNReal.toReal_mul,
      Set.inter_comm A (multiFiber N_f a)]
  have hRHS : ∫ σ, h σ ∂(condFiniteSupportMeasure μ N_f a) =
      ((μ (multiFiber N_f a))⁻¹).toReal *
        ∫ σ in multiFiber N_f a, h σ ∂μ := by
    simp only [condFiniteSupportMeasure, integral_smul_measure, smul_eq_mul]
  rw [hLHS, hRHS, hkey]

/-! ## Abstract multi-source Neumann iteration

The single-source version in `CondTVBridge.lean` (`abstract_neumann_iteration`)
produces `δ y ≤ neumannSeriesCoeff γ y x` assuming the self-consistency
inequality holds at every `z ≠ x`. We need the same conclusion but with
the exceptional set being a *finite set* `N_f` rather than a single point:
output `δ y ≤ ∑ x ∈ N_f, neumannSeriesCoeff γ y x`.

The proof is a straightforward generalization of the single-source one.
The key change is that the "zeroed" vector `δ' w := if w ∈ N_f then 0 else δ w`
picks up, in the self-consistency inequality at a contracting `z ∉ N_f`,
a boundary term `∑ x ∈ N_f, C(z, x)` (rather than the single term `C(z, x)`
in the single-source case). All induction identities, Fubini swaps, and
tendsto arguments carry over verbatim with the finite-sum boundary term. -/

set_option maxHeartbeats 800000 in
/-- **Multi-source Neumann iteration.** A bounded vector satisfying the
self-consistency inequality at every `z ∉ N_f` is bounded by the sum
of Neumann-series coefficients indexed over `N_f`. -/
lemma abstract_neumann_iteration_finset
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (N_f : Finset I)
    (δ : I → ℝ) (hδ_nn : ∀ w, 0 ≤ δ w) (hδ_le_one : ∀ w, δ w ≤ 1)
    (hcontract : ∀ z, z ∉ N_f →
      δ z ≤ ∑' w, influenceCoeff γ z w * δ w)
    (y : I) :
    δ y ≤ ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by
  classical
  set δ' : I → ℝ := fun w => if w ∈ N_f then 0 else δ w with hδ'_def
  have hδ'_nn : ∀ w, 0 ≤ δ' w := fun w => by
    by_cases hw : w ∈ N_f
    · simp [δ', hw]
    · simp [δ', hw]; exact hδ_nn w
  have hδ'_le_one : ∀ w, δ' w ≤ 1 := fun w => by
    by_cases hw : w ∈ N_f
    · simp [δ', hw]
    · simp [δ', hw]; exact hδ_le_one w
  have hδ_le_δ'_indicator : ∀ w,
      δ w ≤ δ' w + (if w ∈ N_f then 1 else 0) := fun w => by
    by_cases hw : w ∈ N_f
    · simp [δ', hw]; exact hδ_le_one w
    · simp [δ', hw]
  -- ∑' w, C(z,w) * (if w ∈ N_f then 1 else 0) = ∑ x ∈ N_f, C(z, x)
  have h_ind_tsum : ∀ z : I,
      ∑' w : I, influenceCoeff γ z w * (if w ∈ N_f then (1:ℝ) else 0)
        = ∑ x ∈ N_f, influenceCoeff γ z x := by
    intro z
    have heq : (fun w : I => influenceCoeff γ z w *
        (if w ∈ N_f then (1:ℝ) else 0)) =
      fun w => if w ∈ N_f then influenceCoeff γ z w else 0 := by
      funext w; by_cases hw : w ∈ N_f <;> simp [hw]
    rw [heq]
    rw [tsum_eq_sum (s := N_f)
          (f := fun w => if w ∈ N_f then influenceCoeff γ z w else 0)]
    · apply Finset.sum_congr rfl
      intro x hx; simp [hx]
    · intro w hw; simp [hw]
  -- Extended self-consistency at every z ∉ N_f.
  have hcontract' : ∀ z, z ∉ N_f →
      δ z ≤ (∑ x ∈ N_f, influenceCoeff γ z x) +
        ∑' w, influenceCoeff γ z w * δ' w := by
    intro z hzN
    have h1 : Summable (fun w => influenceCoeff γ z w * δ w) :=
      Summable.of_nonneg_of_le
        (fun w => mul_nonneg (influenceCoeff_nonneg γ z w) (hδ_nn w))
        (fun w => by
          calc influenceCoeff γ z w * δ w
              ≤ influenceCoeff γ z w * 1 :=
                mul_le_mul_of_nonneg_left (hδ_le_one w)
                  (influenceCoeff_nonneg γ z w)
            _ = influenceCoeff γ z w := mul_one _)
        (hD.row_summable z)
    have h2 : Summable (fun w => influenceCoeff γ z w * δ' w) :=
      Summable.of_nonneg_of_le
        (fun w => mul_nonneg (influenceCoeff_nonneg γ z w) (hδ'_nn w))
        (fun w => by
          calc influenceCoeff γ z w * δ' w
              ≤ influenceCoeff γ z w * 1 :=
                mul_le_mul_of_nonneg_left (hδ'_le_one w)
                  (influenceCoeff_nonneg γ z w)
            _ = influenceCoeff γ z w := mul_one _)
        (hD.row_summable z)
    have h_ind_summ : Summable (fun w : I =>
        influenceCoeff γ z w * (if w ∈ N_f then (1:ℝ) else 0)) := by
      refine Summable.of_nonneg_of_le
        (fun w => mul_nonneg (influenceCoeff_nonneg γ z w)
          (by split_ifs <;> linarith))
        (fun w => ?_) (hD.row_summable z)
      by_cases hw : w ∈ N_f
      · simp [hw]
      · simp [hw]; exact influenceCoeff_nonneg γ z w
    calc δ z
        ≤ ∑' w, influenceCoeff γ z w * δ w := hcontract z hzN
      _ ≤ ∑' w, influenceCoeff γ z w *
            (δ' w + (if w ∈ N_f then 1 else 0)) := by
          refine h1.tsum_le_tsum
            (fun w => mul_le_mul_of_nonneg_left (hδ_le_δ'_indicator w)
              (influenceCoeff_nonneg γ z w)) ?_
          refine Summable.of_nonneg_of_le
            (fun w => mul_nonneg (influenceCoeff_nonneg γ z w)
              (add_nonneg (hδ'_nn w) (by split_ifs <;> linarith)))
            (fun w => ?_) (hD.row_summable z)
          have hd' : δ' w + (if w ∈ N_f then (1:ℝ) else 0) ≤ 1 := by
            by_cases hw : w ∈ N_f
            · simp [δ', hw]
            · simp [δ', hw]; exact hδ_le_one w
          calc influenceCoeff γ z w *
                (δ' w + (if w ∈ N_f then 1 else 0))
              ≤ influenceCoeff γ z w * 1 :=
                mul_le_mul_of_nonneg_left hd'
                  (influenceCoeff_nonneg γ z w)
            _ = influenceCoeff γ z w := mul_one _
      _ = ∑' w, (influenceCoeff γ z w * δ' w +
            influenceCoeff γ z w * (if w ∈ N_f then 1 else 0)) := by
          congr 1; funext w; ring
      _ = (∑' w, influenceCoeff γ z w * δ' w) +
            ∑' w, influenceCoeff γ z w * (if w ∈ N_f then 1 else 0) :=
          Summable.tsum_add h2 h_ind_summ
      _ = (∑' w, influenceCoeff γ z w * δ' w) +
            ∑ x ∈ N_f, influenceCoeff γ z x := by rw [h_ind_tsum z]
      _ = (∑ x ∈ N_f, influenceCoeff γ z x) +
            ∑' w, influenceCoeff γ z w * δ' w := by ring
  have hstep : ∀ w : I,
      δ' w ≤ (∑ x ∈ N_f, influenceCoeff γ w x) +
        ∑' z, influenceCoeff γ w z * δ' z := by
    intro w
    by_cases hw : w ∈ N_f
    · have hδ'w : δ' w = 0 := by simp [δ', hw]
      rw [hδ'w]
      exact add_nonneg
        (Finset.sum_nonneg (fun x _ => influenceCoeff_nonneg γ w x))
        (tsum_nonneg (fun z =>
          mul_nonneg (influenceCoeff_nonneg γ w z) (hδ'_nn z)))
    · have hδ'w : δ' w = δ w := by simp [δ', hw]
      rw [hδ'w]; exact hcontract' w hw
  -- Auxiliary summabilities
  have h_Cw_δ'_summ : ∀ w, Summable (fun z => influenceCoeff γ w z * δ' z) :=
    fun w => Summable.of_nonneg_of_le
      (fun z => mul_nonneg (influenceCoeff_nonneg γ w z) (hδ'_nn z))
      (fun z => by
        calc influenceCoeff γ w z * δ' z
            ≤ influenceCoeff γ w z * 1 :=
              mul_le_mul_of_nonneg_left (hδ'_le_one z)
                (influenceCoeff_nonneg γ w z)
          _ = influenceCoeff γ w z := mul_one _)
      (hD.row_summable w)
  have h_Cw_δ'_bd : ∀ w, ∑' z, influenceCoeff γ w z * δ' z ≤ hD.α := by
    intro w
    calc ∑' z, influenceCoeff γ w z * δ' z
        ≤ ∑' z, influenceCoeff γ w z * 1 :=
          Summable.tsum_le_tsum
            (fun z => mul_le_mul_of_nonneg_left (hδ'_le_one z)
              (influenceCoeff_nonneg γ w z))
            (h_Cw_δ'_summ w)
            ((hD.row_summable w).congr (fun z => (mul_one _).symm))
      _ = ∑' z, influenceCoeff γ w z := by
          congr 1; funext z; exact mul_one _
      _ ≤ hD.α := hD.row_bound w
  -- Induction.
  have h_ind : ∀ N : ℕ,
      δ y ≤ (∑ k ∈ Finset.range (N + 1), ∑ x ∈ N_f,
          iterateInfluence γ k y x) +
        ∑' w, iterateInfluence γ N y w * δ' w := by
    intro N
    induction N with
    | zero =>
      have h_tsum_zero :
          ∑' w, iterateInfluence γ 0 y w * δ' w = δ' y := by
        rw [tsum_eq_single y]
        · simp [iterateInfluence_zero]
        · intro w hw; simp [iterateInfluence_zero, Ne.symm hw]
      have h_sum_zero :
          ∑ k ∈ Finset.range 1, ∑ x ∈ N_f, iterateInfluence γ k y x
            = ∑ x ∈ N_f, iterateInfluence γ 0 y x := by simp
      rw [h_sum_zero, h_tsum_zero]
      by_cases hyN : y ∈ N_f
      · have h_δ'y : δ' y = 0 := by simp [δ', hyN]
        rw [h_δ'y, add_zero]
        have h_term_y : iterateInfluence γ 0 y y = 1 := by
          simp [iterateInfluence_zero]
        have h_nn : ∀ x ∈ N_f, 0 ≤ iterateInfluence γ 0 y x :=
          fun x _ => iterateInfluence_nonneg γ 0 y x
        have h_sum_ge : (1 : ℝ) ≤ ∑ x ∈ N_f, iterateInfluence γ 0 y x := by
          calc (1 : ℝ) = iterateInfluence γ 0 y y := h_term_y.symm
            _ ≤ ∑ x ∈ N_f, iterateInfluence γ 0 y x :=
                Finset.single_le_sum h_nn hyN
        exact (hδ_le_one y).trans h_sum_ge
      · have h_δ'y : δ' y = δ y := by simp [δ', hyN]
        rw [h_δ'y]
        have h_zero_terms : ∀ x ∈ N_f, iterateInfluence γ 0 y x = 0 := by
          intro x hx
          simp only [iterateInfluence_zero]
          rw [if_neg]
          intro hyx; subst hyx; exact hyN hx
        have h_sum_zero : ∑ x ∈ N_f, iterateInfluence γ 0 y x = 0 :=
          Finset.sum_eq_zero h_zero_terms
        rw [h_sum_zero, zero_add]
    | succ N ih =>
      have h_iterN_summ := iterateInfluence_row_summable γ hD N y
      have h_iterN_CwX_summ : ∀ x : I,
          Summable (fun w => iterateInfluence γ N y w * influenceCoeff γ w x) := by
        intro x
        refine Summable.of_nonneg_of_le
          (fun w => mul_nonneg (iterateInfluence_nonneg γ N y w)
            (influenceCoeff_nonneg γ w x))
          (fun w => ?_) h_iterN_summ
        calc iterateInfluence γ N y w * influenceCoeff γ w x
            ≤ iterateInfluence γ N y w * 1 :=
              mul_le_mul_of_nonneg_left (influenceCoeff_le_one γ w x)
                (iterateInfluence_nonneg γ N y w)
          _ = iterateInfluence γ N y w := mul_one _
      have h_iterN_CwSum_summ :
          Summable (fun w => iterateInfluence γ N y w *
            ∑' z, influenceCoeff γ w z * δ' z) := by
        refine Summable.of_nonneg_of_le
          (fun w => mul_nonneg (iterateInfluence_nonneg γ N y w)
            (tsum_nonneg (fun z => mul_nonneg (influenceCoeff_nonneg γ w z)
              (hδ'_nn z))))
          (fun w => ?_) (h_iterN_summ.mul_right hD.α)
        exact mul_le_mul_of_nonneg_left (h_Cw_δ'_bd w)
          (iterateInfluence_nonneg γ N y w)
      -- Rewrite as a finite sum of terms, then use summable_finset_sum.
      have h_iterN_CwNSum_summ :
          Summable (fun w => iterateInfluence γ N y w *
            ∑ x ∈ N_f, influenceCoeff γ w x) := by
        have heq : (fun w => iterateInfluence γ N y w *
            ∑ x ∈ N_f, influenceCoeff γ w x) =
          (fun w => ∑ x ∈ N_f, iterateInfluence γ N y w *
            influenceCoeff γ w x) := by
          funext w; rw [Finset.mul_sum]
        rw [heq]
        exact summable_sum (fun x _ => h_iterN_CwX_summ x)
      have h_termwise : ∀ w,
          iterateInfluence γ N y w * δ' w ≤
            iterateInfluence γ N y w * (∑ x ∈ N_f, influenceCoeff γ w x) +
            iterateInfluence γ N y w * ∑' z, influenceCoeff γ w z * δ' z := by
        intro w
        calc iterateInfluence γ N y w * δ' w
            ≤ iterateInfluence γ N y w *
                ((∑ x ∈ N_f, influenceCoeff γ w x) +
                  ∑' z, influenceCoeff γ w z * δ' z) :=
              mul_le_mul_of_nonneg_left (hstep w)
                (iterateInfluence_nonneg γ N y w)
          _ = iterateInfluence γ N y w *
                (∑ x ∈ N_f, influenceCoeff γ w x) +
              iterateInfluence γ N y w * ∑' z, influenceCoeff γ w z * δ' z :=
              mul_add _ _ _
      have h_LHS_summ : Summable (fun w => iterateInfluence γ N y w * δ' w) := by
        refine Summable.of_nonneg_of_le
          (fun w => mul_nonneg (iterateInfluence_nonneg γ N y w) (hδ'_nn w))
          (fun w => ?_) h_iterN_summ
        calc iterateInfluence γ N y w * δ' w
            ≤ iterateInfluence γ N y w * 1 :=
              mul_le_mul_of_nonneg_left (hδ'_le_one w)
                (iterateInfluence_nonneg γ N y w)
          _ = iterateInfluence γ N y w := mul_one _
      have h_split_summ :
          Summable (fun w =>
            iterateInfluence γ N y w * (∑ x ∈ N_f, influenceCoeff γ w x) +
              iterateInfluence γ N y w * ∑' z, influenceCoeff γ w z * δ' z) :=
        (h_iterN_CwNSum_summ).add h_iterN_CwSum_summ
      have h_tsum_bound :
          ∑' w, iterateInfluence γ N y w * δ' w ≤
            (∑' w, iterateInfluence γ N y w *
              (∑ x ∈ N_f, influenceCoeff γ w x)) +
            ∑' w, iterateInfluence γ N y w *
              ∑' z, influenceCoeff γ w z * δ' z := by
        calc ∑' w, iterateInfluence γ N y w * δ' w
            ≤ ∑' w, (iterateInfluence γ N y w *
                (∑ x ∈ N_f, influenceCoeff γ w x) +
                iterateInfluence γ N y w *
                  ∑' z, influenceCoeff γ w z * δ' z) :=
              h_LHS_summ.tsum_le_tsum h_termwise h_split_summ
          _ = (∑' w, iterateInfluence γ N y w *
                (∑ x ∈ N_f, influenceCoeff γ w x)) +
              ∑' w, iterateInfluence γ N y w *
                ∑' z, influenceCoeff γ w z * δ' z :=
            Summable.tsum_add h_iterN_CwNSum_summ h_iterN_CwSum_summ
      -- Identify first sum with ∑ x ∈ N_f, iter^(N+1)(y, x).
      have h_first_eq :
          ∑' w, iterateInfluence γ N y w *
              (∑ x ∈ N_f, influenceCoeff γ w x) =
            ∑ x ∈ N_f, iterateInfluence γ (N + 1) y x := by
        have step1 : ∀ w, iterateInfluence γ N y w *
              (∑ x ∈ N_f, influenceCoeff γ w x) =
              ∑ x ∈ N_f, iterateInfluence γ N y w * influenceCoeff γ w x :=
          fun w => by rw [Finset.mul_sum]
        calc ∑' w, iterateInfluence γ N y w *
                (∑ x ∈ N_f, influenceCoeff γ w x)
            = ∑' w, ∑ x ∈ N_f, iterateInfluence γ N y w *
                influenceCoeff γ w x := by
              congr 1; funext w; exact step1 w
          _ = ∑ x ∈ N_f, ∑' w, iterateInfluence γ N y w *
                influenceCoeff γ w x := by
              rw [Summable.tsum_finsetSum (fun x _ => h_iterN_CwX_summ x)]
          _ = ∑ x ∈ N_f, iterateInfluence γ (N + 1) y x := rfl
      -- Second identification via Fubini.
      have h_pair_nn : ∀ p : I × I,
          0 ≤ iterateInfluence γ N y p.1 * influenceCoeff γ p.1 p.2 * δ' p.2 :=
        fun p => mul_nonneg
          (mul_nonneg (iterateInfluence_nonneg γ N y p.1)
            (influenceCoeff_nonneg γ p.1 p.2)) (hδ'_nn p.2)
      have h_inner_sum : ∀ w, Summable
          (fun z => iterateInfluence γ N y w *
            influenceCoeff γ w z * δ' z) := by
        intro w
        have : (fun z => iterateInfluence γ N y w *
            influenceCoeff γ w z * δ' z) =
          fun z => iterateInfluence γ N y w *
            (influenceCoeff γ w z * δ' z) := by
          funext z; ring
        rw [this]
        exact (h_Cw_δ'_summ w).mul_left _
      have h_outer_sum :
          Summable (fun w => ∑' z,
            iterateInfluence γ N y w * influenceCoeff γ w z * δ' z) := by
        have heq :
            (fun w => ∑' z, iterateInfluence γ N y w *
                  influenceCoeff γ w z * δ' z) =
            (fun w => iterateInfluence γ N y w *
              ∑' z, influenceCoeff γ w z * δ' z) := by
          funext w
          rw [← tsum_mul_left]
          congr 1; funext z; ring
        rw [heq]
        exact h_iterN_CwSum_summ
      have h_prod_sum : Summable
          (fun p : I × I =>
            iterateInfluence γ N y p.1 * influenceCoeff γ p.1 p.2 * δ' p.2) := by
        rw [summable_prod_of_nonneg h_pair_nn]
        exact ⟨h_inner_sum, h_outer_sum⟩
      have h_swap_sum : Summable
          (fun p : I × I =>
            iterateInfluence γ N y p.2 * influenceCoeff γ p.2 p.1 * δ' p.1) := by
        rw [show (fun p : I × I =>
            iterateInfluence γ N y p.2 * influenceCoeff γ p.2 p.1 * δ' p.1) =
          (fun p : I × I =>
            iterateInfluence γ N y p.1 * influenceCoeff γ p.1 p.2 * δ' p.2) ∘
          (Equiv.prodComm I I) from by ext ⟨a, b⟩; rfl]
        exact (Equiv.prodComm I I).summable_iff.mpr h_prod_sum
      have h_pair_nn_swap : ∀ p : I × I,
          0 ≤ iterateInfluence γ N y p.2 * influenceCoeff γ p.2 p.1 * δ' p.1 :=
        fun p => mul_nonneg
          (mul_nonneg (iterateInfluence_nonneg γ N y p.2)
            (influenceCoeff_nonneg γ p.2 p.1)) (hδ'_nn p.1)
      have h_row_z_sum : ∀ z, Summable
          (fun w => iterateInfluence γ N y w *
            influenceCoeff γ w z * δ' z) := by
        intro z
        exact ((summable_prod_of_nonneg h_pair_nn_swap).mp h_swap_sum).1 z
      have h_fubini :
          ∑' z, ∑' w, iterateInfluence γ N y w *
              influenceCoeff γ w z * δ' z =
          ∑' w, ∑' z, iterateInfluence γ N y w *
              influenceCoeff γ w z * δ' z := by
        exact h_prod_sum.tsum_comm' h_inner_sum h_row_z_sum
      have h_second_eq :
          ∑' w, iterateInfluence γ N y w *
              ∑' z, influenceCoeff γ w z * δ' z =
            ∑' z, iterateInfluence γ (N + 1) y z * δ' z := by
        have step1 : ∀ w, iterateInfluence γ N y w *
              ∑' z, influenceCoeff γ w z * δ' z =
              ∑' z, iterateInfluence γ N y w *
                influenceCoeff γ w z * δ' z := fun w => by
          rw [← tsum_mul_left]; congr 1; funext z; ring
        calc ∑' w, iterateInfluence γ N y w *
                ∑' z, influenceCoeff γ w z * δ' z
            = ∑' w, ∑' z, iterateInfluence γ N y w *
                influenceCoeff γ w z * δ' z := by
              congr 1; funext w; exact step1 w
          _ = ∑' z, ∑' w, iterateInfluence γ N y w *
                influenceCoeff γ w z * δ' z := h_fubini.symm
          _ = ∑' z, (∑' w, iterateInfluence γ N y w *
                influenceCoeff γ w z) * δ' z := by
              congr 1; funext z
              rw [← tsum_mul_right]
          _ = ∑' z, iterateInfluence γ (N + 1) y z * δ' z := rfl
      have h_step_final :
          ∑' w, iterateInfluence γ N y w * δ' w ≤
            (∑ x ∈ N_f, iterateInfluence γ (N + 1) y x) +
            ∑' w, iterateInfluence γ (N + 1) y w * δ' w := by
        rw [← h_first_eq, ← h_second_eq]
        exact h_tsum_bound
      calc δ y
          ≤ (∑ k ∈ Finset.range (N + 1),
                ∑ x ∈ N_f, iterateInfluence γ k y x) +
              ∑' w, iterateInfluence γ N y w * δ' w := ih
        _ ≤ (∑ k ∈ Finset.range (N + 1),
                ∑ x ∈ N_f, iterateInfluence γ k y x) +
              ((∑ x ∈ N_f, iterateInfluence γ (N + 1) y x) +
                ∑' w, iterateInfluence γ (N + 1) y w * δ' w) := by
            linarith [h_step_final]
        _ = (∑ k ∈ Finset.range (N + 1 + 1),
                ∑ x ∈ N_f, iterateInfluence γ k y x) +
              ∑' w, iterateInfluence γ (N + 1) y w * δ' w := by
            rw [show N + 1 + 1 = (N + 1) + 1 from rfl,
                Finset.sum_range_succ
                  (fun k => ∑ x ∈ N_f, iterateInfluence γ k y x) (N + 1)]
            ring
  -- Residual bound: ∑' w, iter^N(y,w) * δ'(w) ≤ α^N.
  have h_res_bound : ∀ N,
      ∑' w, iterateInfluence γ N y w * δ' w ≤ hD.α ^ N := by
    intro N
    have h_summ : Summable (fun w => iterateInfluence γ N y w * δ' w) := by
      refine Summable.of_nonneg_of_le
        (fun w => mul_nonneg (iterateInfluence_nonneg γ N y w) (hδ'_nn w))
        (fun w => ?_) (iterateInfluence_row_summable γ hD N y)
      calc iterateInfluence γ N y w * δ' w
          ≤ iterateInfluence γ N y w * 1 :=
            mul_le_mul_of_nonneg_left (hδ'_le_one w)
              (iterateInfluence_nonneg γ N y w)
        _ = iterateInfluence γ N y w := mul_one _
    calc ∑' w, iterateInfluence γ N y w * δ' w
        ≤ ∑' w, iterateInfluence γ N y w * 1 :=
          Summable.tsum_le_tsum
            (fun w => mul_le_mul_of_nonneg_left (hδ'_le_one w)
              (iterateInfluence_nonneg γ N y w))
            h_summ
            ((iterateInfluence_row_summable γ hD N y).congr
              (fun w => (mul_one _).symm))
      _ = ∑' w, iterateInfluence γ N y w := by
          congr 1; funext w; exact mul_one _
      _ ≤ hD.α ^ N := iterateInfluence_row_sum_bound γ hD N y
  -- Tendsto facts.
  have h_partial_sum_tendsto :
      Tendsto (fun N => ∑ k ∈ Finset.range (N + 1),
          ∑ x ∈ N_f, iterateInfluence γ k y x)
        atTop (𝓝 (∑ x ∈ N_f, neumannSeriesCoeff γ y x)) := by
    have h_eq : ∀ N,
        (∑ k ∈ Finset.range (N + 1), ∑ x ∈ N_f, iterateInfluence γ k y x) =
        ∑ x ∈ N_f, ∑ k ∈ Finset.range (N + 1), iterateInfluence γ k y x :=
      fun N => Finset.sum_comm
    have h_each : ∀ x ∈ N_f,
        Tendsto (fun N => ∑ k ∈ Finset.range (N + 1), iterateInfluence γ k y x)
          atTop (𝓝 (neumannSeriesCoeff γ y x)) := by
      intro x _
      have h := (neumannSeriesCoeff_summable γ hD y x).hasSum.tendsto_sum_nat
      exact h.comp (tendsto_add_atTop_nat 1)
    have h_fin :
        Tendsto (fun N => ∑ x ∈ N_f,
          ∑ k ∈ Finset.range (N + 1), iterateInfluence γ k y x)
          atTop (𝓝 (∑ x ∈ N_f, neumannSeriesCoeff γ y x)) :=
      tendsto_finset_sum N_f h_each
    have hfun_eq : (fun N => ∑ k ∈ Finset.range (N + 1),
        ∑ x ∈ N_f, iterateInfluence γ k y x) =
        (fun N => ∑ x ∈ N_f, ∑ k ∈ Finset.range (N + 1),
          iterateInfluence γ k y x) := by
      funext N; exact h_eq N
    rw [hfun_eq]; exact h_fin
  have h_res_tendsto :
      Tendsto (fun N => ∑' w, iterateInfluence γ N y w * δ' w) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ N ≥ N₀, hD.α ^ N < ε := by
      have hgeom : Tendsto (fun N : ℕ => hD.α ^ N) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hD.hα_pos hD.hα_lt
      rw [Metric.tendsto_atTop] at hgeom
      obtain ⟨N₀, h⟩ := hgeom ε hε
      refine ⟨N₀, fun N hN => ?_⟩
      have := h N hN
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hD.hα_pos N)] at this
      exact this
    refine ⟨N₀, fun N hN => ?_⟩
    have hres_nn : 0 ≤ ∑' w, iterateInfluence γ N y w * δ' w :=
      tsum_nonneg (fun w => mul_nonneg (iterateInfluence_nonneg γ N y w) (hδ'_nn w))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hres_nn]
    exact lt_of_le_of_lt (h_res_bound N) (hN₀ N hN)
  have h_rhs_tendsto :
      Tendsto
        (fun N => (∑ k ∈ Finset.range (N + 1),
            ∑ x ∈ N_f, iterateInfluence γ k y x) +
          ∑' w, iterateInfluence γ N y w * δ' w)
        atTop (𝓝 (∑ x ∈ N_f, neumannSeriesCoeff γ y x)) := by
    have := h_partial_sum_tendsto.add h_res_tendsto
    simpa using this
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds h_rhs_tendsto h_ind

/-! ## Multi-site marginal TV bound -/

/-- **Marginal TV bound for the multi-site conditional.** The `y`-marginal
TV distance between `condFiniteSupportMeasure μ N_f a` and `μ` is bounded
by the sum of Neumann-series coefficients `∑ x ∈ N_f, neumannSeriesCoeff γ y x`. -/
lemma condFiniteSupportMeasure_marginalTvDist_le_neumannSeriesSum
    [Fintype I] [Fintype S] [MeasurableSingletonClass S]
    [MeasurableEq (SpinConfig I S)]
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (N_f : Finset I) (a : I → S) (hpos : μ (multiFiber N_f a) ≠ 0)
    [IsProbabilityMeasure (condFiniteSupportMeasure μ N_f a)]
    (y : I)
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    marginalTvDist (condFiniteSupportMeasure μ N_f a) μ y ≤
      ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by
  set T : Set I := {z | z ∉ N_f} with hT_def
  have hdlr₁ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (condFiniteSupportMeasure μ N_f a A).toReal =
        ∫ σ, (γ.condDist {z} σ A).toReal ∂(condFiniteSupportMeasure μ N_f a) := by
    intro z hzT A hA
    exact condFiniteSupportMeasure_dlr_at_site γ μ hμ N_f a hpos z hzT A hA
  have hdlr₂ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (μ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ := by
    intro z _ A hA
    exact hμ.dlr {z} A hA
  obtain ⟨P, hP_coup, hP_ineq⟩ :=
    dobrushin_iterated_coupling_exists γ (condFiniteSupportMeasure μ N_f a) μ T
      hdlr₁ hdlr₂ hfinsupp h_dep_F
  haveI := hP_coup.isProb
  set δ : I → ℝ :=
    fun w => (P {p : SpinConfig I S × SpinConfig I S | p.1 w ≠ p.2 w}).toReal
    with hδ_def
  have hδ_nn : ∀ w, 0 ≤ δ w := fun _ => ENNReal.toReal_nonneg
  have hδ_le_one : ∀ w, δ w ≤ 1 := by
    intro w
    have h := prob_le_one (μ := P)
      (s := {p : SpinConfig I S × SpinConfig I S | p.1 w ≠ p.2 w})
    calc (P {p : SpinConfig I S × SpinConfig I S | p.1 w ≠ p.2 w}).toReal
        ≤ (1 : ENNReal).toReal :=
          ENNReal.toReal_mono (by simp) h
      _ = 1 := by simp
  have hcontract : ∀ z, z ∉ N_f → δ z ≤ ∑' w, influenceCoeff γ z w * δ w := by
    intro z hzN
    exact hP_ineq z hzN
  have hδ_le_neu : δ y ≤ ∑ x ∈ N_f, neumannSeriesCoeff γ y x :=
    abstract_neumann_iteration_finset γ hD N_f δ hδ_nn hδ_le_one hcontract y
  have h_marg_le :
      marginalTvDist (condFiniteSupportMeasure μ N_f a) μ y ≤ δ y :=
    marginalTvDist_le_coupling_site (condFiniteSupportMeasure μ N_f a) μ P hP_coup y
  exact le_trans h_marg_le hδ_le_neu

/-! ## Multi-site condTV bound for single-site g

This is the primary bridge: for an arbitrary `N_f`-local f and a
*single-site*-local g at y, bound
`|∫g d(cond μ N_f a) − ∫g dμ|` by `2·Bg·∑ x ∈ N_f, neumannSeriesCoeff γ y x`.

A fully multi-site-local version for g is straightforward to obtain by
union-bounding over `N_g`: one adds `2·Bg·∑ x ∈ N_f, neumannSeriesCoeff γ y x`
across `y ∈ N_g`. See `condTV_bound_multisite_Ng` below. -/

/-- **Multi-site condTV bound for single-site g.** For a Gibbs measure μ,
a single-site-local g at y bounded by Bg, and a multi-site conditioning at
`(N_f, a)`, the conditional-expectation difference is bounded by
`2 · Bg · ∑ x ∈ N_f, neumannSeriesCoeff γ y x`. -/
theorem condTV_bound_multisite_y
    [Inhabited S] [Fintype I] [Fintype S] [MeasurableSingletonClass S]
    [MeasurableEq (SpinConfig I S)]
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (g : SpinConfig I S → ℝ) (hg_meas : Measurable g)
    (Bg : ℝ) (hBg_nn : 0 ≤ Bg) (hBg : ∀ σ, |g σ| ≤ Bg)
    (N_f : Finset I) (a : I → S) (y : I)
    (hg_local : ∀ σ τ : SpinConfig I S, σ y = τ y → g σ = g τ)
    (hg_int : Integrable g μ)
    (hpos : μ (multiFiber N_f a) ≠ 0)
    (hg_cond_int : Integrable g (condFiniteSupportMeasure μ N_f a))
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    |∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f a) - ∫ σ, g σ ∂μ| ≤
      2 * Bg * ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by
  have hne_top : μ (multiFiber N_f a) ≠ ⊤ := (measure_lt_top μ _).ne
  haveI : IsProbabilityMeasure (condFiniteSupportMeasure μ N_f a) :=
    isProbabilityMeasure_condFiniteSupportMeasure μ N_f a hpos hne_top
  have h1 := local_integral_sub_le_marginalTvDist
    (condFiniteSupportMeasure μ N_f a) μ g y hg_local hg_meas Bg hBg_nn hBg
    hg_cond_int hg_int
  have h2 := condFiniteSupportMeasure_marginalTvDist_le_neumannSeriesSum
    γ hD μ hμ N_f a hpos y hfinsupp h_dep_F
  calc |∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f a) - ∫ σ, g σ ∂μ|
      ≤ 2 * Bg * marginalTvDist (condFiniteSupportMeasure μ N_f a) μ y := h1
    _ ≤ 2 * Bg * ∑ x ∈ N_f, neumannSeriesCoeff γ y x :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-! ## Short wiring: multi-site single-site covariance bound

Combines `condTV_bound_multisite_y` with the standard single-site covariance
decomposition to produce a multi-site covariance bound for f single-site-local
at x and g single-site-local at y via a trivial specialization `N_f := {x}`.
This is NOT the full multi-site bound (f general multi-site would require a
different decomposition), but it provides a clean composition point. -/

/-- **Textbook exponential decay wiring for the multi-site marginal TV.**

Specializes `condFiniteSupportMeasure_marginalTvDist_le_neumannSeriesSum` via
`neumannSeriesCoeff_nn_dist_bound` to obtain the textbook
`α^{d(y, x)}/(1−α)` form summed over `x ∈ N_f`.

Use case: lgt plaquette mass-gap proof where the plaquette observable `plaqObs`
depends on 4 links (i.e. `N_f` has 4 elements). The bound gives:
`marginalTvDist(cond μ N_f a, μ, y) ≤ ∑ x ∈ N_f, α^{d(y,x)}/(1−α)`. -/
theorem condFiniteSupportMeasure_marginalTvDist_nn_dist_bound
    [Fintype I] [Fintype S] [MeasurableSingletonClass S]
    [MeasurableEq (SpinConfig I S)]
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (N_f : Finset I) (a : I → S) (hpos : μ (multiFiber N_f a) ≠ 0)
    [IsProbabilityMeasure (condFiniteSupportMeasure μ N_f a)]
    (y : I)
    (d : I → I → ℕ)
    (h_refl : ∀ x, d x x = 0)
    (h_triangle : ∀ x y z, d x y ≤ d x z + d z y)
    (h_support : ∀ u v, d u v > 1 → influenceCoeff γ u v = 0)
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    marginalTvDist (condFiniteSupportMeasure μ N_f a) μ y ≤
      ∑ x ∈ N_f, hD.α ^ d y x / (1 - hD.α) := by
  have h1 := condFiniteSupportMeasure_marginalTvDist_le_neumannSeriesSum
    γ hD μ hμ N_f a hpos y hfinsupp h_dep_F
  have h2 : ∀ x, neumannSeriesCoeff γ y x ≤ hD.α ^ d y x / (1 - hD.α) :=
    fun x => neumannSeriesCoeff_nn_dist_bound γ hD d h_refl h_triangle h_support y x
  have h3 : ∑ x ∈ N_f, neumannSeriesCoeff γ y x ≤
      ∑ x ∈ N_f, hD.α ^ d y x / (1 - hD.α) :=
    Finset.sum_le_sum (fun x _ => h2 x)
  exact le_trans h1 h3

/-! ## Multi-site disintegration (T1)

Generalizes `tsum_integral_condSingleSiteMeasure` to multi-site fibers.
We parameterize fibers by `a : N_f → S` (functions on the subtype),
which gives a pairwise disjoint decomposition of `SpinConfig I S`.
-/

/-- Extend a function `a : N_f → S` to all of `I → S` by using the
default value outside `N_f`. -/
def extendOnFinset [Inhabited S] (N_f : Finset I) (a : N_f → S) :
    I → S :=
  fun i => if h : i ∈ N_f then a ⟨i, h⟩ else (default : S)

omit [MeasurableSpace S] in
/-- `extendOnFinset a` agrees with `a` on `N_f`. -/
lemma extendOnFinset_mem [Inhabited S] (N_f : Finset I) (a : N_f → S)
    (i : I) (hi : i ∈ N_f) :
    extendOnFinset N_f a i = a ⟨i, hi⟩ := by
  simp [extendOnFinset, hi]

omit [MeasurableSpace S] in
/-- Two configurations agreeing on `N_f` identify the fiber parameter. -/
lemma multiFiber_extend_iff [Inhabited S] {N_f : Finset I}
    {a : N_f → S} {σ : SpinConfig I S} :
    σ ∈ multiFiber N_f (extendOnFinset N_f a) ↔
      ∀ (w : I) (hw : w ∈ N_f), σ w = a ⟨w, hw⟩ := by
  refine ⟨fun h w hw => ?_, fun h w hw => ?_⟩
  · have := h w hw
    rw [extendOnFinset_mem N_f a w hw] at this
    exact this
  · rw [extendOnFinset_mem N_f a w hw]; exact h w hw

omit [MeasurableSpace S] in
/-- The canonical `N_f → S`-parameter of a configuration. -/
def restrictToFinset (N_f : Finset I) (σ : SpinConfig I S) : N_f → S :=
  fun w => σ w.1

omit [MeasurableSpace S] in
/-- Every configuration lies in exactly one multi-fiber (parameterized by
`a : N_f → S`). -/
lemma mem_multiFiber_extend_restrictToFinset [Inhabited S]
    (N_f : Finset I) (σ : SpinConfig I S) :
    σ ∈ multiFiber N_f (extendOnFinset N_f (restrictToFinset N_f σ)) := by
  intro w hw
  rw [extendOnFinset_mem N_f _ w hw]
  rfl

omit [MeasurableSpace S] in
/-- Union of multi-fibers (parameterized by `a : N_f → S`) covers all configs. -/
lemma iUnion_multiFiber_extend [Inhabited S] (N_f : Finset I) :
    (⋃ a : N_f → S,
        multiFiber (I := I) (S := S) N_f (extendOnFinset N_f a)) = Set.univ := by
  ext σ
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  refine ⟨restrictToFinset N_f σ, ?_⟩
  exact mem_multiFiber_extend_restrictToFinset N_f σ

omit [MeasurableSpace S] in
/-- Multi-fibers parameterized by distinct `a : N_f → S` are disjoint. -/
lemma pairwise_disjoint_multiFiber_extend [Inhabited S] (N_f : Finset I) :
    Pairwise (Function.onFun Disjoint
      (fun a : N_f → S =>
        multiFiber (I := I) (S := S) N_f (extendOnFinset N_f a))) := by
  intro a b hab
  rw [Function.onFun, Set.disjoint_iff]
  intro σ hσ
  rcases hσ with ⟨ha, hb⟩
  rw [multiFiber_extend_iff] at ha hb
  apply hab
  funext ⟨w, hw⟩
  rw [← ha w hw, hb w hw]

/-- Countable union decomposition of `μ` along multi-fibers. -/
lemma sum_restrict_multiFiber_eq [Countable S] [MeasurableSingletonClass S]
    [Inhabited S]
    (μ : Measure (SpinConfig I S)) (N_f : Finset I) :
    (Measure.sum fun a : N_f → S =>
        μ.restrict (multiFiber (I := I) (S := S) N_f
          (extendOnFinset N_f a))) = μ := by
  have hcov := iUnion_multiFiber_extend (I := I) (S := S) N_f
  have hdisj := pairwise_disjoint_multiFiber_extend (I := I) (S := S) N_f
  have hmeas : ∀ a : N_f → S,
      MeasurableSet (multiFiber (I := I) (S := S) N_f (extendOnFinset N_f a)) :=
    fun a => measurableSet_multiFiber N_f _
  have := Measure.restrict_iUnion (μ := μ)
    (s := fun a : N_f → S =>
      multiFiber (I := I) (S := S) N_f (extendOnFinset N_f a)) hdisj hmeas
  rw [hcov, Measure.restrict_univ] at this
  exact this.symm

/-- **Multi-site disintegration identity, tsum form.**

For integrable `f`, the integral of `f` with respect to `μ` decomposes
into a countable sum (over `a : N_f → S`) of conditional expectations
weighted by the fiber masses. Generalizes
`tsum_integral_condSingleSiteMeasure`. -/
theorem tsum_integral_condFiniteSupportMeasure
    [Countable S] [MeasurableSingletonClass S] [Inhabited S]
    (μ : Measure (SpinConfig I S)) [IsFiniteMeasure μ]
    (N_f : Finset I) {f : SpinConfig I S → ℝ} (hf : Integrable f μ) :
    ∫ σ, f σ ∂μ =
      ∑' a : N_f → S,
        (μ (multiFiber N_f (extendOnFinset N_f a))).toReal •
          ∫ σ, f σ ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) := by
  have hsum := sum_restrict_multiFiber_eq (I := I) (S := S) μ N_f
  have hf' : Integrable f (Measure.sum (fun a : N_f → S =>
      μ.restrict (multiFiber N_f (extendOnFinset N_f a)))) := by
    rw [hsum]; exact hf
  calc
    ∫ σ, f σ ∂μ
        = ∫ σ, f σ ∂(Measure.sum (fun a : N_f → S =>
            μ.restrict (multiFiber N_f (extendOnFinset N_f a)))) := by rw [hsum]
    _ = ∑' a : N_f → S, ∫ σ, f σ ∂(μ.restrict (multiFiber N_f
            (extendOnFinset N_f a))) := integral_sum_measure hf'
    _ = ∑' a : N_f → S,
          (μ (multiFiber N_f (extendOnFinset N_f a))).toReal •
            ∫ σ, f σ ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) := by
        apply tsum_congr
        intro a
        by_cases hmass : μ (multiFiber N_f (extendOnFinset N_f a)) = 0
        · have hzero :
              μ.restrict (multiFiber N_f (extendOnFinset N_f a)) = 0 := by
            rw [Measure.restrict_eq_zero]; exact hmass
          rw [hzero]
          simp [condFiniteSupportMeasure, hmass]
        · have hne_top : μ (multiFiber N_f (extendOnFinset N_f a)) ≠ ⊤ :=
            (measure_lt_top μ _).ne
          have hrescale :
              ∫ σ, f σ ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a))
                = ((μ (multiFiber N_f (extendOnFinset N_f a)))⁻¹).toReal
                    • ∫ σ, f σ ∂(μ.restrict
                        (multiFiber N_f (extendOnFinset N_f a))) := by
            simp [condFiniteSupportMeasure, integral_smul_measure]
          rw [hrescale, smul_smul]
          have hpos_toReal :
              (μ (multiFiber N_f (extendOnFinset N_f a))).toReal *
                ((μ (multiFiber N_f (extendOnFinset N_f a)))⁻¹).toReal = 1 := by
            rw [ENNReal.toReal_inv]
            exact mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hmass, hne_top⟩)
          rw [hpos_toReal]; simp

/-! ## Fiber-mass summability for multi-site fibers -/

/-- The fiber masses (over the `N_f → S` parameterization) sum to `1`. -/
lemma multiFiber_toReal_tsum_eq_one
    [Countable S] [MeasurableSingletonClass S] [Inhabited S]
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (N_f : Finset I) :
    ∑' a : N_f → S, (μ (multiFiber N_f (extendOnFinset N_f a))).toReal = 1 := by
  have h := tsum_integral_condFiniteSupportMeasure μ N_f
    (f := fun _ => (1 : ℝ)) (integrable_const (1 : ℝ))
  have hlhs : ∫ _, (1 : ℝ) ∂μ = 1 := by simp
  rw [hlhs] at h
  rw [h]
  apply tsum_congr; intro a
  by_cases ha : μ (multiFiber N_f (extendOnFinset N_f a)) = 0
  · simp [ha, ENNReal.toReal_eq_zero_iff]
  · have hne_top : μ (multiFiber N_f (extendOnFinset N_f a)) ≠ ⊤ :=
      (measure_lt_top μ _).ne
    have hprob :=
      isProbabilityMeasure_condFiniteSupportMeasure μ N_f _ ha hne_top
    have : ∫ _, (1 : ℝ) ∂(condFiniteSupportMeasure μ N_f
        (extendOnFinset N_f a)) = 1 := by simp
    rw [this, smul_eq_mul, mul_one]

/-! ## Multi-site bridge: factoring out `f` on each fiber

Analog of `integral_local_mul` for the multi-site case. -/

/-- If `f` is `N_f`-local, then `f σ = f σ₀` a.e. under
`condFiniteSupportMeasure μ N_f a` for any `σ₀` agreeing with `a` on `N_f`.
(Restated here for convenience; same as `local_fn_ae_const_multisite`.) -/
lemma integral_local_multisite_eq
    [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) [IsFiniteMeasure μ]
    (N_f : Finset I) (a : I → S)
    (f : SpinConfig I S → ℝ)
    (hf_local : ∀ σ τ : SpinConfig I S,
      (∀ w ∈ N_f, σ w = τ w) → f σ = f τ)
    (σ₀ : SpinConfig I S) (hσ₀ : ∀ w ∈ N_f, σ₀ w = a w)
    (hpos : μ (multiFiber N_f a) ≠ 0) :
    ∫ σ, f σ ∂(condFiniteSupportMeasure μ N_f a) = f σ₀ := by
  have hne_top : μ (multiFiber N_f a) ≠ ⊤ := (measure_lt_top μ _).ne
  have _ := isProbabilityMeasure_condFiniteSupportMeasure μ N_f a hpos hne_top
  rw [integral_congr_ae (local_fn_ae_const_multisite μ N_f a f hf_local σ₀ hσ₀)]
  simp [measure_univ]

/-- `∫ f · g d(condμ) = f(σ₀) · ∫ g d(condμ)` for `f` `N_f`-local and any
`σ₀` agreeing with `a` on `N_f`. -/
lemma integral_local_mul_multisite
    [MeasurableSingletonClass S]
    (μ : Measure (SpinConfig I S)) [IsFiniteMeasure μ]
    (N_f : Finset I) (a : I → S) (f g : SpinConfig I S → ℝ)
    (hf_local : ∀ σ τ : SpinConfig I S,
      (∀ w ∈ N_f, σ w = τ w) → f σ = f τ)
    (σ₀ : SpinConfig I S) (hσ₀ : ∀ w ∈ N_f, σ₀ w = a w)
    (hpos : μ (multiFiber N_f a) ≠ 0)
    (hg_int : Integrable g (condFiniteSupportMeasure μ N_f a)) :
    ∫ σ, f σ * g σ ∂(condFiniteSupportMeasure μ N_f a) =
      f σ₀ * ∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f a) := by
  have hne_top : μ (multiFiber N_f a) ≠ ⊤ := (measure_lt_top μ _).ne
  have _ := isProbabilityMeasure_condFiniteSupportMeasure μ N_f a hpos hne_top
  have hae : ∀ᵐ σ ∂(condFiniteSupportMeasure μ N_f a),
      f σ * g σ = f σ₀ * g σ := by
    filter_upwards [local_fn_ae_const_multisite μ N_f a f hf_local σ₀ hσ₀]
      with σ hσ; rw [hσ]
  rw [integral_congr_ae hae, integral_const_mul]

/-! ## Multi-site `covariance_bound_via_bridge`

Direct generalization of `covariance_bound_via_bridge` to multi-site-local
`f` with conditioning on `multiFiber N_f a`. -/

/-- **Multi-site covariance bound via conditional bridge.**

For `f` `N_f`-local with `|f| ≤ Bf` on a probability space, if the
conditional-expectation difference of `g` against every positive-mass
multi-fiber is bounded by `K`, then `|Cov(f, g)| ≤ Bf · K`.

This generalizes `covariance_bound_via_bridge` (single-site `x` replaced
by finite set `N_f`, with parameterization of fibers by `a : N_f → S`). -/
lemma covariance_bound_via_bridge_multisite
    [Countable S] [MeasurableSingletonClass S] [Inhabited S]
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (f g : SpinConfig I S → ℝ)
    (Bf : ℝ) (hBf_nn : 0 ≤ Bf) (hBf : ∀ σ, |f σ| ≤ Bf)
    (N_f : Finset I)
    (hf_local : ∀ σ τ : SpinConfig I S,
      (∀ w ∈ N_f, σ w = τ w) → f σ = f τ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun σ => f σ * g σ) μ)
    (K : ℝ) (hK_nn : 0 ≤ K)
    (hcond_bound : ∀ a : N_f → S,
      μ (multiFiber N_f (extendOnFinset N_f a)) ≠ 0 →
      |∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) -
          ∫ σ, g σ ∂μ| ≤ K)
    (choose_σ : (N_f → S) → SpinConfig I S)
    (h_choose : ∀ a : N_f → S,
      ∀ w (hw : w ∈ N_f), choose_σ a w = a ⟨w, hw⟩)
    (hg_cond : ∀ a : N_f → S,
      μ (multiFiber N_f (extendOnFinset N_f a)) ≠ 0 →
      Integrable g (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a))) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)| ≤ Bf * K := by
  set Eg := ∫ σ, g σ ∂μ
  -- Centering identity: Cov(f, g) = E[f · (g - Eg)].
  have hfEg : Integrable (fun σ => f σ * Eg) μ := by
    have : (fun σ => f σ * Eg) = fun σ => Eg * f σ := by ext σ; ring
    rw [this]; exact hf.const_mul Eg
  have hfgc : Integrable (fun σ => f σ * (g σ - Eg)) μ := by
    have : (fun σ => f σ * (g σ - Eg)) = fun σ => f σ * g σ - Eg * f σ := by
      ext σ; ring
    rw [this]; exact hfg.sub (hf.const_mul Eg)
  have cov_eq : ∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * Eg =
      ∫ σ, f σ * (g σ - Eg) ∂μ := by
    have h1 : ∫ σ, f σ * (g σ - Eg) ∂μ =
        ∫ σ, (f σ * g σ - Eg * f σ) ∂μ := by
      apply integral_congr_ae; filter_upwards with σ; ring
    rw [h1, integral_sub hfg (hf.const_mul Eg)]
    have h2 : ∫ σ, Eg * f σ ∂μ = Eg * ∫ σ, f σ ∂μ := integral_const_mul Eg f
    linarith
  rw [cov_eq]
  -- Decompose via T1.
  have hfgc_dec := tsum_integral_condFiniteSupportMeasure μ N_f hfgc
  -- Factor f out on each fiber.
  have hterm : ∀ a : N_f → S,
      (μ (multiFiber N_f (extendOnFinset N_f a))).toReal •
        ∫ σ, f σ * (g σ - Eg)
          ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) =
      (μ (multiFiber N_f (extendOnFinset N_f a))).toReal *
        (f (choose_σ a) *
          (∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a))
            - Eg)) := by
    intro a
    by_cases ha : μ (multiFiber N_f (extendOnFinset N_f a)) = 0
    · simp [condFiniteSupportMeasure, ha]
    · rw [smul_eq_mul]
      have hne_top : μ (multiFiber N_f (extendOnFinset N_f a)) ≠ ⊤ :=
        (measure_lt_top μ _).ne
      have _ :=
        isProbabilityMeasure_condFiniteSupportMeasure μ N_f _ ha hne_top
      have hσ₀ : ∀ w ∈ N_f, choose_σ a w = extendOnFinset N_f a w := by
        intro w hw
        rw [h_choose a w hw, extendOnFinset_mem N_f a w hw]
      have hae : ∀ᵐ σ ∂(condFiniteSupportMeasure μ N_f
          (extendOnFinset N_f a)),
          f σ * (g σ - Eg) = f (choose_σ a) * (g σ - Eg) := by
        filter_upwards [local_fn_ae_const_multisite μ N_f
          (extendOnFinset N_f a) f hf_local (choose_σ a) hσ₀]
          with σ hσ; rw [hσ]
      rw [integral_congr_ae hae, integral_const_mul]
      congr 1
      rw [integral_sub (hg_cond a ha) (integrable_const Eg)]
      simp
  rw [hfgc_dec]; simp_rw [hterm]
  -- Bound the tsum by Bf · K via termwise |T a| ≤ w(a) · Bf · K.
  set T : (N_f → S) → ℝ := fun a =>
    (μ (multiFiber N_f (extendOnFinset N_f a))).toReal *
      (f (choose_σ a) *
        (∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) - Eg))
  have hTB : ∀ a, ‖T a‖ ≤
      (μ (multiFiber N_f (extendOnFinset N_f a))).toReal * (Bf * K) := by
    intro a; rw [Real.norm_eq_abs]
    by_cases ha : μ (multiFiber N_f (extendOnFinset N_f a)) = 0
    · simp [T, show (μ (multiFiber N_f (extendOnFinset N_f a))).toReal = 0 from
        by rw [ENNReal.toReal_eq_zero_iff]; exact Or.inl ha]
    · rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      rw [abs_mul]
      exact mul_le_mul (hBf _) (hcond_bound a ha) (abs_nonneg _) hBf_nn
  -- Summability of the fiber weights (they sum to 1).
  have hw_summ : Summable (fun a : N_f → S =>
      (μ (multiFiber N_f (extendOnFinset N_f a))).toReal) := by
    apply ENNReal.summable_toReal
    have hdisj := pairwise_disjoint_multiFiber_extend (I := I) (S := S) N_f
    have hmeas : ∀ a : N_f → S,
        MeasurableSet (multiFiber (I := I) (S := S) N_f
          (extendOnFinset N_f a)) :=
      fun a => measurableSet_multiFiber N_f _
    have heq :
        ∑' a : N_f → S, μ (multiFiber N_f (extendOnFinset N_f a))
          = μ Set.univ := by
      rw [← iUnion_multiFiber_extend (I := I) (S := S) N_f]
      exact (measure_iUnion hdisj hmeas).symm
    rw [heq, measure_univ]; exact ENNReal.one_ne_top
  have hB_summ : Summable (fun a : N_f → S =>
      (μ (multiFiber N_f (extendOnFinset N_f a))).toReal * (Bf * K)) :=
    hw_summ.mul_right _
  have hT_summ : Summable T := Summable.of_norm_bounded hB_summ hTB
  have hTnorm_summ : Summable (fun a => ‖T a‖) :=
    Summable.of_nonneg_of_le (fun a => norm_nonneg _) hTB hB_summ
  calc |∑' a, T a|
      = ‖∑' a, T a‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' a, ‖T a‖ := norm_tsum_le_tsum_norm hTnorm_summ
    _ ≤ ∑' a, (μ (multiFiber N_f (extendOnFinset N_f a))).toReal * (Bf * K) :=
        Summable.tsum_le_tsum hTB hTnorm_summ hB_summ
    _ = (∑' a, (μ (multiFiber N_f (extendOnFinset N_f a))).toReal) * (Bf * K) := by
        rw [← tsum_mul_right]
    _ = 1 * (Bf * K) := by rw [multiFiber_toReal_tsum_eq_one μ N_f]
    _ = Bf * K := one_mul _

/-! ## T2: Full two-sided multi-site covariance bound

Combines the multi-site bridge `covariance_bound_via_bridge_multisite`
with `condTV_bound_multisite_y` applied at each `y ∈ N_g` via a
telescoping / union bound. -/

/-- **Full two-sided multi-site covariance bound.**

For a Gibbs measure `μ` under Dobrushin's condition, with `f` `N_f`-local
and `g` `N_g`-local observables bounded by `Bf, Bg`:

    |Cov_μ(f, g)| ≤ 2 · Bf · Bg · ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x

The proof composes two ingredients:
1. `covariance_bound_via_bridge_multisite` (factoring f out on each `N_f`-fiber);
2. a witness-decomposition of `g` as a finite sum of single-site-local terms,
   each of which is bounded against the conditional via `condTV_bound_multisite_y`.

The user supplies the witness decomposition `g_witness : I → SpinConfig I S → ℝ`
(each `g_witness y` is single-site-local at `y`, bounded by `Bg`) with the
equality `g σ = ∑ y ∈ N_g, g_witness y σ`. For the application in LGT's
Wilson plaquette setting, such a witness decomposition is natural: each
Wilson plaquette is `∑ over 4 links, contribution depending only on that link`.

The `|N_g|` factor is absorbed into the outer sum: the final bound is exactly
`∑∑` (not a max times `|N_g|`). -/
theorem covariance_bound_gibbs_multisite
    [Inhabited S] [Fintype I] [Fintype S] [MeasurableSingletonClass S]
    [MeasurableEq (SpinConfig I S)]
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (f g : SpinConfig I S → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (Bf Bg : ℝ) (hBf_nn : 0 ≤ Bf) (hBg_nn : 0 ≤ Bg)
    (hBf : ∀ σ, |f σ| ≤ Bf) (hBg : ∀ σ, |g σ| ≤ Bg)
    (N_f N_g : Finset I)
    (hf_local : ∀ σ τ, (∀ w ∈ N_f, σ w = τ w) → f σ = f τ)
    (hg_local : ∀ σ τ, (∀ w ∈ N_g, σ w = τ w) → g σ = g τ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun σ => f σ * g σ) μ)
    (choose_σ : (N_f → S) → SpinConfig I S)
    (h_choose : ∀ a : N_f → S,
      ∀ w (hw : w ∈ N_f), choose_σ a w = a ⟨w, hw⟩)
    (hg_cond : ∀ a : N_f → S,
      μ (multiFiber N_f (extendOnFinset N_f a)) ≠ 0 →
      Integrable g (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)))
    -- Single-site-local witnesses: for each y ∈ N_g, a function g_y that
    -- is single-site-local at y and differs from g by a bounded amount.
    -- We bypass this via direct summation.
    (g_witness : I → SpinConfig I S → ℝ)
    (g_witness_meas : ∀ y, Measurable (g_witness y))
    (g_witness_local : ∀ y σ τ, σ y = τ y → g_witness y σ = g_witness y τ)
    (g_witness_bound : ∀ y σ, |g_witness y σ| ≤ Bg)
    (g_witness_int : ∀ y, Integrable (g_witness y) μ)
    (g_witness_cond_int : ∀ y a,
      μ (multiFiber N_f (extendOnFinset N_f a)) ≠ 0 →
      Integrable (g_witness y)
        (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)))
    -- Decomposition hypothesis: g = ∑ y ∈ N_g, g_witness y under integrals
    -- (pointwise equality a.e. suffices but we assume pointwise for simplicity).
    (g_decomp : ∀ σ, g σ = ∑ y ∈ N_g, g_witness y σ)
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)| ≤
      2 * Bf * Bg * ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x := by
  -- Build the bridge: for each a : N_f → S with positive-mass fiber,
  -- the conditional TV difference on g is bounded by
  -- 2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x.
  -- This follows by summing condTV_bound_multisite_y over y ∈ N_g
  -- after rewriting g = ∑ g_witness y.
  have hCondTV : ∀ a : N_f → S,
      μ (multiFiber N_f (extendOnFinset N_f a)) ≠ 0 →
      |∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) -
        ∫ σ, g σ ∂μ| ≤
        2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by
    intro a hpos
    have hne_top : μ (multiFiber N_f (extendOnFinset N_f a)) ≠ ⊤ :=
      (measure_lt_top μ _).ne
    haveI : IsProbabilityMeasure
        (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) :=
      isProbabilityMeasure_condFiniteSupportMeasure μ N_f _ hpos hne_top
    -- Rewrite g via g_decomp and apply linearity.
    have hLHS :
        ∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) =
          ∑ y ∈ N_g,
            ∫ σ, g_witness y σ
              ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) := by
      rw [show (fun σ => g σ) =
            (fun σ => ∑ y ∈ N_g, g_witness y σ) from funext g_decomp]
      rw [integral_finset_sum N_g (fun y _ => g_witness_cond_int y a hpos)]
    have hRHS :
        ∫ σ, g σ ∂μ = ∑ y ∈ N_g, ∫ σ, g_witness y σ ∂μ := by
      rw [show (fun σ => g σ) =
            (fun σ => ∑ y ∈ N_g, g_witness y σ) from funext g_decomp]
      rw [integral_finset_sum N_g (fun y _ => g_witness_int y)]
    rw [hLHS, hRHS, ← Finset.sum_sub_distrib]
    calc |∑ y ∈ N_g,
            (∫ σ, g_witness y σ
              ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) -
              ∫ σ, g_witness y σ ∂μ)|
        ≤ ∑ y ∈ N_g,
            |∫ σ, g_witness y σ
              ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) -
              ∫ σ, g_witness y σ ∂μ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ N_g, 2 * Bg * ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by
          refine Finset.sum_le_sum (fun y _ => ?_)
          exact condTV_bound_multisite_y γ hD μ hμ
            (g_witness y) (g_witness_meas y) Bg hBg_nn (g_witness_bound y)
            N_f (extendOnFinset N_f a) y (g_witness_local y) (g_witness_int y)
            hpos (g_witness_cond_int y a hpos) hfinsupp h_dep_F
      _ = 2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by
          rw [← Finset.mul_sum]
  -- Apply the multi-site bridge.
  have hK_nn : 0 ≤ 2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by
    refine mul_nonneg (mul_nonneg (by norm_num) hBg_nn) ?_
    exact Finset.sum_nonneg (fun y _ =>
      Finset.sum_nonneg (fun x _ => neumannSeriesCoeff_nonneg γ y x))
  have hswap :
      (∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x) =
      ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x :=
    Finset.sum_comm
  calc |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)|
      ≤ Bf * (2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x) :=
        covariance_bound_via_bridge_multisite μ f g Bf hBf_nn hBf N_f
          hf_local hf hg hfg _ hK_nn hCondTV choose_σ h_choose hg_cond
    _ = 2 * Bf * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by ring
    _ = 2 * Bf * Bg * ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x := by
        rw [hswap]

/-! ## T3: Textbook wrapper -/

/-- **Textbook exponential decay wiring for the full two-sided covariance bound.**

Specializes `covariance_bound_gibbs_multisite` via
`neumannSeriesCoeff_nn_dist_bound` to the textbook `α^{d(y,x)}/(1−α)` form. -/
theorem covariance_bound_gibbs_multisite_nn_dist
    [Inhabited S] [Fintype I] [Fintype S] [MeasurableSingletonClass S]
    [MeasurableEq (SpinConfig I S)]
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (f g : SpinConfig I S → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (Bf Bg : ℝ) (hBf_nn : 0 ≤ Bf) (hBg_nn : 0 ≤ Bg)
    (hBf : ∀ σ, |f σ| ≤ Bf) (hBg : ∀ σ, |g σ| ≤ Bg)
    (N_f N_g : Finset I)
    (hf_local : ∀ σ τ, (∀ w ∈ N_f, σ w = τ w) → f σ = f τ)
    (hg_local : ∀ σ τ, (∀ w ∈ N_g, σ w = τ w) → g σ = g τ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun σ => f σ * g σ) μ)
    (choose_σ : (N_f → S) → SpinConfig I S)
    (h_choose : ∀ a : N_f → S,
      ∀ w (hw : w ∈ N_f), choose_σ a w = a ⟨w, hw⟩)
    (hg_cond : ∀ a : N_f → S,
      μ (multiFiber N_f (extendOnFinset N_f a)) ≠ 0 →
      Integrable g (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)))
    (g_witness : I → SpinConfig I S → ℝ)
    (g_witness_meas : ∀ y, Measurable (g_witness y))
    (g_witness_local : ∀ y σ τ, σ y = τ y → g_witness y σ = g_witness y τ)
    (g_witness_bound : ∀ y σ, |g_witness y σ| ≤ Bg)
    (g_witness_int : ∀ y, Integrable (g_witness y) μ)
    (g_witness_cond_int : ∀ y a,
      μ (multiFiber N_f (extendOnFinset N_f a)) ≠ 0 →
      Integrable (g_witness y)
        (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)))
    (g_decomp : ∀ σ, g σ = ∑ y ∈ N_g, g_witness y σ)
    (d : I → I → ℕ)
    (h_refl : ∀ x, d x x = 0)
    (h_triangle : ∀ x y z, d x y ≤ d x z + d z y)
    (h_support : ∀ u v, d u v > 1 → influenceCoeff γ u v = 0)
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)| ≤
      2 * Bf * Bg * ∑ x ∈ N_f, ∑ y ∈ N_g, hD.α ^ d y x / (1 - hD.α) := by
  have h1 := covariance_bound_gibbs_multisite γ hD μ hμ f g hf_meas hg_meas
    Bf Bg hBf_nn hBg_nn hBf hBg N_f N_g hf_local hg_local hf hg hfg
    choose_σ h_choose hg_cond g_witness g_witness_meas g_witness_local
    g_witness_bound g_witness_int g_witness_cond_int g_decomp hfinsupp h_dep_F
  have h2 : ∀ x y, neumannSeriesCoeff γ y x ≤ hD.α ^ d y x / (1 - hD.α) :=
    fun x y => neumannSeriesCoeff_nn_dist_bound γ hD d h_refl h_triangle h_support y x
  have h3 : ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x ≤
      ∑ x ∈ N_f, ∑ y ∈ N_g, hD.α ^ d y x / (1 - hD.α) := by
    apply Finset.sum_le_sum; intro x _
    apply Finset.sum_le_sum; intro y _
    exact h2 x y
  have hBfBg_nn : 0 ≤ 2 * Bf * Bg :=
    mul_nonneg (mul_nonneg (by norm_num) hBf_nn) hBg_nn
  calc |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)|
      ≤ 2 * Bf * Bg * ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x := h1
    _ ≤ 2 * Bf * Bg * ∑ x ∈ N_f, ∑ y ∈ N_g, hD.α ^ d y x / (1 - hD.α) :=
        mul_le_mul_of_nonneg_left h3 hBfBg_nn

/-! ## T2-general: Full multi-site covariance bound WITHOUT witness decomposition

This variant removes the `g_witness` decomposition requirement from
`covariance_bound_gibbs_multisite`, instead relying on a direct coupling-based
argument for N_g-local g.

The key technical ingredient is a helper that bounds the integral difference of
an N_g-local function under any coupling by `2·Bg · ∑ y ∈ N_g, P{σ_y ≠ τ_y}`. -/

/-- **Pointwise bound for N_g-local g via set-indicators.** If `g` is
`N_g`-local and `|g| ≤ Bg`, then for any pair `(σ, τ)`:
`|g σ - g τ| ≤ 2·Bg · ∑ y ∈ N_g, 𝟙_{σ y ≠ τ y}`. The indicator is expressed
as a `Set.indicator` over the product space evaluated at `(σ, τ)`. -/
private lemma abs_sub_g_le_sum_indicator_Ng
    (g : SpinConfig I S → ℝ) (Bg : ℝ) (hBg_nn : 0 ≤ Bg)
    (hBg : ∀ σ, |g σ| ≤ Bg)
    (N_g : Finset I)
    (hg_local : ∀ σ τ : SpinConfig I S, (∀ w ∈ N_g, σ w = τ w) → g σ = g τ)
    (σ τ : SpinConfig I S) :
    |g σ - g τ| ≤
      2 * Bg * ∑ y ∈ N_g,
        Set.indicator {q : SpinConfig I S × SpinConfig I S | q.1 y ≠ q.2 y}
          (fun _ => (1 : ℝ)) (σ, τ) := by
  classical
  by_cases hagree : ∀ y ∈ N_g, σ y = τ y
  · -- All coordinates in N_g agree: use locality.
    rw [hg_local σ τ hagree]
    simp only [sub_self, abs_zero]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg ?_)
    intro y _
    exact Set.indicator_nonneg (fun _ _ => by norm_num) _
  · -- Some coordinate differs: use boundedness.
    push_neg at hagree
    obtain ⟨y₀, hy₀N, hy₀ne⟩ := hagree
    have hy₀mem :
        ((σ, τ) : SpinConfig I S × SpinConfig I S) ∈
          {q : SpinConfig I S × SpinConfig I S | q.1 y₀ ≠ q.2 y₀} := hy₀ne
    have h_indicator_ge_one :
        (1 : ℝ) ≤ ∑ y ∈ N_g,
          Set.indicator {q : SpinConfig I S × SpinConfig I S | q.1 y ≠ q.2 y}
            (fun _ => (1 : ℝ)) (σ, τ) := by
      calc (1 : ℝ)
          = Set.indicator
              {q : SpinConfig I S × SpinConfig I S | q.1 y₀ ≠ q.2 y₀}
              (fun _ => (1 : ℝ)) (σ, τ) := by
            rw [Set.indicator_of_mem hy₀mem]
        _ ≤ ∑ y ∈ N_g,
              Set.indicator
                {q : SpinConfig I S × SpinConfig I S | q.1 y ≠ q.2 y}
                (fun _ => (1 : ℝ)) (σ, τ) := by
            apply Finset.single_le_sum
              (f := fun y =>
                Set.indicator
                  {q : SpinConfig I S × SpinConfig I S | q.1 y ≠ q.2 y}
                  (fun _ => (1 : ℝ)) (σ, τ))
              (s := N_g) ?_ hy₀N
            intro y _
            exact Set.indicator_nonneg (fun _ _ => by norm_num) _
    have h_abs_sub : |g σ - g τ| ≤ 2 * Bg := by
      have h1 : |g σ - g τ| ≤ |g σ| + |g τ| := abs_sub _ _
      calc |g σ - g τ|
          ≤ |g σ| + |g τ| := h1
        _ ≤ Bg + Bg := add_le_add (hBg σ) (hBg τ)
        _ = 2 * Bg := by ring
    calc |g σ - g τ|
        ≤ 2 * Bg := h_abs_sub
      _ = 2 * Bg * 1 := by ring
      _ ≤ 2 * Bg * ∑ y ∈ N_g,
            Set.indicator
              {q : SpinConfig I S × SpinConfig I S | q.1 y ≠ q.2 y}
              (fun _ => (1 : ℝ)) (σ, τ) :=
          mul_le_mul_of_nonneg_left h_indicator_ge_one
            (by positivity)

/-- **Integral difference bound for N_g-local g via coupling.**
For any coupling `P` of probability measures `μ₁, μ₂`, an `N_g`-local `g`
bounded by `Bg` satisfies:
`|∫g dμ₁ - ∫g dμ₂| ≤ 2·Bg · ∑ y ∈ N_g, (P{p | p.1 y ≠ p.2 y}).toReal`. -/
lemma local_integral_sub_le_coupling_Ng
    [MeasurableEq S]
    (μ₁ μ₂ : Measure (SpinConfig I S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (P : Measure (SpinConfig I S × SpinConfig I S))
    (hP : IsCoupling P μ₁ μ₂)
    (g : SpinConfig I S → ℝ) (hg_meas : Measurable g)
    (Bg : ℝ) (hBg_nn : 0 ≤ Bg) (hBg : ∀ σ, |g σ| ≤ Bg)
    (hg_int₁ : Integrable g μ₁) (hg_int₂ : Integrable g μ₂)
    (N_g : Finset I)
    (hg_local : ∀ σ τ : SpinConfig I S,
      (∀ w ∈ N_g, σ w = τ w) → g σ = g τ) :
    |∫ σ, g σ ∂μ₁ - ∫ σ, g σ ∂μ₂| ≤
      2 * Bg * ∑ y ∈ N_g,
        (P {p : SpinConfig I S × SpinConfig I S | p.1 y ≠ p.2 y}).toReal := by
  classical
  haveI := hP.isProb
  -- Rewrite both integrals against P using the marginal conditions.
  have h_int_fst : Integrable (fun p : SpinConfig I S × SpinConfig I S => g p.1) P := by
    rw [← hP.fst_marginal] at hg_int₁
    exact (integrable_map_measure (hg_meas.aestronglyMeasurable)
      measurable_fst.aemeasurable).mp hg_int₁
  have h_int_snd : Integrable (fun p : SpinConfig I S × SpinConfig I S => g p.2) P := by
    rw [← hP.snd_marginal] at hg_int₂
    exact (integrable_map_measure (hg_meas.aestronglyMeasurable)
      measurable_snd.aemeasurable).mp hg_int₂
  have hfst : ∫ σ, g σ ∂μ₁ = ∫ p, g p.1 ∂P := by
    rw [← hP.fst_marginal]
    exact integral_map measurable_fst.aemeasurable hg_meas.aestronglyMeasurable
  have hsnd : ∫ σ, g σ ∂μ₂ = ∫ p, g p.2 ∂P := by
    rw [← hP.snd_marginal]
    exact integral_map measurable_snd.aemeasurable hg_meas.aestronglyMeasurable
  rw [hfst, hsnd, ← integral_sub h_int_fst h_int_snd]
  -- Pointwise bound on |g p.1 - g p.2|.
  have h_ptwise : ∀ p : SpinConfig I S × SpinConfig I S,
      |g p.1 - g p.2| ≤
        2 * Bg * ∑ y ∈ N_g,
          Set.indicator {q : SpinConfig I S × SpinConfig I S | q.1 y ≠ q.2 y}
            (fun _ => (1 : ℝ)) p := by
    intro p
    have := abs_sub_g_le_sum_indicator_Ng g Bg hBg_nn hBg N_g hg_local p.1 p.2
    simpa using this
  -- Measurability of the diagonal-disagreement sets.
  have h_meas_ne : ∀ y : I,
      MeasurableSet {p : SpinConfig I S × SpinConfig I S | p.1 y ≠ p.2 y} := by
    intro y
    apply MeasurableSet.compl
    exact measurableSet_eq_fun
      ((measurable_pi_apply y).comp measurable_fst)
      ((measurable_pi_apply y).comp measurable_snd)
  -- Each 𝟙_{p.1 y ≠ p.2 y} is measurable via the indicator of a measurable set.
  have h_meas_indicator : ∀ y : I,
      Measurable (fun p : SpinConfig I S × SpinConfig I S =>
        Set.indicator {q : SpinConfig I S × SpinConfig I S | q.1 y ≠ q.2 y}
          (fun _ => (1 : ℝ)) p) := by
    intro y
    exact (measurable_const.indicator (h_meas_ne y))
  -- Each indicator is integrable under the probability measure P.
  have h_int_indicator : ∀ y ∈ N_g,
      Integrable (fun p : SpinConfig I S × SpinConfig I S =>
        Set.indicator {q : SpinConfig I S × SpinConfig I S | q.1 y ≠ q.2 y}
          (fun _ => (1 : ℝ)) p) P := by
    intro y _
    refine Integrable.of_bound (h_meas_indicator y).aestronglyMeasurable 1
      (ae_of_all _ ?_)
    intro p
    simp only [Real.norm_eq_abs]
    by_cases hp : p ∈ {q : SpinConfig I S × SpinConfig I S | q.1 y ≠ q.2 y}
    · rw [Set.indicator_of_mem hp]; simp
    · rw [Set.indicator_of_notMem hp]; simp
  -- ∫ 𝟙_A dP = P(A).toReal.
  have h_int_indicator_eq : ∀ y,
      ∫ p, Set.indicator {q : SpinConfig I S × SpinConfig I S | q.1 y ≠ q.2 y}
          (fun _ => (1 : ℝ)) p ∂P =
        (P {p : SpinConfig I S × SpinConfig I S | p.1 y ≠ p.2 y}).toReal := by
    intro y
    rw [integral_indicator (h_meas_ne y), setIntegral_const, smul_eq_mul, mul_one]
    rfl
  -- Bound |∫(g∘fst - g∘snd)| using the pointwise bound.
  calc |∫ p, (g p.1 - g p.2) ∂P|
      ≤ ∫ p, |g p.1 - g p.2| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ p, 2 * Bg *
          ∑ y ∈ N_g,
            Set.indicator {q : SpinConfig I S × SpinConfig I S | q.1 y ≠ q.2 y}
              (fun _ => (1 : ℝ)) p ∂P := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ (fun p => abs_nonneg _)
        · -- Integrability of the pointwise upper bound.
          refine Integrable.const_mul ?_ (2 * Bg)
          exact integrable_finset_sum N_g h_int_indicator
        · exact ae_of_all _ h_ptwise
    _ = 2 * Bg * ∫ p, ∑ y ∈ N_g,
          Set.indicator {q : SpinConfig I S × SpinConfig I S | q.1 y ≠ q.2 y}
            (fun _ => (1 : ℝ)) p ∂P := by
        rw [integral_const_mul]
    _ = 2 * Bg * ∑ y ∈ N_g,
          ∫ p, Set.indicator
            {q : SpinConfig I S × SpinConfig I S | q.1 y ≠ q.2 y}
            (fun _ => (1 : ℝ)) p ∂P := by
        congr 1
        rw [integral_finset_sum N_g h_int_indicator]
    _ = 2 * Bg * ∑ y ∈ N_g,
          (P {p : SpinConfig I S × SpinConfig I S | p.1 y ≠ p.2 y}).toReal := by
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        exact h_int_indicator_eq y

/-- **Full two-sided multi-site covariance bound (no witness decomposition).**

Same conclusion as `covariance_bound_gibbs_multisite`, but without requiring
a witness decomposition `g = ∑ y ∈ N_g, g_witness y` with each `g_witness y`
single-site-local. Only requires that `g` be `N_g`-local and bounded by `Bg`.

This is suitable for Wilson plaquette observables
`gaugeReTr (plaquetteHolonomy U p)` where no natural single-site decomposition
exists. -/
theorem covariance_bound_gibbs_multisite_general
    [Inhabited S] [Fintype I] [Fintype S] [MeasurableSingletonClass S]
    [MeasurableEq (SpinConfig I S)]
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (f g : SpinConfig I S → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (Bf Bg : ℝ) (hBf_nn : 0 ≤ Bf) (hBg_nn : 0 ≤ Bg)
    (hBf : ∀ σ, |f σ| ≤ Bf) (hBg : ∀ σ, |g σ| ≤ Bg)
    (N_f N_g : Finset I)
    (hf_local : ∀ σ τ, (∀ w ∈ N_f, σ w = τ w) → f σ = f τ)
    (hg_local : ∀ σ τ, (∀ w ∈ N_g, σ w = τ w) → g σ = g τ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun σ => f σ * g σ) μ)
    (choose_σ : (N_f → S) → SpinConfig I S)
    (h_choose : ∀ a : N_f → S,
      ∀ w (hw : w ∈ N_f), choose_σ a w = a ⟨w, hw⟩)
    (hg_cond : ∀ a : N_f → S,
      μ (multiFiber N_f (extendOnFinset N_f a)) ≠ 0 →
      Integrable g (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)))
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)| ≤
      2 * Bf * Bg * ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x := by
  -- Derive MeasurableEq S from [Fintype S] [MeasurableSingletonClass S].
  haveI : MeasurableEq S := inferInstance
  -- Build the bridge: for each a : N_f → S with positive-mass fiber, the
  -- conditional TV difference on g is bounded by
  -- 2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x.
  -- Strategy: invoke `dobrushin_iterated_coupling_exists` to obtain a
  -- coupling P of (cond μ N_f a) and μ satisfying the coupling-level
  -- contraction, apply `abstract_neumann_iteration_finset` to each δ_y
  -- separately, then combine via `local_integral_sub_le_coupling_Ng`.
  have hCondTV : ∀ a : N_f → S,
      μ (multiFiber N_f (extendOnFinset N_f a)) ≠ 0 →
      |∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) -
        ∫ σ, g σ ∂μ| ≤
        2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by
    intro a hpos
    have hne_top : μ (multiFiber N_f (extendOnFinset N_f a)) ≠ ⊤ :=
      (measure_lt_top μ _).ne
    haveI : IsProbabilityMeasure
        (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) :=
      isProbabilityMeasure_condFiniteSupportMeasure μ N_f _ hpos hne_top
    -- Obtain the coupling P and the coupling-level contraction.
    set T : Set I := {z | z ∉ N_f} with hT_def
    have hdlr₁ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
        (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a) A).toReal =
          ∫ σ, (γ.condDist {z} σ A).toReal
            ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) := by
      intro z hzT A hA
      exact condFiniteSupportMeasure_dlr_at_site γ μ hμ N_f _ hpos z hzT A hA
    have hdlr₂ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
        (μ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ := by
      intro z _ A hA
      exact hμ.dlr {z} A hA
    obtain ⟨P, hP_coup, hP_ineq⟩ :=
      dobrushin_iterated_coupling_exists γ
        (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) μ T
        hdlr₁ hdlr₂ hfinsupp h_dep_F
    haveI := hP_coup.isProb
    set δ : I → ℝ :=
      fun w => (P {p : SpinConfig I S × SpinConfig I S | p.1 w ≠ p.2 w}).toReal
      with hδ_def
    have hδ_nn : ∀ w, 0 ≤ δ w := fun _ => ENNReal.toReal_nonneg
    have hδ_le_one : ∀ w, δ w ≤ 1 := by
      intro w
      have h := prob_le_one (μ := P)
        (s := {p : SpinConfig I S × SpinConfig I S | p.1 w ≠ p.2 w})
      calc (P {p : SpinConfig I S × SpinConfig I S | p.1 w ≠ p.2 w}).toReal
          ≤ (1 : ENNReal).toReal :=
            ENNReal.toReal_mono (by simp) h
        _ = 1 := by simp
    have hcontract : ∀ z, z ∉ N_f → δ z ≤ ∑' w, influenceCoeff γ z w * δ w := by
      intro z hzN
      exact hP_ineq z hzN
    -- For each y ∈ N_g, the Neumann-iteration bound.
    have hδ_le_neu : ∀ y, δ y ≤ ∑ x ∈ N_f, neumannSeriesCoeff γ y x := fun y =>
      abstract_neumann_iteration_finset γ hD N_f δ hδ_nn hδ_le_one hcontract y
    -- Sum over y ∈ N_g.
    have h_sum_le : ∑ y ∈ N_g, δ y ≤
        ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x :=
      Finset.sum_le_sum (fun y _ => hδ_le_neu y)
    -- Apply the coupling-based integral difference helper.
    have h_int_bound :
        |∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) -
            ∫ σ, g σ ∂μ| ≤ 2 * Bg * ∑ y ∈ N_g, δ y :=
      local_integral_sub_le_coupling_Ng
        (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) μ P hP_coup
        g hg_meas Bg hBg_nn hBg
        (hg_cond a hpos) hg N_g hg_local
    -- Chain: 2·Bg · ∑ δ y ≤ 2·Bg · (Neumann sum).
    have hBg2_nn : 0 ≤ 2 * Bg := by positivity
    calc |∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) -
            ∫ σ, g σ ∂μ|
        ≤ 2 * Bg * ∑ y ∈ N_g, δ y := h_int_bound
      _ ≤ 2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x :=
          mul_le_mul_of_nonneg_left h_sum_le hBg2_nn
  -- Apply the multi-site bridge.
  have hK_nn : 0 ≤ 2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by
    refine mul_nonneg (mul_nonneg (by norm_num) hBg_nn) ?_
    exact Finset.sum_nonneg (fun y _ =>
      Finset.sum_nonneg (fun x _ => neumannSeriesCoeff_nonneg γ y x))
  have hswap :
      (∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x) =
      ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x :=
    Finset.sum_comm
  calc |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)|
      ≤ Bf * (2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x) :=
        covariance_bound_via_bridge_multisite μ f g Bf hBf_nn hBf N_f
          hf_local hf hg hfg _ hK_nn hCondTV choose_σ h_choose hg_cond
    _ = 2 * Bf * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by ring
    _ = 2 * Bf * Bg * ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x := by
        rw [hswap]

/-! ## T3-general: Textbook wrapper (no witness decomposition) -/

/-- **Textbook exponential decay wiring for the witness-free covariance bound.**

Specializes `covariance_bound_gibbs_multisite_general` via
`neumannSeriesCoeff_nn_dist_bound` to the textbook `α^{d(y,x)}/(1−α)` form.
This is the calling point for downstream applications (e.g. LGT Wilson
plaquette mass-gap proofs) where the observable is a product of link
variables rather than a sum of link-local terms. -/
theorem covariance_bound_gibbs_multisite_general_nn_dist
    [Inhabited S] [Fintype I] [Fintype S] [MeasurableSingletonClass S]
    [MeasurableEq (SpinConfig I S)]
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (f g : SpinConfig I S → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (Bf Bg : ℝ) (hBf_nn : 0 ≤ Bf) (hBg_nn : 0 ≤ Bg)
    (hBf : ∀ σ, |f σ| ≤ Bf) (hBg : ∀ σ, |g σ| ≤ Bg)
    (N_f N_g : Finset I)
    (hf_local : ∀ σ τ, (∀ w ∈ N_f, σ w = τ w) → f σ = f τ)
    (hg_local : ∀ σ τ, (∀ w ∈ N_g, σ w = τ w) → g σ = g τ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun σ => f σ * g σ) μ)
    (choose_σ : (N_f → S) → SpinConfig I S)
    (h_choose : ∀ a : N_f → S,
      ∀ w (hw : w ∈ N_f), choose_σ a w = a ⟨w, hw⟩)
    (hg_cond : ∀ a : N_f → S,
      μ (multiFiber N_f (extendOnFinset N_f a)) ≠ 0 →
      Integrable g (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)))
    (d : I → I → ℕ)
    (h_refl : ∀ x, d x x = 0)
    (h_triangle : ∀ x y z, d x y ≤ d x z + d z y)
    (h_support : ∀ u v, d u v > 1 → influenceCoeff γ u v = 0)
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)| ≤
      2 * Bf * Bg * ∑ x ∈ N_f, ∑ y ∈ N_g, hD.α ^ d y x / (1 - hD.α) := by
  have h1 := covariance_bound_gibbs_multisite_general γ hD μ hμ f g hf_meas hg_meas
    Bf Bg hBf_nn hBg_nn hBf hBg N_f N_g hf_local hg_local hf hg hfg
    choose_σ h_choose hg_cond hfinsupp h_dep_F
  have h2 : ∀ x y, neumannSeriesCoeff γ y x ≤ hD.α ^ d y x / (1 - hD.α) :=
    fun x y => neumannSeriesCoeff_nn_dist_bound γ hD d h_refl h_triangle h_support y x
  have h3 : ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x ≤
      ∑ x ∈ N_f, ∑ y ∈ N_g, hD.α ^ d y x / (1 - hD.α) := by
    apply Finset.sum_le_sum; intro x _
    apply Finset.sum_le_sum; intro y _
    exact h2 x y
  have hBfBg_nn : 0 ≤ 2 * Bf * Bg :=
    mul_nonneg (mul_nonneg (by norm_num) hBf_nn) hBg_nn
  calc |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)|
      ≤ 2 * Bf * Bg * ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x := h1
    _ ≤ 2 * Bf * Bg * ∑ x ∈ N_f, ∑ y ∈ N_g, hD.α ^ d y x / (1 - hD.α) :=
        mul_le_mul_of_nonneg_left h3 hBfBg_nn

/-! ## Nocount variants

The following variants replace `[Countable S]` with
`[MeasurableEq S]` (or `[MeasurableSingletonClass S] [MeasurableEq S]`),
enabling the Dobrushin covariance bound for uncountable compact Lie
groups like U(n). The coupling axiom `dobrushin_iterated_coupling_exists`
(already weakened to drop `[Countable S]`) provides the coupling-level
contraction, and the Neumann iteration / marginal TV bound proceed
identically.

The main gap is `covariance_bound_via_bridge_multisite`, which uses a
countable tsum fiber decomposition of the measure. For the nocount case
we provide an axiom `covariance_tower_property` expressing the
tower-property decomposition of Cov(f,g) via conditional expectations.
This is a standard measure-theoretic fact (for any sigma-algebra, not
just countable partitions) but its formalization requires disintegration
infrastructure (e.g. `Measure.condKernel`) not currently wired to the
project's `condFiniteSupportMeasure`.

### Axiom: tower property for the multi-site covariance decomposition -/

/-- **Tower property for the multisite covariance decomposition.**

For `f` `N_f`-local with `|f| <= Bf` on a probability space `μ`,
if the conditional-expectation difference of `g` on every
positive-mass multi-fiber `a : N_f -> S` is bounded by `K`, then
`|Cov_μ(f, g)| <= Bf * K`.

This is a consequence of the tower property of conditional expectations:
`E[f * (g - Eg)] = E[f * E[g - Eg | sigma_{N_f}]]` (since `f` is
`σ(N_f)`-measurable) followed by `|...| <= Bf * E[|E[g - Eg | N_f]|]
<= Bf * K`. The countable version `covariance_bound_via_bridge_multisite`
proves this using a tsum over fibers; here we postulate the result
for arbitrary (possibly uncountable) `S`.

**Note.** The original `axiom` version omitted `[Countable S]`, claiming
validity for arbitrary (possibly uncountable) `S`. However, the statement
is false in that generality: for atomless probability measures, every
multi-fiber has measure zero, making `hcond_bound` vacuously true with
`K = 0`, while the covariance can be non-zero. The countability
hypothesis is essential for the tsum-based fiber decomposition.

For uncountable compact spin spaces (e.g. compact Lie groups), the
correct bridge requires Mathlib's `condKernel` disintegration or
`condexp` conditional expectation. The downstream `_nocount` theorems
now also carry `[Countable S]` until that infrastructure is wired. -/
theorem covariance_tower_property
    {I S : Type*} [DecidableEq I] [MeasurableSpace S]
    [Countable S] [MeasurableSingletonClass S] [Inhabited S]
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (f g : SpinConfig I S → ℝ)
    (Bf : ℝ) (hBf_nn : 0 ≤ Bf) (hBf : ∀ σ, |f σ| ≤ Bf)
    (N_f : Finset I)
    (hf_local : ∀ σ τ : SpinConfig I S,
      (∀ w ∈ N_f, σ w = τ w) → f σ = f τ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun σ => f σ * g σ) μ)
    (K : ℝ) (hK_nn : 0 ≤ K)
    (hcond_bound : ∀ a : N_f → S,
      μ (multiFiber N_f (extendOnFinset N_f a)) ≠ 0 →
      |∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) -
          ∫ σ, g σ ∂μ| ≤ K)
    (choose_σ : (N_f → S) → SpinConfig I S)
    (h_choose : ∀ a : N_f → S,
      ∀ w (hw : w ∈ N_f), choose_σ a w = a ⟨w, hw⟩)
    (hg_cond : ∀ a : N_f → S,
      μ (multiFiber N_f (extendOnFinset N_f a)) ≠ 0 →
      Integrable g (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a))) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)| ≤ Bf * K :=
  covariance_bound_via_bridge_multisite μ f g Bf hBf_nn hBf N_f hf_local
    hf hg hfg K hK_nn hcond_bound choose_σ h_choose hg_cond

/-! ### DLR (no countability) -/

/-- **DLR for `condFiniteSupportMeasure` (no countability).**
Same as `condFiniteSupportMeasure_dlr_at_site` with `[Countable S]`
dropped — the proof only uses `[MeasurableSingletonClass S]`. -/
lemma condFiniteSupportMeasure_dlr_at_site_nocount
    [MeasurableSingletonClass S]
    (γ : GibbsSpec I S)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (N_f : Finset I) (a : I → S) (hpos : μ (multiFiber N_f a) ≠ 0)
    (z : I) (hz : z ∉ N_f)
    (A : Set (SpinConfig I S)) (hA : MeasurableSet A) :
    (condFiniteSupportMeasure μ N_f a A).toReal =
    ∫ σ, (γ.condDist {z} σ A).toReal ∂(condFiniteSupportMeasure μ N_f a) := by
  have hfib := measurableSet_multiFiber (I := I) (S := S) N_f a
  have hAfib : MeasurableSet (A ∩ multiFiber N_f a) := hA.inter hfib
  have dlr_mu := hμ.dlr {z} (A ∩ multiFiber N_f a) hAfib
  set h : SpinConfig I S → ℝ := fun σ => (γ.condDist {z} σ A).toReal with hh_def
  set h_int : SpinConfig I S → ℝ :=
    fun σ => (γ.condDist {z} σ (A ∩ multiFiber N_f a)).toReal with hh_int_def
  have h_agree : ∀ σ, σ ∈ multiFiber N_f a → h_int σ = h σ := by
    intro σ hσ
    have hσ' : ∀ w ∈ N_f, σ w = a w := hσ
    show (γ.condDist {z} σ (A ∩ multiFiber N_f a)).toReal =
        (γ.condDist {z} σ A).toReal
    rw [condDist_inter_multiFiber_eq γ z N_f hz σ a hσ' A hA]
  have h_zero_off : ∀ σ, σ ∉ multiFiber N_f a → h_int σ = 0 := by
    intro σ hσ
    have hσ' : ¬ (∀ w ∈ N_f, σ w = a w) := hσ
    show (γ.condDist {z} σ (A ∩ multiFiber N_f a)).toReal = 0
    rw [condDist_inter_multiFiber_eq_zero γ z N_f hz σ a hσ' A]
    simp
  have h_int_eq : ∫ σ, h_int σ ∂μ = ∫ σ in multiFiber N_f a, h σ ∂μ := by
    rw [← integral_indicator hfib]
    apply integral_congr_ae
    filter_upwards with σ
    by_cases hσ : σ ∈ multiFiber N_f a
    · rw [h_agree σ hσ, Set.indicator_of_mem hσ]
    · rw [h_zero_off σ hσ, Set.indicator_of_notMem hσ]
  have hkey : (μ (A ∩ multiFiber N_f a)).toReal =
      ∫ σ in multiFiber N_f a, h σ ∂μ := by
    rw [dlr_mu]; exact h_int_eq
  have hLHS : (condFiniteSupportMeasure μ N_f a A).toReal =
      ((μ (multiFiber N_f a))⁻¹).toReal * (μ (A ∩ multiFiber N_f a)).toReal := by
    simp only [condFiniteSupportMeasure, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hA, ENNReal.toReal_mul,
      Set.inter_comm A (multiFiber N_f a)]
  have hRHS : ∫ σ, h σ ∂(condFiniteSupportMeasure μ N_f a) =
      ((μ (multiFiber N_f a))⁻¹).toReal *
        ∫ σ in multiFiber N_f a, h σ ∂μ := by
    simp only [condFiniteSupportMeasure, integral_smul_measure, smul_eq_mul]
  rw [hLHS, hRHS, hkey]

/-! ### Marginal TV bound (no countability) -/

/-- **Multi-site marginal TV bound (compact spin space).** Same as
`condFiniteSupportMeasure_marginalTvDist_le_neumannSeriesSum` with
`[Fintype S]` replaced by compact-space typeclasses. -/
lemma condFiniteSupportMeasure_marginalTvDist_le_neumannSeriesSum_nocount
    [Fintype I]
    [TopologicalSpace S] [CompactSpace S] [T2Space S] [SecondCountableTopology S]
    [BorelSpace S]
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (N_f : Finset I) (a : I → S) (hpos : μ (multiFiber N_f a) ≠ 0)
    [IsProbabilityMeasure (condFiniteSupportMeasure μ N_f a)]
    (y : I)
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    marginalTvDist (condFiniteSupportMeasure μ N_f a) μ y ≤
      ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by
  -- Derive MeasurableEq from compact + T2 + second-countable + Borel
  haveI : MeasurableEq S := inferInstance
  set T : Set I := {z | z ∉ N_f} with hT_def
  have hdlr₁ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (condFiniteSupportMeasure μ N_f a A).toReal =
        ∫ σ, (γ.condDist {z} σ A).toReal ∂(condFiniteSupportMeasure μ N_f a) := by
    intro z hzT A hA
    exact condFiniteSupportMeasure_dlr_at_site_nocount γ μ hμ N_f a hpos z hzT A hA
  have hdlr₂ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
      (μ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ := by
    intro z _ A hA; exact hμ.dlr {z} A hA
  obtain ⟨P, hP_coup, hP_ineq⟩ :=
    dobrushin_iterated_coupling_exists_compact γ
      (condFiniteSupportMeasure μ N_f a) μ T
      hdlr₁ hdlr₂ hfinsupp h_dep_F
  haveI := hP_coup.isProb
  set δ : I → ℝ :=
    fun w => (P {p : SpinConfig I S × SpinConfig I S | p.1 w ≠ p.2 w}).toReal
  have hδ_nn : ∀ w, 0 ≤ δ w := fun _ => ENNReal.toReal_nonneg
  have hδ_le_one : ∀ w, δ w ≤ 1 := by
    intro w
    calc (P {p : SpinConfig I S × SpinConfig I S | p.1 w ≠ p.2 w}).toReal
        ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) (prob_le_one)
      _ = 1 := by simp
  have hcontract : ∀ z, z ∉ N_f → δ z ≤ ∑' w, influenceCoeff γ z w * δ w :=
    fun z hzN => hP_ineq z hzN
  have hδ_le_neu : δ y ≤ ∑ x ∈ N_f, neumannSeriesCoeff γ y x :=
    abstract_neumann_iteration_finset γ hD N_f δ hδ_nn hδ_le_one hcontract y
  exact le_trans
    (marginalTvDist_le_coupling_site_nocount (condFiniteSupportMeasure μ N_f a) μ P hP_coup y)
    hδ_le_neu

/-! ### condTV bound for single-site g (no countability) -/

/-- **Multi-site condTV bound for single-site g (compact spin space).**
Same as `condTV_bound_multisite_y` with `[Fintype S]` replaced by
compact-space typeclasses. -/
theorem condTV_bound_multisite_y_nocount
    [Inhabited S] [Fintype I]
    [TopologicalSpace S] [CompactSpace S] [T2Space S] [SecondCountableTopology S]
    [BorelSpace S]
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (g : SpinConfig I S → ℝ) (hg_meas : Measurable g)
    (Bg : ℝ) (hBg_nn : 0 ≤ Bg) (hBg : ∀ σ, |g σ| ≤ Bg)
    (N_f : Finset I) (a : I → S) (y : I)
    (hg_local : ∀ σ τ : SpinConfig I S, σ y = τ y → g σ = g τ)
    (hg_int : Integrable g μ)
    (hpos : μ (multiFiber N_f a) ≠ 0)
    (hg_cond_int : Integrable g (condFiniteSupportMeasure μ N_f a))
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    |∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f a) - ∫ σ, g σ ∂μ| ≤
      2 * Bg * ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by
  have hne_top : μ (multiFiber N_f a) ≠ ⊤ := (measure_lt_top μ _).ne
  haveI : IsProbabilityMeasure (condFiniteSupportMeasure μ N_f a) :=
    isProbabilityMeasure_condFiniteSupportMeasure μ N_f a hpos hne_top
  have h1 := local_integral_sub_le_marginalTvDist
    (condFiniteSupportMeasure μ N_f a) μ g y hg_local hg_meas Bg hBg_nn hBg
    hg_cond_int hg_int
  have h2 := condFiniteSupportMeasure_marginalTvDist_le_neumannSeriesSum_nocount
    γ hD μ hμ N_f a hpos y hfinsupp h_dep_F
  calc |∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f a) - ∫ σ, g σ ∂μ|
      ≤ 2 * Bg * marginalTvDist (condFiniteSupportMeasure μ N_f a) μ y := h1
    _ ≤ 2 * Bg * ∑ x ∈ N_f, neumannSeriesCoeff γ y x :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-! ### Multi-site covariance bound (compact spin space, countable) -/

/-- **Full two-sided multi-site covariance bound (compact spin space).**
Same as `covariance_bound_gibbs_multisite_general` with `[Fintype S]`
replaced by compact-space typeclasses.

Uses `covariance_tower_property` for the bridge step.

**Note.** Currently requires `[Countable S]` for the tsum-based fiber
decomposition in `covariance_tower_property`. Removing this hypothesis
requires Mathlib's `condKernel` disintegration infrastructure. -/
theorem covariance_bound_gibbs_multisite_general_nocount
    [Inhabited S] [Fintype I] [Countable S]
    [TopologicalSpace S] [CompactSpace S] [T2Space S] [SecondCountableTopology S]
    [BorelSpace S]
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (f g : SpinConfig I S → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (Bf Bg : ℝ) (hBf_nn : 0 ≤ Bf) (hBg_nn : 0 ≤ Bg)
    (hBf : ∀ σ, |f σ| ≤ Bf) (hBg : ∀ σ, |g σ| ≤ Bg)
    (N_f N_g : Finset I)
    (hf_local : ∀ σ τ, (∀ w ∈ N_f, σ w = τ w) → f σ = f τ)
    (hg_local : ∀ σ τ, (∀ w ∈ N_g, σ w = τ w) → g σ = g τ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun σ => f σ * g σ) μ)
    (choose_σ : (N_f → S) → SpinConfig I S)
    (h_choose : ∀ a : N_f → S,
      ∀ w (hw : w ∈ N_f), choose_σ a w = a ⟨w, hw⟩)
    (hg_cond : ∀ a : N_f → S,
      μ (multiFiber N_f (extendOnFinset N_f a)) ≠ 0 →
      Integrable g (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)))
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)| ≤
      2 * Bf * Bg * ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x := by
  -- Build the conditional TV bridge using the coupling (no countability).
  have hCondTV : ∀ a : N_f → S,
      μ (multiFiber N_f (extendOnFinset N_f a)) ≠ 0 →
      |∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) -
        ∫ σ, g σ ∂μ| ≤
        2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by
    intro a hpos
    have hne_top : μ (multiFiber N_f (extendOnFinset N_f a)) ≠ ⊤ :=
      (measure_lt_top μ _).ne
    haveI : IsProbabilityMeasure
        (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) :=
      isProbabilityMeasure_condFiniteSupportMeasure μ N_f _ hpos hne_top
    set T : Set I := {z | z ∉ N_f} with hT_def
    have hdlr₁ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
        (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a) A).toReal =
          ∫ σ, (γ.condDist {z} σ A).toReal
            ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) := by
      intro z hzT A hA
      exact condFiniteSupportMeasure_dlr_at_site_nocount γ μ hμ N_f _ hpos z hzT A hA
    have hdlr₂ : ∀ z ∈ T, ∀ (A : Set (SpinConfig I S)), MeasurableSet A →
        (μ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ := by
      intro z _ A hA; exact hμ.dlr {z} A hA
    obtain ⟨P, hP_coup, hP_ineq⟩ :=
      dobrushin_iterated_coupling_exists_compact γ
        (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) μ T
        hdlr₁ hdlr₂ hfinsupp h_dep_F
    haveI := hP_coup.isProb
    set δ : I → ℝ :=
      fun w => (P {p : SpinConfig I S × SpinConfig I S | p.1 w ≠ p.2 w}).toReal
    have hδ_nn : ∀ w, 0 ≤ δ w := fun _ => ENNReal.toReal_nonneg
    have hδ_le_one : ∀ w, δ w ≤ 1 := by
      intro w
      calc (P {p : SpinConfig I S × SpinConfig I S | p.1 w ≠ p.2 w}).toReal
          ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) (prob_le_one)
        _ = 1 := by simp
    have hcontract : ∀ z, z ∉ N_f → δ z ≤ ∑' w, influenceCoeff γ z w * δ w :=
      fun z hzN => hP_ineq z hzN
    have hδ_le_neu : ∀ y, δ y ≤ ∑ x ∈ N_f, neumannSeriesCoeff γ y x := fun y =>
      abstract_neumann_iteration_finset γ hD N_f δ hδ_nn hδ_le_one hcontract y
    have h_sum_le : ∑ y ∈ N_g, δ y ≤
        ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x :=
      Finset.sum_le_sum (fun y _ => hδ_le_neu y)
    -- MeasurableEq S is inferred from [SecondCountableTopology S] [T2Space S] [BorelSpace S]
    haveI : MeasurableEq S := inferInstance
    have h_int_bound :
        |∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) -
            ∫ σ, g σ ∂μ| ≤ 2 * Bg * ∑ y ∈ N_g, δ y :=
      local_integral_sub_le_coupling_Ng
        (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) μ P hP_coup
        g hg_meas Bg hBg_nn hBg
        (hg_cond a hpos) hg N_g hg_local
    calc |∫ σ, g σ ∂(condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)) -
            ∫ σ, g σ ∂μ|
        ≤ 2 * Bg * ∑ y ∈ N_g, δ y := h_int_bound
      _ ≤ 2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x :=
          mul_le_mul_of_nonneg_left h_sum_le (by positivity)
  -- Apply the tower-property axiom for the covariance bridge.
  have hK_nn : 0 ≤ 2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by
    refine mul_nonneg (mul_nonneg (by norm_num) hBg_nn) ?_
    exact Finset.sum_nonneg (fun y _ =>
      Finset.sum_nonneg (fun x _ => neumannSeriesCoeff_nonneg γ y x))
  have hswap :
      (∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x) =
      ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x :=
    Finset.sum_comm
  calc |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)|
      ≤ Bf * (2 * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x) :=
        covariance_tower_property μ f g Bf hBf_nn hBf N_f
          hf_local hf hg hfg _ hK_nn hCondTV choose_σ h_choose hg_cond
    _ = 2 * Bf * Bg * ∑ y ∈ N_g, ∑ x ∈ N_f, neumannSeriesCoeff γ y x := by ring
    _ = 2 * Bf * Bg * ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x := by
        rw [hswap]

/-- **Textbook exponential decay wiring (compact spin space).**
Same as `covariance_bound_gibbs_multisite_general_nn_dist` with
`[Fintype S]` replaced by compact-space typeclasses.

**Note.** Currently requires `[Countable S]` — see
`covariance_bound_gibbs_multisite_general_nocount` for details. -/
theorem covariance_bound_gibbs_multisite_general_nn_dist_nocount
    [Inhabited S] [Fintype I] [Countable S]
    [TopologicalSpace S] [CompactSpace S] [T2Space S] [SecondCountableTopology S]
    [BorelSpace S]
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (f g : SpinConfig I S → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (Bf Bg : ℝ) (hBf_nn : 0 ≤ Bf) (hBg_nn : 0 ≤ Bg)
    (hBf : ∀ σ, |f σ| ≤ Bf) (hBg : ∀ σ, |g σ| ≤ Bg)
    (N_f N_g : Finset I)
    (hf_local : ∀ σ τ, (∀ w ∈ N_f, σ w = τ w) → f σ = f τ)
    (hg_local : ∀ σ τ, (∀ w ∈ N_g, σ w = τ w) → g σ = g τ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun σ => f σ * g σ) μ)
    (choose_σ : (N_f → S) → SpinConfig I S)
    (h_choose : ∀ a : N_f → S,
      ∀ w (hw : w ∈ N_f), choose_σ a w = a ⟨w, hw⟩)
    (hg_cond : ∀ a : N_f → S,
      μ (multiFiber N_f (extendOnFinset N_f a)) ≠ 0 →
      Integrable g (condFiniteSupportMeasure μ N_f (extendOnFinset N_f a)))
    (d : I → I → ℕ)
    (h_refl : ∀ x, d x x = 0)
    (h_triangle : ∀ x y z, d x y ≤ d x z + d z y)
    (h_support : ∀ u v, d u v > 1 → influenceCoeff γ u v = 0)
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (B : Set S), MeasurableSet B →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)| ≤
      2 * Bf * Bg * ∑ x ∈ N_f, ∑ y ∈ N_g, hD.α ^ d y x / (1 - hD.α) := by
  have h1 := covariance_bound_gibbs_multisite_general_nocount γ hD μ hμ f g hf_meas hg_meas
    Bf Bg hBf_nn hBg_nn hBf hBg N_f N_g hf_local hg_local hf hg hfg
    choose_σ h_choose hg_cond hfinsupp h_dep_F
  have h2 : ∀ x y, neumannSeriesCoeff γ y x ≤ hD.α ^ d y x / (1 - hD.α) :=
    fun x y => neumannSeriesCoeff_nn_dist_bound γ hD d h_refl h_triangle h_support y x
  have h3 : ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x ≤
      ∑ x ∈ N_f, ∑ y ∈ N_g, hD.α ^ d y x / (1 - hD.α) := by
    apply Finset.sum_le_sum; intro x _
    apply Finset.sum_le_sum; intro y _
    exact h2 x y
  have hBfBg_nn : 0 ≤ 2 * Bf * Bg :=
    mul_nonneg (mul_nonneg (by norm_num) hBf_nn) hBg_nn
  calc |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)|
      ≤ 2 * Bf * Bg * ∑ x ∈ N_f, ∑ y ∈ N_g, neumannSeriesCoeff γ y x := h1
    _ ≤ 2 * Bf * Bg * ∑ x ∈ N_f, ∑ y ∈ N_g, hD.α ^ d y x / (1 - hD.α) :=
        mul_le_mul_of_nonneg_left h3 hBfBg_nn

end CovarianceBoundMultisite

end
