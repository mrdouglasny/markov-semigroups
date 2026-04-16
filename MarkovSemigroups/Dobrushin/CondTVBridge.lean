/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conditional TV Bridge for the Covariance Bound

Proves the `hCondTV` bridge: for a Gibbs measure mu, y-local observable g
bounded by Bg, site x, and fiber value a with positive mass:

    |integral g d(condSingleSiteMeasure mu x a) - integral g dmu|
      <= 2 * Bg * neumannSeriesCoeff gamma x y

This connects the single-site disintegration (M1) with the Dobrushin
influence propagation (Neumann series) to close the covariance bound chain.

## Strategy

1. Factor y-local functions through the projection sigma -> sigma(y),
   reducing integrals on SpinConfig to integrals on the marginal space S.
2. Apply `tv_integral_bound_abs` on S to bound the marginal integral
   difference by `2 * Bg * marginalTvDist(cond, mu, y)`.
3. Prove the conditional measure satisfies DLR at sites z != x.
4. Use DLR + single-site contraction to bound marginalTvDist.

## References

- Georgii (1988), Gibbs Measures and Phase Transitions, section 8
- Dobrushin (1968), uniqueness via influence matrix
-/

import MarkovSemigroups.Dobrushin.CovarianceBound
import MarkovSemigroups.Convergence.IntegralBounds

open MeasureTheory SingleSiteDisintegration Topology Filter

noncomputable section

variable {I : Type*} [DecidableEq I] {S : Type*} [MeasurableSpace S]

/-! ## Factoring y-local functions through the site projection -/

/-- Lift a SpinConfig function to a single-site function. For y-local `g`,
`liftToSite g y` satisfies `g sigma = liftToSite g y (sigma y)`. -/
def liftToSite (g : SpinConfig I S → ℝ) (y : I) [Inhabited S] : S → ℝ :=
  fun s => g (Function.update (fun _ => default) y s)

omit [MeasurableSpace S] in
/-- `liftToSite g y` agrees with `g` on any config, when `g` is y-local. -/
lemma liftToSite_eq_of_local [Inhabited S]
    (g : SpinConfig I S → ℝ) (y : I)
    (hg_local : ∀ σ τ : SpinConfig I S, σ y = τ y → g σ = g τ)
    (σ : SpinConfig I S) :
    liftToSite g y (σ y) = g σ := by
  unfold liftToSite
  apply hg_local
  simp [Function.update_self]

omit [MeasurableSpace S] in
/-- `g = liftToSite g y circ pi_y` pointwise when `g` is y-local. -/
lemma local_fn_eq_comp_proj [Inhabited S]
    (g : SpinConfig I S → ℝ) (y : I)
    (hg_local : ∀ σ τ : SpinConfig I S, σ y = τ y → g σ = g τ) :
    g = liftToSite g y ∘ (fun σ : SpinConfig I S => σ y) := by
  ext σ; exact (liftToSite_eq_of_local g y hg_local σ).symm

/-- The map `s -> Function.update base y s` is measurable. -/
lemma measurable_update_at (base : SpinConfig I S) (y : I) :
    Measurable (fun s : S => Function.update base y s) :=
  measurable_pi_lambda _ (fun i => by
    by_cases h : i = y
    · subst h
      have : (fun s => (Function.update base i s) i) = id := by
        ext s; simp [Function.update_self]
      rw [this]; exact measurable_id
    · have : (fun s => (Function.update base y s) i) = fun _ => base i := by
        ext s; exact Function.update_of_ne h s base
      rw [this]; exact measurable_const)

/-- `liftToSite g y` is measurable when `g` is. -/
lemma measurable_liftToSite [Inhabited S]
    (g : SpinConfig I S → ℝ) (y : I) (hg : Measurable g) :
    Measurable (liftToSite g y) :=
  hg.comp (measurable_update_at _ y)

omit [MeasurableSpace S] in
/-- `liftToSite g y` inherits the bound of `g`. -/
lemma liftToSite_bound [Inhabited S]
    (g : SpinConfig I S → ℝ) (y : I) (B : ℝ) (hB : ∀ σ, |g σ| ≤ B) :
    ∀ s : S, |liftToSite g y s| ≤ B := fun _ => hB _

/-- For y-local `g`, `integral g dmu = integral (liftToSite g y) d(marginalAtSite mu y)`. -/
lemma integral_local_eq_marginal [Inhabited S]
    (μ : Measure (SpinConfig I S))
    (g : SpinConfig I S → ℝ) (y : I)
    (hg_local : ∀ σ τ : SpinConfig I S, σ y = τ y → g σ = g τ)
    (hg_meas : Measurable g) :
    ∫ σ, g σ ∂μ = ∫ s, liftToSite g y s ∂(marginalAtSite μ y) := by
  have heq : g = liftToSite g y ∘ (fun σ : SpinConfig I S => σ y) :=
    local_fn_eq_comp_proj g y hg_local
  conv_lhs => rw [show (fun σ => g σ) = g from rfl, heq]
  exact (integral_map (measurable_pi_apply y).aemeasurable
    (measurable_liftToSite g y hg_meas).aestronglyMeasurable).symm

/-- Integrability of `liftToSite g y` on the marginal when `g` is integrable. -/
lemma integrable_liftToSite_marginal [Inhabited S]
    (μ : Measure (SpinConfig I S))
    (g : SpinConfig I S → ℝ) (y : I)
    (hg_local : ∀ σ τ : SpinConfig I S, σ y = τ y → g σ = g τ)
    (hg_meas : Measurable g)
    (hg_int : Integrable g μ) :
    Integrable (liftToSite g y) (marginalAtSite μ y) := by
  rw [marginalAtSite, integrable_map_measure
    (measurable_liftToSite g y hg_meas).aestronglyMeasurable
    (measurable_pi_apply y).aemeasurable]
  have heq : liftToSite g y ∘ (fun σ : SpinConfig I S => σ y) = g := by
    ext σ; exact liftToSite_eq_of_local g y hg_local σ
  rwa [heq]

/-! ## Integral bound via marginal TV distance -/

/-- For y-local `g` bounded by `Bg`, the integral difference between
two probability measures is bounded by `2 * Bg * marginalTvDist`. -/
theorem local_integral_sub_le_marginalTvDist
    [Inhabited S]
    (μ₁ μ₂ : Measure (SpinConfig I S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (g : SpinConfig I S → ℝ) (y : I)
    (hg_local : ∀ σ τ : SpinConfig I S, σ y = τ y → g σ = g τ)
    (hg_meas : Measurable g)
    (Bg : ℝ) (hBg_nn : 0 ≤ Bg) (hBg : ∀ σ, |g σ| ≤ Bg)
    (hg_int₁ : Integrable g μ₁) (hg_int₂ : Integrable g μ₂) :
    |∫ σ, g σ ∂μ₁ - ∫ σ, g σ ∂μ₂| ≤ 2 * Bg * marginalTvDist μ₁ μ₂ y := by
  rw [integral_local_eq_marginal μ₁ g y hg_local hg_meas,
      integral_local_eq_marginal μ₂ g y hg_local hg_meas]
  exact tv_integral_bound_abs (marginalAtSite μ₁ y) (marginalAtSite μ₂ y)
    (liftToSite g y) (measurable_liftToSite g y hg_meas) Bg hBg_nn
    (integrable_liftToSite_marginal μ₁ g y hg_local hg_meas hg_int₁)
    (integrable_liftToSite_marginal μ₂ g y hg_local hg_meas hg_int₂)
    (liftToSite_bound g y Bg hBg)
    (marginalTvDist μ₁ μ₂ y) (marginalTvDist_nonneg μ₁ μ₂ y)
    (fun A hA => abs_toReal_sub_le_tvDist (marginalAtSite μ₁ y) (marginalAtSite μ₂ y) A hA)

/-! ## Properness lemmas for condDist at off-site

These show that `gamma.condDist {z} sigma` preserves the fiber
at site x when z != x. This is a consequence of `GibbsSpec.proper`. -/

/-- `gamma.condDist {z} sigma` puts full mass on `fiber x a` when
sigma(x) = a and z != x. -/
lemma condDist_measure_fiber_eq_one [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z x : I) (hzx : z ≠ x)
    (σ : SpinConfig I S) (a : S) (hσ : σ x = a) :
    γ.condDist {z} σ (fiber x a) = 1 := by
  have hproper := γ.proper {z} σ
  have hsub : {τ : SpinConfig I S | ∀ i, i ∉ ({z} : Finset I) → τ i = σ i} ⊆
      fiber x a := by
    intro τ hτ
    simp only [fiber, evalAt, Set.mem_preimage, Set.mem_singleton_iff]
    have := hτ x (by simp [Finset.mem_singleton]; exact hzx.symm)
    rw [this, hσ]
  have h1 := measure_mono (μ := γ.condDist {z} σ) hsub
  rw [hproper] at h1
  exact le_antisymm (prob_le_one (μ := γ.condDist {z} σ) (s := fiber x a)) h1

/-- The complement of `fiber x a` has zero mass under
`gamma.condDist {z} sigma` when sigma(x) = a and z != x. -/
lemma condDist_fiber_compl_eq_zero [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z x : I) (hzx : z ≠ x)
    (σ : SpinConfig I S) (a : S) (hσ : σ x = a) :
    γ.condDist {z} σ (fiber x a)ᶜ = 0 := by
  have h_full := condDist_measure_fiber_eq_one γ z x hzx σ a hσ
  have hfin : γ.condDist {z} σ (fiber x a) ≠ ⊤ := by rw [h_full]; exact ENNReal.one_ne_top
  rw [measure_compl (measurableSet_fiber x a) hfin,
      h_full, (γ.isProb {z} σ).measure_univ, tsub_self]

/-- `gamma.condDist {z} sigma (fiber x a) = 0` when sigma(x) != a and z != x. -/
lemma condDist_fiber_eq_zero
    [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z x : I) (hzx : z ≠ x)
    (σ : SpinConfig I S) (a : S) (hσ : σ x ≠ a) :
    γ.condDist {z} σ (fiber x a) = 0 := by
  have h_full := condDist_measure_fiber_eq_one γ z x hzx σ (σ x) rfl
  have h_compl := condDist_fiber_compl_eq_zero γ z x hzx σ (σ x) rfl
  -- fiber x a ⊆ (fiber x (sigma x))^c since sigma(x) != a
  have hsub : fiber x a ⊆ (fiber x (σ x))ᶜ := by
    intro τ hτ hτ'
    simp [fiber, evalAt, Set.mem_preimage] at hτ hτ'
    exact hσ (hτ'.symm.trans hτ)
  exact le_antisymm (measure_mono hsub |>.trans h_compl.le) (zero_le _)

/-- When z != x and sigma(x) = a, conditioning at {z} preserves the fiber:
gamma.condDist {z} sigma (A ∩ fiber x a) = gamma.condDist {z} sigma A. -/
lemma condDist_inter_fiber_eq
    [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z x : I) (hzx : z ≠ x)
    (σ : SpinConfig I S) (a : S) (hσ : σ x = a)
    (A : Set (SpinConfig I S)) (hA : MeasurableSet A) :
    γ.condDist {z} σ (A ∩ fiber x a) = γ.condDist {z} σ A := by
  -- A = (A ∩ fiber x a) ∪ (A ∩ (fiber x a)^c), disjoint union
  have h_split : γ.condDist {z} σ A =
      γ.condDist {z} σ (A ∩ fiber x a) + γ.condDist {z} σ (A ∩ (fiber x a)ᶜ) := by
    have hdisj : Disjoint (A ∩ fiber x a) (A ∩ (fiber x a)ᶜ) :=
      Set.disjoint_of_subset Set.inter_subset_right Set.inter_subset_right
        disjoint_compl_right
    have hmeas : MeasurableSet (A ∩ (fiber x a)ᶜ) :=
      hA.inter (measurableSet_fiber x a).compl
    have hunion : (A ∩ fiber x a) ∪ (A ∩ (fiber x a)ᶜ) = A := by
      ext τ; simp [Set.mem_inter_iff, em']
    conv_lhs => rw [← hunion]
    exact measure_union hdisj hmeas
  -- The second term is 0
  have h_zero : γ.condDist {z} σ (A ∩ (fiber x a)ᶜ) = 0 :=
    le_antisymm (measure_mono Set.inter_subset_right |>.trans
      (condDist_fiber_compl_eq_zero γ z x hzx σ a hσ).le) (zero_le _)
  -- goal: ... (A ∩ fiber x a) = ... A
  -- h_split: ... A = ... (A ∩ fiber x a) + ... (A ∩ (fiber x a)^c)
  -- h_zero: ... (A ∩ (fiber x a)^c) = 0
  rw [h_zero, add_zero] at h_split
  exact h_split.symm

/-- When z != x and sigma(x) != a, the integrand
gamma.condDist {z} sigma (A ∩ fiber x a) = 0. -/
lemma condDist_inter_fiber_eq_zero
    [MeasurableSingletonClass S]
    (γ : GibbsSpec I S) (z x : I) (hzx : z ≠ x)
    (σ : SpinConfig I S) (a : S) (hσ : σ x ≠ a)
    (A : Set (SpinConfig I S)) :
    γ.condDist {z} σ (A ∩ fiber x a) = 0 :=
  le_antisymm (measure_mono Set.inter_subset_right |>.trans
    (condDist_fiber_eq_zero γ z x hzx σ a hσ).le) (zero_le _)

/-! ## DLR for condSingleSiteMeasure -/

/-- **DLR for condSingleSiteMeasure at sites z != x.**

If mu is a Gibbs measure, then `condSingleSiteMeasure mu x a` satisfies
the DLR equation at singleton {z} for z != x. -/
lemma condSingleSiteMeasure_dlr_at_site
    [Countable S] [MeasurableSingletonClass S]
    (γ : GibbsSpec I S)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (x : I) (a : S) (hpos : μ (fiber x a) ≠ 0)
    (z : I) (hzx : z ≠ x)
    (A : Set (SpinConfig I S)) (hA : MeasurableSet A) :
    (condSingleSiteMeasure μ x a A).toReal =
    ∫ σ, (γ.condDist {z} σ A).toReal ∂(condSingleSiteMeasure μ x a) := by
  -- Unfolding condSingleSiteMeasure:
  --   LHS = (μ(fiber x a))⁻¹.toReal * μ(A ∩ fiber x a).toReal
  --   RHS = (μ(fiber x a))⁻¹.toReal * ∫_{fiber x a} (γ.condDist {z} σ A).toReal dμ
  -- So it suffices to show:
  --   μ(A ∩ fiber x a).toReal = ∫_{fiber x a} (γ.condDist {z} σ A).toReal dμ
  have hfib := measurableSet_fiber (I := I) (S := S) x a
  have hAfib : MeasurableSet (A ∩ fiber x a) := hA.inter hfib
  have hne_top : μ (fiber x a) ≠ ⊤ := (measure_lt_top μ (fiber x a)).ne
  -- The key identity from DLR for μ at {z}, specialized to A ∩ fiber x a:
  have dlr_mu := hμ.dlr {z} (A ∩ fiber x a) hAfib
  -- Define the integrand
  set h : SpinConfig I S → ℝ := fun σ => (γ.condDist {z} σ A).toReal with hh_def
  set h_int : SpinConfig I S → ℝ := fun σ => (γ.condDist {z} σ (A ∩ fiber x a)).toReal
    with hh_int_def
  -- Key pointwise identities:
  -- (a) On fiber x a: h_int σ = h σ
  -- (b) On (fiber x a)ᶜ: h_int σ = 0
  have h_agree : ∀ σ, σ ∈ fiber x a → h_int σ = h σ := by
    intro σ hσ
    simp only [fiber, evalAt, Set.mem_preimage, Set.mem_singleton_iff] at hσ
    show (γ.condDist {z} σ (A ∩ fiber x a)).toReal = (γ.condDist {z} σ A).toReal
    rw [condDist_inter_fiber_eq γ z x hzx σ a hσ A hA]
  have h_zero_off : ∀ σ, σ ∉ fiber x a → h_int σ = 0 := by
    intro σ hσ
    simp only [fiber, evalAt, Set.mem_preimage, Set.mem_singleton_iff] at hσ
    show (γ.condDist {z} σ (A ∩ fiber x a)).toReal = 0
    rw [condDist_inter_fiber_eq_zero γ z x hzx σ a hσ A]
    simp
  -- Thus: ∫ h_int dμ = ∫_{fiber x a} h dμ
  have h_int_eq : ∫ σ, h_int σ ∂μ = ∫ σ in fiber x a, h σ ∂μ := by
    rw [← integral_indicator hfib]
    apply integral_congr_ae
    filter_upwards with σ
    by_cases hσ : σ ∈ fiber x a
    · rw [h_agree σ hσ, Set.indicator_of_mem hσ]
    · rw [h_zero_off σ hσ, Set.indicator_of_notMem hσ]
  -- From DLR: μ(A ∩ fiber x a).toReal = ∫ h_int dμ = ∫_{fiber x a} h dμ
  have hkey : (μ (A ∩ fiber x a)).toReal = ∫ σ in fiber x a, h σ ∂μ := by
    rw [dlr_mu]; exact h_int_eq
  -- Now expand the LHS and RHS of the goal using condSingleSiteMeasure's def.
  -- LHS: (condSingleSiteMeasure μ x a A).toReal
  have hLHS : (condSingleSiteMeasure μ x a A).toReal =
      ((μ (fiber x a))⁻¹).toReal * (μ (A ∩ fiber x a)).toReal := by
    simp only [condSingleSiteMeasure, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hA, ENNReal.toReal_mul, Set.inter_comm A (fiber x a)]
  -- RHS: ∫ h d(condSingleSiteMeasure μ x a)
  have hRHS : ∫ σ, h σ ∂(condSingleSiteMeasure μ x a) =
      ((μ (fiber x a))⁻¹).toReal * ∫ σ in fiber x a, h σ ∂μ := by
    simp only [condSingleSiteMeasure, integral_smul_measure, smul_eq_mul]
  rw [hLHS, hRHS, hkey]

/-! ## Marginal TV bound for condSingleSiteMeasure

The key bridge: conditioning a Gibbs measure mu on sigma(x) = a changes
the y-marginal by at most the resolvent entry neumannSeriesCoeff gamma x y.

### Mathematical argument

Once we know `condSingleSiteMeasure mu x a` satisfies DLR at sites z != x,
the same contraction machinery as `dobrushin_single_site_contraction` applies.

Define delta(z) = marginalTvDist(condSingleSiteMeasure mu x a, mu, z).

- Initial condition: delta(z) <= 1 for all z (trivial TV bound).
  In particular, delta(x) <= 1.
- Contraction at z != x: by DLR at {z} for both measures, and the
  same Lipschitz argument as `dobrushin_single_site_contraction`:
  delta(z) <= sum_w C(z,w) * delta(w).
- Summing over paths: delta(y) <= sum_n (C^n)_{xy} = neumannSeriesCoeff gamma x y.

The formal gap is Steps 2 and 3: applying the Lipschitz argument requires
an abstract version of `marginalTvDist_contraction` that works for
measures satisfying DLR at a single site (not at all sites), and the
path summation requires an abstract Neumann-series contraction for
vectors satisfying a matrix inequality. The DLR at {z} for the
conditional measure is provided by `condSingleSiteMeasure_dlr_at_site`
(proved above, no sorry).
-/

/-! ### Helper: single-site contraction when only one site z has DLR

The key lemma `dobrushin_single_site_contraction` requires both measures to be
full Gibbs measures, but actually only uses `h₁.dlr {z}` and `h₂.dlr {z}` (the
DLR equation at the single site `z`). We inline that proof here with a direct
DLR-at-z hypothesis on `μ₁` only (we only need it for `condSingleSiteMeasure`;
for `μ` we still use its full Gibbs property). -/

/-- DLR-at-z variant of the single-site contraction: if `μ₁` and `μ₂` satisfy
the DLR equation at singleton `{z}` (instead of being full Gibbs measures),
then the same single-site contraction applies. -/
lemma dobrushin_single_site_contraction_of_dlr
    [Countable S] [MeasurableSingletonClass S]
    [MeasurableEq (SpinConfig I S)]
    (γ : GibbsSpec I S)
    (μ₁ μ₂ : Measure (SpinConfig I S))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (z : I)
    (A : Set (SpinConfig I S)) (hA : MeasurableSet A)
    {B : Set S} (hB : MeasurableSet B)
    (hA_cyl : A = (fun σ : SpinConfig I S => σ z) ⁻¹' B)
    (hdlr₁ : (μ₁ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₁)
    (hdlr₂ : (μ₂ A).toReal = ∫ σ, (γ.condDist {z} σ A).toReal ∂μ₂)
    (δ : I → ℝ) (hδ_nn : ∀ w, 0 ≤ δ w)
    (hδ_bound : ∀ (w : I) (B : Set (SpinConfig I S)),
      MeasurableSet B → |(μ₁ B).toReal - (μ₂ B).toReal| ≤ δ w)
    (hfinsupp : (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (σ τ : SpinConfig I S),
      (∀ w ∈ hfinsupp.toFinset, σ w = τ w) →
      (γ.condDist {z} σ A).toReal = (γ.condDist {z} τ A).toReal) :
    |(μ₁ A).toReal - (μ₂ A).toReal| ≤ ∑' w, influenceCoeff γ z w * δ w := by
  rw [hdlr₁, hdlr₂]
  exact condDist_integral_bound γ μ₁ μ₂ z A hA hB hA_cyl δ hδ_nn hδ_bound
    hfinsupp h_dep_F

/-! ### Step 2: the self-consistency inequality at `z ≠ x`.

Define `δ w := marginalTvDist (condSingleSiteMeasure μ x a) μ w`. Since
`condSingleSiteMeasure μ x a` satisfies DLR at `{z}` for `z ≠ x` and `μ`
satisfies DLR at every site, the single-site contraction at `z` gives
`δ z ≤ ∑' w, influenceCoeff γ z w · δ w`. -/

/-- Self-consistency inequality at `z ≠ x`.

The self-consistency inequality `δ z ≤ ∑' w, C(z,w) · δ w` (where
`δ w := marginalTvDist (condSingleSiteMeasure μ x a) μ w`) is a delicate
claim: the single-site contraction `dobrushin_single_site_contraction_of_dlr`
delivers a bound in terms of δ values dominating the FULL TV (not marginal TV),
while here we wish the iteration to close with δ = marginal TV. A direct
proof uses a site-wise coupling refinement that is not yet in-project.

This lemma is the analog of `marginalTvDist_contraction` (which takes full
TV as its δ on the RHS), adapted to the conditional-measure setting with
only DLR at `z`. Its proof via a site-level coupling refinement is left as
a sorry pending that infrastructure. -/
lemma condSingleSiteMeasure_marginalTvDist_contraction_at_nonX
    [Countable S] [MeasurableSingletonClass S]
    [MeasurableEq (SpinConfig I S)]
    (γ : GibbsSpec I S)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (x : I) (a : S) (hpos : μ (fiber x a) ≠ 0)
    [IsProbabilityMeasure (condSingleSiteMeasure μ x a)]
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (A : Set (SpinConfig I S)), MeasurableSet A →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ A).toReal = (γ.condDist {z} τ A).toReal)
    (z : I) (hzx : z ≠ x) :
    marginalTvDist (condSingleSiteMeasure μ x a) μ z ≤
      ∑' w, influenceCoeff γ z w *
        marginalTvDist (condSingleSiteMeasure μ x a) μ w := by
  sorry

/-! ### Step 3: the Neumann-series iteration.

Given the self-consistency inequality `δ z ≤ ∑' w C(z,w) δ w` for `z ≠ x`
and `δ w ≤ 1` for all `w`, conclude `δ y ≤ neumannSeriesCoeff γ y x`.

The proof is by induction: for each `N`,
    `δ y ≤ ∑_{k=0}^{N} (C^k)_{y,x} + ∑' w, (C^N)_{y,w} · δ' w`
where `δ' w = if w = x then 0 else δ w`. The residual `∑' w, (C^N)_{y,w} · δ' w`
is bounded by `α^N → 0`. -/

/-- Residual bound: for `δ' w ∈ [0, 1]`,
`∑' w, (C^N)_{y,w} · δ' w ≤ α^N`. -/
private lemma residual_bound_abstract
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (δ' : I → ℝ) (hδ'_nn : ∀ w, 0 ≤ δ' w) (hδ'_le_one : ∀ w, δ' w ≤ 1)
    (N : ℕ) (y : I) :
    ∑' w, iterateInfluence γ N y w * δ' w ≤ hD.α ^ N := by
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
          ((iterateInfluence_row_summable γ hD N y).congr (fun w => (mul_one _).symm))
    _ = ∑' w, iterateInfluence γ N y w := by
        congr 1; funext w; exact mul_one _
    _ ≤ hD.α ^ N := iterateInfluence_row_sum_bound γ hD N y

/-- Abstract Neumann iteration: a bounded vector satisfying the
self-consistency inequality at all sites except `x` is bounded by the
Neumann-series coefficient indexed at `x`.

TODO: The inductive step is outlined as follows.
1. Define `δ' w := if w = x then 0 else δ w`.
2. By induction on `N`, show
   `δ y ≤ (∑ k ∈ range (N+1), (C^k)_{y,x}) + ∑' w, (C^N)_{y,w} · δ' w`.
3. Take `N → ∞`: partial sum → `neumannSeriesCoeff γ y x`, residual → 0.

The inductive step (from N to N+1) and the final limit are deferred. -/
lemma abstract_neumann_iteration
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (x : I)
    (δ : I → ℝ) (hδ_nn : ∀ w, 0 ≤ δ w) (hδ_le_one : ∀ w, δ w ≤ 1)
    (hcontract : ∀ z, z ≠ x →
      δ z ≤ ∑' w, influenceCoeff γ z w * δ w)
    (y : I) :
    δ y ≤ neumannSeriesCoeff γ y x := by
  classical
  -- δ' w := if w = x then 0 else δ w
  set δ' : I → ℝ := fun w => if w = x then 0 else δ w with hδ'_def
  have hδ'_nn : ∀ w, 0 ≤ δ' w := fun w => by
    by_cases hw : w = x
    · simp [δ', hw]
    · simp [δ', hw]; exact hδ_nn w
  have hδ'_le_one : ∀ w, δ' w ≤ 1 := fun w => by
    by_cases hw : w = x
    · simp [δ', hw]
    · simp [δ', hw]; exact hδ_le_one w
  have hδ'_le_δ : ∀ w, δ' w ≤ δ w := fun w => by
    by_cases hw : w = x
    · simp [δ', hw]; exact hδ_nn x
    · simp [δ', hw]
  -- Key observation: δ w ≤ δ' w + 1_{w = x} pointwise, since δ' w = δ w for
  -- w ≠ x and δ x ≤ 1.
  have hδ_le_δ'_indicator : ∀ w,
      δ w ≤ δ' w + (if w = x then 1 else 0) := fun w => by
    by_cases hw : w = x
    · subst hw; simp [δ']; exact hδ_le_one w
    · simp [δ', hw]
  -- Intermediate lemma: if `z ≠ x`, then
  --   δ z ≤ C(z, x) + ∑' w, C(z, w) · δ' w.
  -- (Obtained by splitting the contraction sum at w = x.)
  have hcontract' : ∀ z, z ≠ x →
      δ z ≤ influenceCoeff γ z x + ∑' w, influenceCoeff γ z w * δ' w := by
    intro z hzx
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
    calc δ z
        ≤ ∑' w, influenceCoeff γ z w * δ w := hcontract z hzx
      _ ≤ ∑' w, influenceCoeff γ z w *
            (δ' w + (if w = x then 1 else 0)) :=
          h1.tsum_le_tsum
            (fun w => mul_le_mul_of_nonneg_left (hδ_le_δ'_indicator w)
              (influenceCoeff_nonneg γ z w))
            (by
              -- Summable of fun w => C(z,w) * (δ' w + if w = x then 1 else 0)
              refine Summable.of_nonneg_of_le
                (fun w => mul_nonneg (influenceCoeff_nonneg γ z w)
                  (add_nonneg (hδ'_nn w) (by split_ifs <;> linarith)))
                (fun w => ?_) (hD.row_summable z)
              have hd' : δ' w + (if w = x then 1 else 0) ≤ 1 := by
                by_cases hw : w = x
                · simp [δ', hw]
                · simp [δ', hw]; exact hδ_le_one w
              calc influenceCoeff γ z w * (δ' w + (if w = x then 1 else 0))
                  ≤ influenceCoeff γ z w * 1 :=
                    mul_le_mul_of_nonneg_left hd'
                      (influenceCoeff_nonneg γ z w)
                _ = influenceCoeff γ z w := mul_one _)
      _ = ∑' w, (influenceCoeff γ z w * δ' w +
            influenceCoeff γ z w * (if w = x then 1 else 0)) := by
          congr 1; funext w; ring
      _ = (∑' w, influenceCoeff γ z w * δ' w) +
            ∑' w, influenceCoeff γ z w * (if w = x then 1 else 0) := by
          -- Summable of the indicator at x
          have h_ind_summ :
              Summable (fun w : I => influenceCoeff γ z w * (if w = x then 1 else 0)) := by
            have heq : (fun w : I => influenceCoeff γ z w * (if w = x then 1 else 0)) =
              fun w => if w = x then influenceCoeff γ z x else 0 := by
              funext w
              by_cases hw : w = x
              · subst hw; simp
              · simp [hw]
            rw [heq]
            exact summable_of_ne_finset_zero (s := {x}) (fun w hw => by
              simp [Finset.mem_singleton] at hw; simp [hw])
          exact Summable.tsum_add h2 h_ind_summ
      _ = (∑' w, influenceCoeff γ z w * δ' w) + influenceCoeff γ z x := by
          congr 1
          rw [tsum_eq_single x]
          · simp
          · intro w hw; simp [hw]
      _ = influenceCoeff γ z x + ∑' w, influenceCoeff γ z w * δ' w := by ring
  -- Inductive bound:
  -- ∀ N, δ y ≤ (∑ k ∈ range (N+1), (C^k)_{y,x}) + ∑' w, (C^N)_{y,w} * δ' w.
  --
  -- The inductive step requires an associativity lemma for `iterateInfluence`
  -- that is not yet in-project: specifically, `∑' w, C(z, w) · (C^n)_{w, x}
  -- = (C^{n+1})_{z, x}` (the "right recursion" of the iterate, complementing
  -- the existing "left recursion" definition). This is a standard consequence
  -- of Fubini for nonneg tsums, but the formalization is non-trivial in the
  -- present infrastructure.
  --
  -- With such a lemma, the induction goes: use `hcontract'` at z = y to step
  -- from N = 0 to N = 1; then at each step, use `hcontract'` at each w ≠ x
  -- in the residual (and the fact that δ' x = 0 eliminates the w = x term).
  -- The associativity lemma pushes the extra factor of C into (C^{n+1}).
  -- Extended self-consistency: δ'(w) ≤ C(w,x) + ∑' z, C(w,z) · δ'(z) for every w.
  -- For w ≠ x this is `hcontract'`. For w = x, both sides are nonneg (LHS = 0).
  have hstep : ∀ w : I,
      δ' w ≤ influenceCoeff γ w x + ∑' z, influenceCoeff γ w z * δ' z := by
    intro w
    by_cases hw : w = x
    · -- δ'(w) = 0 since w = x
      have hδ'w : δ' w = 0 := by simp [δ', hw]
      rw [hδ'w]
      exact add_nonneg (influenceCoeff_nonneg γ w x)
        (tsum_nonneg (fun z =>
          mul_nonneg (influenceCoeff_nonneg γ w z) (hδ'_nn z)))
    · -- w ≠ x: δ'(w) = δ(w); apply hcontract'
      have hδ'w : δ' w = δ w := by simp [δ', hw]
      rw [hδ'w]; exact hcontract' w hw
  -- Summability facts for the induction step.
  -- For each w: ∑' z, C(w,z) · δ'(z) is summable (comparison with C(w,·) row).
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
  -- The induction.
  have h_ind : ∀ N : ℕ,
      δ y ≤ (∑ k ∈ Finset.range (N + 1), iterateInfluence γ k y x) +
        ∑' w, iterateInfluence γ N y w * δ' w := by
    intro N
    induction N with
    | zero =>
      -- Base: RHS = iter^0(y,x) + ∑' w, iter^0(y,w) * δ'(w)
      --           = (if y=x then 1 else 0) + δ'(y)
      have h_tsum_zero :
          ∑' w, iterateInfluence γ 0 y w * δ' w = δ' y := by
        rw [tsum_eq_single y]
        · simp [iterateInfluence_zero]
        · intro w hw
          simp [iterateInfluence_zero, Ne.symm hw]
      have h_sum_zero :
          ∑ k ∈ Finset.range 1, iterateInfluence γ k y x =
            iterateInfluence γ 0 y x := by
        simp
      rw [h_sum_zero, h_tsum_zero, iterateInfluence_zero]
      by_cases hy : y = x
      · subst hy
        have : δ' y = 0 := by simp [δ']
        rw [this]; simp; exact hδ_le_one y
      · have : δ' y = δ y := by simp [δ', hy]
        rw [this]; simp [hy]
    | succ N ih =>
      -- We must show:
      --   δ y ≤ (∑_{k ∈ range(N+2)} iter^k(y,x)) + ∑' w, iter^(N+1)(y,w) * δ'(w)
      -- Suffices (by ih) to show:
      --   ∑' w, iter^N(y,w) * δ'(w)
      --     ≤ iter^(N+1)(y,x) + ∑' w, iter^(N+1)(y,w) * δ'(w)
      -- Strategy: Apply hstep at each w, then use Fubini for the double sum.
      -- Summabilities for tsum manipulations.
      have h_iterN_summ := iterateInfluence_row_summable γ hD N y
      -- ∑' w, iter^N(y,w) * C(w,x) is summable (comparison: * ≤ iter^N(y,w))
      have h_iterN_CwX_summ :
          Summable (fun w => iterateInfluence γ N y w * influenceCoeff γ w x) := by
        refine Summable.of_nonneg_of_le
          (fun w => mul_nonneg (iterateInfluence_nonneg γ N y w)
            (influenceCoeff_nonneg γ w x))
          (fun w => ?_) h_iterN_summ
        calc iterateInfluence γ N y w * influenceCoeff γ w x
            ≤ iterateInfluence γ N y w * 1 :=
              mul_le_mul_of_nonneg_left (influenceCoeff_le_one γ w x)
                (iterateInfluence_nonneg γ N y w)
          _ = iterateInfluence γ N y w := mul_one _
      -- ∑' w, iter^N(y,w) * (∑' z, C(w,z) * δ'(z)) is summable.
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
      -- Summability of ∑' w, iter^(N+1)(y,w) * δ'(w)
      have h_iterSucc_δ'_summ :
          Summable (fun w => iterateInfluence γ (N + 1) y w * δ' w) := by
        refine Summable.of_nonneg_of_le
          (fun w => mul_nonneg (iterateInfluence_nonneg γ (N + 1) y w)
            (hδ'_nn w))
          (fun w => ?_) (iterateInfluence_row_summable γ hD (N + 1) y)
        calc iterateInfluence γ (N + 1) y w * δ' w
            ≤ iterateInfluence γ (N + 1) y w * 1 :=
              mul_le_mul_of_nonneg_left (hδ'_le_one w)
                (iterateInfluence_nonneg γ (N + 1) y w)
          _ = iterateInfluence γ (N + 1) y w := mul_one _
      -- Step 1: termwise inequality
      --   iter^N(y,w) * δ'(w) ≤ iter^N(y,w) * C(w,x) + iter^N(y,w) * ∑' z, C(w,z) * δ'(z)
      have h_termwise : ∀ w,
          iterateInfluence γ N y w * δ' w ≤
            iterateInfluence γ N y w * influenceCoeff γ w x +
            iterateInfluence γ N y w * ∑' z, influenceCoeff γ w z * δ' z := by
        intro w
        calc iterateInfluence γ N y w * δ' w
            ≤ iterateInfluence γ N y w *
                (influenceCoeff γ w x + ∑' z, influenceCoeff γ w z * δ' z) :=
              mul_le_mul_of_nonneg_left (hstep w)
                (iterateInfluence_nonneg γ N y w)
          _ = iterateInfluence γ N y w * influenceCoeff γ w x +
                iterateInfluence γ N y w * ∑' z, influenceCoeff γ w z * δ' z :=
              mul_add _ _ _
      -- Step 2: sum and split the tsum.
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
          Summable (fun w => iterateInfluence γ N y w * influenceCoeff γ w x +
              iterateInfluence γ N y w * ∑' z, influenceCoeff γ w z * δ' z) :=
        h_iterN_CwX_summ.add h_iterN_CwSum_summ
      have h_tsum_bound :
          ∑' w, iterateInfluence γ N y w * δ' w ≤
            (∑' w, iterateInfluence γ N y w * influenceCoeff γ w x) +
            ∑' w, iterateInfluence γ N y w *
              ∑' z, influenceCoeff γ w z * δ' z := by
        calc ∑' w, iterateInfluence γ N y w * δ' w
            ≤ ∑' w, (iterateInfluence γ N y w * influenceCoeff γ w x +
                iterateInfluence γ N y w *
                  ∑' z, influenceCoeff γ w z * δ' z) :=
              h_LHS_summ.tsum_le_tsum h_termwise h_split_summ
          _ = (∑' w, iterateInfluence γ N y w * influenceCoeff γ w x) +
              ∑' w, iterateInfluence γ N y w *
                ∑' z, influenceCoeff γ w z * δ' z :=
            Summable.tsum_add h_iterN_CwX_summ h_iterN_CwSum_summ
      -- Step 3: identify ∑' w, iter^N(y,w) * C(w,x) with iter^(N+1)(y,x) (definition).
      have h_first_eq :
          ∑' w, iterateInfluence γ N y w * influenceCoeff γ w x =
            iterateInfluence γ (N + 1) y x := rfl
      -- Step 4: the second sum equals ∑' z, iter^(N+1)(y,z) * δ'(z). This uses Fubini.
      -- g(w, z) := iter^N(y,w) * C(w,z) * δ'(z)  is summable on I × I.
      -- ∑' w ∑' z g(w,z) = ∑' z ∑' w g(w,z)
      have h_pair_nn : ∀ p : I × I,
          0 ≤ iterateInfluence γ N y p.1 * influenceCoeff γ p.1 p.2 * δ' p.2 := by
        intro p
        exact mul_nonneg
          (mul_nonneg (iterateInfluence_nonneg γ N y p.1)
            (influenceCoeff_nonneg γ p.1 p.2)) (hδ'_nn p.2)
      -- Inner (z)-summability for each w.
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
      -- Outer (w)-summability.
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
      -- Product summability via `summable_prod_of_nonneg`.
      have h_prod_sum : Summable
          (fun p : I × I =>
            iterateInfluence γ N y p.1 * influenceCoeff γ p.1 p.2 * δ' p.2) := by
        rw [summable_prod_of_nonneg h_pair_nn]
        exact ⟨h_inner_sum, h_outer_sum⟩
      -- Inner (w)-summability for each z; use swap/prodComm.
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
          0 ≤ iterateInfluence γ N y p.2 * influenceCoeff γ p.2 p.1 * δ' p.1 := by
        intro p
        exact mul_nonneg
          (mul_nonneg (iterateInfluence_nonneg γ N y p.2)
            (influenceCoeff_nonneg γ p.2 p.1)) (hδ'_nn p.1)
      have h_row_z_sum : ∀ z, Summable
          (fun w => iterateInfluence γ N y w *
            influenceCoeff γ w z * δ' z) :=
        fun z =>
          ((summable_prod_of_nonneg h_pair_nn_swap).mp h_swap_sum).1 z
      -- Fubini swap.
      -- tsum_comm' : ∑' c, ∑' b, f b c = ∑' b, ∑' c, f b c
      -- Here f b c = iter^N(y, b) * C(b, c) * δ'(c), b = w, c = z.
      -- Gives: ∑' z, ∑' w, iter*C*δ' = ∑' w, ∑' z, iter*C*δ'.
      have h_fubini :
          ∑' z, ∑' w, iterateInfluence γ N y w *
              influenceCoeff γ w z * δ' z =
          ∑' w, ∑' z, iterateInfluence γ N y w *
              influenceCoeff γ w z * δ' z :=
        h_prod_sum.tsum_comm' h_inner_sum h_row_z_sum
      -- Clean-up: rewrite the second sum.
      have h_second_eq :
          ∑' w, iterateInfluence γ N y w *
              ∑' z, influenceCoeff γ w z * δ' z =
            ∑' z, iterateInfluence γ (N + 1) y z * δ' z := by
        -- LHS = ∑' w ∑' z (... triple product), swap, factor δ'(z).
        have step1 : ∀ w, iterateInfluence γ N y w *
              ∑' z, influenceCoeff γ w z * δ' z =
              ∑' z, iterateInfluence γ N y w *
                influenceCoeff γ w z * δ' z := by
          intro w
          rw [← tsum_mul_left]
          congr 1; funext z; ring
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
          _ = ∑' z, iterateInfluence γ (N + 1) y z * δ' z := by
              -- ∑' w, iter^N(y,w) * C(w,z) = iter^(N+1)(y,z) by definition
              rfl
      -- Assemble.
      have h_step_final :
          ∑' w, iterateInfluence γ N y w * δ' w ≤
            iterateInfluence γ (N + 1) y x +
            ∑' w, iterateInfluence γ (N + 1) y w * δ' w := by
        rw [← h_first_eq, ← h_second_eq]
        exact h_tsum_bound
      -- Combine with ih: δ y ≤ sum_{k=0}^N iter^k(y,x) + ∑' w, iter^N(y,w) * δ'(w)
      -- ≤ sum_{k=0}^N iter^k(y,x) + iter^(N+1)(y,x) + ∑' w, iter^(N+1)(y,w) * δ'(w).
      -- The first two summands equal ∑_{k ∈ range (N+2)} iter^k(y,x).
      calc δ y
          ≤ (∑ k ∈ Finset.range (N + 1), iterateInfluence γ k y x) +
              ∑' w, iterateInfluence γ N y w * δ' w := ih
        _ ≤ (∑ k ∈ Finset.range (N + 1), iterateInfluence γ k y x) +
              (iterateInfluence γ (N + 1) y x +
                ∑' w, iterateInfluence γ (N + 1) y w * δ' w) := by
            have := h_step_final
            linarith
        _ = (∑ k ∈ Finset.range (N + 1 + 1), iterateInfluence γ k y x) +
              ∑' w, iterateInfluence γ (N + 1) y w * δ' w := by
            rw [show N + 1 + 1 = (N + 1) + 1 from rfl,
                Finset.sum_range_succ _ (N + 1)]
            ring
  -- Residual bound: ∑' w, (C^N)_{y,w} · δ' w ≤ α^N.
  have h_res_bound : ∀ N,
      ∑' w, iterateInfluence γ N y w * δ' w ≤ hD.α ^ N :=
    fun N => residual_bound_abstract γ hD δ' hδ'_nn hδ'_le_one N y
  -- Partial sum converges to neumannSeriesCoeff γ y x.
  have h_partial_sum_tendsto :
      Tendsto (fun N => ∑ k ∈ Finset.range (N + 1), iterateInfluence γ k y x)
        atTop (𝓝 (neumannSeriesCoeff γ y x)) := by
    have h := (neumannSeriesCoeff_summable γ hD y x).hasSum.tendsto_sum_nat
    exact (h.comp (tendsto_add_atTop_nat 1))
  -- Residual tends to 0.
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
  -- RHS total tends to neumann γ y x + 0 = neumann γ y x.
  have h_rhs_tendsto :
      Tendsto
        (fun N => (∑ k ∈ Finset.range (N + 1), iterateInfluence γ k y x) +
          ∑' w, iterateInfluence γ N y w * δ' w)
        atTop (𝓝 (neumannSeriesCoeff γ y x)) := by
    have := h_partial_sum_tendsto.add h_res_tendsto
    simpa using this
  -- Limit comparison: δ y ≤ RHS_N for all N, RHS_N → neumann γ y x, so
  -- δ y ≤ neumann γ y x.
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds h_rhs_tendsto h_ind

lemma condSingleSiteMeasure_marginalTvDist_le_neumannSeriesCoeff
    [Countable S] [MeasurableSingletonClass S]
    [MeasurableEq (SpinConfig I S)]
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (x y : I)
    (a : S) (hpos : μ (fiber x a) ≠ 0)
    [IsProbabilityMeasure (condSingleSiteMeasure μ x a)]
    -- Finite-range structural hypotheses
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (A : Set (SpinConfig I S)), MeasurableSet A →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ A).toReal = (γ.condDist {z} τ A).toReal) :
    marginalTvDist (condSingleSiteMeasure μ x a) μ y ≤
      neumannSeriesCoeff γ y x := by
  -- Apply the abstract Neumann iteration with δ w = marginalTvDist (cond) μ w.
  set δ : I → ℝ := fun w => marginalTvDist (condSingleSiteMeasure μ x a) μ w with hδ_def
  have hδ_nn : ∀ w, 0 ≤ δ w := fun w =>
    marginalTvDist_nonneg (condSingleSiteMeasure μ x a) μ w
  have hδ_le_one : ∀ w, δ w ≤ 1 := fun w =>
    marginalTvDist_le_one (condSingleSiteMeasure μ x a) μ w
  have hcontract : ∀ z, z ≠ x → δ z ≤ ∑' w, influenceCoeff γ z w * δ w :=
    fun z hzx => condSingleSiteMeasure_marginalTvDist_contraction_at_nonX
      γ μ hμ x a hpos hfinsupp h_dep_F z hzx
  exact abstract_neumann_iteration γ hD x δ hδ_nn hδ_le_one hcontract y

/-! ## The condTV bound -/

/-- **The condTV bound.** For a Gibbs measure mu, y-local observable g
bounded by Bg, the conditional expectation difference is bounded:

    |integral g d(condSingleSiteMeasure mu x a) - integral g dmu|
      <= 2 * Bg * neumannSeriesCoeff gamma y x

Used as the bridge `hCondTV` of
`covariance_le_neumannSeriesCoeff` (with the Neumann-series index
swapped to the row-propagation form `(y, x)`). -/
theorem condTV_bound
    [Inhabited S] [Countable S] [MeasurableSingletonClass S]
    [MeasurableEq (SpinConfig I S)]
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (g : SpinConfig I S → ℝ) (hg_meas : Measurable g)
    (Bg : ℝ) (hBg_nn : 0 ≤ Bg) (hBg : ∀ σ, |g σ| ≤ Bg)
    (x y : I)
    (hg_local : ∀ σ τ : SpinConfig I S, σ y = τ y → g σ = g τ)
    (hg_int : Integrable g μ)
    (a : S) (hpos : μ (fiber x a) ≠ 0)
    (hg_cond_int : Integrable g (condSingleSiteMeasure μ x a))
    -- Finite-range structural hypotheses
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (A : Set (SpinConfig I S)), MeasurableSet A →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ A).toReal = (γ.condDist {z} τ A).toReal) :
    |∫ σ, g σ ∂(condSingleSiteMeasure μ x a) - ∫ σ, g σ ∂μ| ≤
      2 * Bg * neumannSeriesCoeff γ y x := by
  have hne_top : μ (fiber x a) ≠ ⊤ := (measure_lt_top μ (fiber x a)).ne
  haveI : IsProbabilityMeasure (condSingleSiteMeasure μ x a) :=
    isProbabilityMeasure_condSingleSiteMeasure μ x a hpos hne_top
  -- Step 1: Bound integral difference by 2*Bg*marginalTvDist
  have h1 := local_integral_sub_le_marginalTvDist _ _ g y hg_local hg_meas Bg hBg_nn hBg
      hg_cond_int hg_int
  -- Step 2: Bound marginalTvDist by neumannSeriesCoeff
  have h2 := condSingleSiteMeasure_marginalTvDist_le_neumannSeriesCoeff γ hD μ hμ x y a hpos
      hfinsupp h_dep_F
  -- Combine
  calc |∫ σ, g σ ∂(condSingleSiteMeasure μ x a) - ∫ σ, g σ ∂μ|
      ≤ 2 * Bg * marginalTvDist (condSingleSiteMeasure μ x a) μ y := h1
    _ ≤ 2 * Bg * neumannSeriesCoeff γ y x :=
        mul_le_mul_of_nonneg_left h2 (by linarith)

/-! ## Unconditional covariance bound

Composes `condTV_bound` with `covariance_le_neumannSeriesCoeff` to
produce the covariance bound without the `hCondTV` bridge hypothesis. -/

/-- **Unconditional covariance bound via Neumann series.**

For a Gibbs measure μ under Dobrushin's condition, with f x-local and
g y-local observables bounded by Bf, Bg:

    |Cov_μ(f, g)| ≤ 2 · Bf · Bg · neumannSeriesCoeff γ y x

No bridge hypothesis needed — the conditional TV bound is supplied
internally via `condTV_bound`.

Note: the Neumann-series index is `(y, x)` — the walk propagates
from `y` (the site of `g`) to `x` (the conditioned site of `f`),
using the row-sum form of the influence matrix. -/
theorem covariance_bound_gibbs
    [Inhabited S] [Countable S] [MeasurableSingletonClass S]
    [MeasurableEq (SpinConfig I S)]
    (γ : GibbsSpec I S) (hD : DobrushinCondition γ)
    (μ : Measure (SpinConfig I S)) [IsProbabilityMeasure μ]
    (hμ : IsGibbsMeasure γ μ)
    (f g : SpinConfig I S → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (Bf Bg : ℝ) (hBf_nn : 0 ≤ Bf) (hBg_nn : 0 ≤ Bg)
    (hBf : ∀ σ, |f σ| ≤ Bf) (hBg : ∀ σ, |g σ| ≤ Bg)
    (x y : I)
    (hf_local : ∀ σ τ, σ x = τ x → f σ = f τ)
    (hg_local : ∀ σ τ, σ y = τ y → g σ = g τ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun σ => f σ * g σ) μ)
    (choose_σ : S → SpinConfig I S) (h_choose : ∀ a, (choose_σ a) x = a)
    (hg_cond : ∀ a, μ (fiber x a) ≠ 0 →
      Integrable g (condSingleSiteMeasure μ x a))
    -- Finite-range structural hypotheses
    (hfinsupp : ∀ z, (Function.support (influenceCoeff γ z ·)).Finite)
    (h_dep_F : ∀ (z : I) (A : Set (SpinConfig I S)), MeasurableSet A →
      ∀ (σ τ : SpinConfig I S), (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ.condDist {z} σ A).toReal = (γ.condDist {z} τ A).toReal) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)| ≤
      2 * Bf * Bg * neumannSeriesCoeff γ y x := by
  -- Build the hCondTV hypothesis using condTV_bound
  have hCondTV : ∀ a : S, μ (fiber x a) ≠ 0 →
      |∫ σ, g σ ∂(condSingleSiteMeasure μ x a) - ∫ σ, g σ ∂μ| ≤
        2 * Bg * neumannSeriesCoeff γ y x := by
    intro a hpos
    exact condTV_bound γ hD μ hμ g hg_meas Bg hBg_nn hBg x y hg_local hg a hpos
      (hg_cond a hpos) hfinsupp h_dep_F
  -- Apply the abstract covariance_bound_via_bridge directly with
  -- K = 2 * Bg * neumannSeriesCoeff γ y x.
  have hK_nn : 0 ≤ 2 * Bg * neumannSeriesCoeff γ y x :=
    mul_nonneg (mul_nonneg (by norm_num) hBg_nn) (neumannSeriesCoeff_nonneg γ y x)
  calc |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * (∫ σ, g σ ∂μ)|
      ≤ Bf * (2 * Bg * neumannSeriesCoeff γ y x) :=
        covariance_bound_via_bridge μ f g Bf hBf_nn hBf x hf_local
          hf hg hfg _ hK_nn hCondTV choose_σ h_choose hg_cond
    _ = 2 * Bf * Bg * neumannSeriesCoeff γ y x := by ring

end
