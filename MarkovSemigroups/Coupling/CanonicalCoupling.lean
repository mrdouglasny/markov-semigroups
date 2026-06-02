/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Canonical Maximal Coupling and Dobrushin Coupling Existence

## Part 1: Canonical maximal coupling for countable spaces

For `[Countable S] [MeasurableSingletonClass S]`, the maximal coupling
of probability measures mu, nu on S is given by the *explicit formula*:

  P = (mu inf nu).map(diag) + c^{-1} . (mu - mu inf nu).prod(nu - mu inf nu)

where `c = 1 - (mu inf nu)(univ)` is the residual mass (= tvNorm).

This construction avoids the non-constructive `.choose` used in the
general `maximalCoupling` and provides:
- Explicit formula (no Axiom of Choice)
- Parametric Giry measurability: if `f, g : X -> Measure S` are
  measurable (in the Giry sigma-algebra), then
  `x |-> canonicalMaximalCoupling (f x) (g x)` is measurable.

## Part 2: Dobrushin iterated coupling existence

The Dobrushin iterated coupling theorem: for probability measures mu_1, mu_2
on a product space SpinConfig I S that both satisfy DLR at sites in T,
there exists a joint coupling P with per-site contraction.

This is Dobrushin (1968), Lemma 2; Georgii (1988), Proposition 8.7.

References:
- Dobrushin (1968), "Description of a random field by means of
  conditional probabilities and conditions of its regularity", Lemma 2.
- Georgii (1988), *Gibbs Measures and Phase Transitions*, Prop 8.7.
- Lindvall, *Lectures on the Coupling Method*, Wiley, 1992.
-/

import MarkovSemigroups.Coupling.TVCoupling
import MarkovSemigroups.Dobrushin.Specification
import MarkovSemigroups.Dobrushin.Uniqueness

open MeasureTheory Set

noncomputable section

variable {S : Type*} [MeasurableSpace S]

/-! ## Part 1: Canonical maximal coupling for countable spaces -/

/-! ### Step 1: Measure inf on singletons for countable spaces -/

/-- For countable spaces with `MeasurableSingletonClass`, the infimum
measure on a singleton equals the minimum of the two measures on that
singleton: `(mu inf nu) {a} = min (mu {a}) (nu {a})`.

This is a key simplification: the general `Measure.inf_apply` gives
an infimum over all partitions, but for singletons the optimal
partition is trivial. -/
theorem measureInf_singleton [Countable S] [MeasurableSingletonClass S]
    (μ ν : Measure S) (a : S) :
    (μ ⊓ ν) {a} = min (μ {a}) (ν {a}) := by
  rw [Measure.inf_apply (measurableSet_singleton a)]
  apply le_antisymm
  · -- sInf ≤ min: take t = {a} and t = empty
    have hbdd : BddBelow {m | ∃ t, m = μ (t ∩ {a}) + ν (tᶜ ∩ {a})} :=
      ⟨0, fun m ⟨_, hm⟩ => hm ▸ zero_le⟩
    apply le_min
    · exact csInf_le hbdd ⟨{a}, by simp⟩
    · exact csInf_le hbdd ⟨∅, by simp⟩
  · -- min ≤ sInf: for any partition t, mu(t cap {a}) + nu(t^c cap {a}) >= min
    have hne : {m | ∃ t, m = μ (t ∩ {a}) + ν (tᶜ ∩ {a})}.Nonempty :=
      ⟨μ (Set.univ ∩ {a}) + ν (Set.univᶜ ∩ {a}), Set.univ, rfl⟩
    apply le_csInf hne
    rintro m ⟨t, rfl⟩
    by_cases ha : a ∈ t
    · have h1 : t ∩ {a} = {a} := inter_eq_right.mpr (singleton_subset_iff.mpr ha)
      have h2 : tᶜ ∩ {a} = ∅ := by
        rw [eq_empty_iff_forall_notMem]; intro x ⟨hxc, hxa⟩
        exact hxc (mem_singleton_iff.mp hxa ▸ ha)
      rw [h1, h2, measure_empty, add_zero]
      exact min_le_left _ _
    · have h1 : t ∩ {a} = ∅ := by
        rw [eq_empty_iff_forall_notMem]; intro x ⟨hxt, hxa⟩
        exact ha (mem_singleton_iff.mp hxa ▸ hxt)
      have h2 : tᶜ ∩ {a} = {a} :=
        inter_eq_right.mpr (singleton_subset_iff.mpr (mem_compl ha))
      rw [h1, h2, measure_empty, zero_add]
      exact min_le_right _ _

/-- `mu inf nu` is dominated by `mu`. -/
theorem measureInf_le_left (μ ν : Measure S) (A : Set S) (hA : MeasurableSet A) :
    (μ ⊓ ν) A ≤ μ A :=
  Measure.le_iff.mp (inf_le_left (a := μ) (b := ν)) A hA

/-- `mu inf nu` is dominated by `nu`. -/
theorem measureInf_le_right (μ ν : Measure S) (A : Set S) (hA : MeasurableSet A) :
    (μ ⊓ ν) A ≤ ν A :=
  Measure.le_iff.mp (inf_le_right (a := μ) (b := ν)) A hA

/-! ### Step 2: The canonical maximal coupling -/

/-- The **canonical maximal coupling** of two probability measures on a
countable measurable space.

For `[Countable S] [MeasurableSingletonClass S]`:

  P = (mu inf nu).map(diag) + c^{-1} . resid_mu.prod(resid_nu)

where:
- `diag x = (x, x)` is the diagonal embedding
- `resid_mu = mu - mu inf nu` is the residual of mu
- `resid_nu = nu - mu inf nu` is the residual of nu
- `c = resid_mu(univ) = tvNorm(mu, nu)` is the residual mass

On the overlap (mass = 1 - tvNorm), both components agree.
On the residual (mass = tvNorm), they are independent draws
from the normalized residuals.

This is the same coupling as `maximalCoupling` from TVCoupling.lean,
but given by an *explicit formula* rather than via `.choose`. The
explicit formula enables parametric measurability proofs. -/
noncomputable def canonicalMaximalCoupling
    [Countable S] [MeasurableSingletonClass S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Measure (S × S) :=
  let overlap := μ ⊓ ν
  let residμ := μ - overlap
  let residν := ν - overlap
  let c := residμ Set.univ
  -- Diagonal part: overlap pushed to the diagonal
  overlap.map (fun a => (a, a)) +
  -- Off-diagonal part: product of residuals, normalized
  c⁻¹ • (residμ.prod residν)

/-! ### Step 3: Basic properties -/

/-- The overlap `mu inf nu` is a finite measure when mu and nu are
probability measures. -/
instance measureInf_isFiniteMeasure
    (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (μ ⊓ ν) :=
  ⟨lt_of_le_of_lt (Measure.le_iff.mp inf_le_left _ MeasurableSet.univ) (measure_lt_top μ _)⟩

/-- The residual `mu - mu inf nu` is a finite measure. -/
instance residual_isFiniteMeasure
    (μ ν : Measure S) [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ - μ ⊓ ν) := by
  constructor
  calc (μ - μ ⊓ ν) Set.univ
      ≤ μ Set.univ := Measure.sub_le Set.univ
    _ < ⊤ := measure_lt_top μ Set.univ

/-- The residual measures have equal total mass. -/
theorem residual_mass_eq
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (μ - μ ⊓ ν) Set.univ = (ν - μ ⊓ ν) Set.univ := by
  have hle_μ : μ ⊓ ν ≤ μ := inf_le_left
  have hle_ν : μ ⊓ ν ≤ ν := inf_le_right
  rw [Measure.sub_apply MeasurableSet.univ hle_μ,
      Measure.sub_apply MeasurableSet.univ hle_ν]
  have hμ : μ Set.univ = 1 := measure_univ
  have hν : ν Set.univ = 1 := measure_univ
  rw [hμ, hν]

/-- The diagonal embedding is measurable. -/
theorem measurable_diag : Measurable (fun a : S => (a, a)) :=
  Measurable.prodMk measurable_id measurable_id

/-- The overlap is dominated by both measures. -/
theorem overlap_le_left (μ ν : Measure S) : μ ⊓ ν ≤ μ := inf_le_left

/-- The overlap is dominated by both measures. -/
theorem overlap_le_right (μ ν : Measure S) : μ ⊓ ν ≤ ν := inf_le_right

/-! ### Step 4: Marginal proofs -/

/-- Helper: `c⁻¹ • (c • m) = m` when c is finite, handling c = 0 (m = 0). -/
private lemma inv_smul_smul_measure {c : ENNReal} (hc_ne_top : c ≠ ⊤)
    (m : Measure S) (hm : c = 0 → m = 0) :
    c⁻¹ • (c • m) = m := by
  by_cases hc0 : c = 0
  · rw [hm hc0, hc0]; simp
  · rw [smul_smul, ENNReal.inv_mul_cancel hc0 hc_ne_top, one_smul]

/-- The first marginal of the canonical coupling equals mu. -/
theorem canonicalMaximalCoupling_fst [Countable S] [MeasurableSingletonClass S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (canonicalMaximalCoupling μ ν).map Prod.fst = μ := by
  unfold canonicalMaximalCoupling
  -- Step 1: map distributes over addition
  rw [Measure.map_add _ _ measurable_fst]
  -- Step 2: diagonal part
  have hd : ((μ ⊓ ν).map (fun a => (a, a))).map Prod.fst = μ ⊓ ν := by
    rw [Measure.map_map measurable_fst measurable_diag]; convert Measure.map_id using 2
  rw [hd, Measure.map_smul]
  have hp : ((μ - μ ⊓ ν).prod (ν - μ ⊓ ν)).map Prod.fst =
      (ν - μ ⊓ ν) Set.univ • (μ - μ ⊓ ν) := Measure.map_fst_prod
  rw [hp, ← residual_mass_eq μ ν,
      inv_smul_smul_measure (measure_ne_top (μ - μ ⊓ ν) Set.univ) (μ - μ ⊓ ν)
        (fun h => Measure.measure_univ_eq_zero.mp h)]
  haveI : IsFiniteMeasure (μ ⊓ ν) := measureInf_isFiniteMeasure μ ν
  show μ ⊓ ν + (μ - μ ⊓ ν) = μ
  ext1 A hA
  simp only [Measure.add_apply]
  rw [Measure.sub_apply hA inf_le_left, add_comm]
  exact tsub_add_cancel_of_le (Measure.le_iff.mp inf_le_left A hA)

/-- The second marginal of the canonical coupling equals nu. -/
theorem canonicalMaximalCoupling_snd [Countable S] [MeasurableSingletonClass S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (canonicalMaximalCoupling μ ν).map Prod.snd = ν := by
  unfold canonicalMaximalCoupling
  rw [Measure.map_add _ _ measurable_snd]
  have hd : ((μ ⊓ ν).map (fun a => (a, a))).map Prod.snd = μ ⊓ ν := by
    rw [Measure.map_map measurable_snd measurable_diag]; convert Measure.map_id using 2
  rw [hd, Measure.map_smul]
  have hp : ((μ - μ ⊓ ν).prod (ν - μ ⊓ ν)).map Prod.snd =
      (μ - μ ⊓ ν) Set.univ • (ν - μ ⊓ ν) := Measure.map_snd_prod
  rw [hp, inv_smul_smul_measure (measure_ne_top (μ - μ ⊓ ν) Set.univ) (ν - μ ⊓ ν)
      (fun h => Measure.measure_univ_eq_zero.mp (residual_mass_eq μ ν ▸ h))]
  haveI : IsFiniteMeasure (μ ⊓ ν) := measureInf_isFiniteMeasure μ ν
  show μ ⊓ ν + (ν - μ ⊓ ν) = ν
  ext1 A hA
  simp only [Measure.add_apply]
  rw [Measure.sub_apply hA inf_le_right, add_comm]
  exact tsub_add_cancel_of_le (Measure.le_iff.mp inf_le_right A hA)

/-! ### Step 5: Total mass = 1 (probability measure) -/

/-- The canonical coupling is a probability measure. -/
instance canonicalMaximalCoupling_isProbabilityMeasure
    [Countable S] [MeasurableSingletonClass S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (canonicalMaximalCoupling μ ν) := by
  constructor
  have h := canonicalMaximalCoupling_fst μ ν
  have h1 : (canonicalMaximalCoupling μ ν).map Prod.fst Set.univ = μ Set.univ :=
    congr_fun (congr_arg DFunLike.coe h) Set.univ
  rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at h1
  rw [h1, measure_univ]

/-- The canonical coupling is a coupling of mu and nu. -/
theorem canonicalMaximalCoupling_isCoupling
    [Countable S] [MeasurableSingletonClass S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsCoupling (canonicalMaximalCoupling μ ν) μ ν where
  fst_marginal := canonicalMaximalCoupling_fst μ ν
  snd_marginal := canonicalMaximalCoupling_snd μ ν

/-! ### Step 6: Disagreement probability = tvNorm -/

/-- The residual measures have disjoint singleton supports: for any atom a,
`residμ({a}) > 0` implies `residν({a}) = 0` and vice versa.

This is because `residμ({a}) = μ({a}) - min(μ({a}), ν({a})) = max(μ({a}) - ν({a}), 0)`
and similarly for residν, so they can't both be positive. -/
theorem residual_singleton_disjoint
    [Countable S] [MeasurableSingletonClass S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a : S) :
    (μ - μ ⊓ ν) {a} * (ν - μ ⊓ ν) {a} = 0 := by
  have hle_μ : μ ⊓ ν ≤ μ := inf_le_left
  have hle_ν : μ ⊓ ν ≤ ν := inf_le_right
  rw [Measure.sub_apply (measurableSet_singleton a) hle_μ,
      Measure.sub_apply (measurableSet_singleton a) hle_ν,
      measureInf_singleton]
  -- (μ{a} - min(μ{a}, ν{a})) * (ν{a} - min(μ{a}, ν{a})) = 0
  rcases le_total (μ {a}) (ν {a}) with h | h
  · -- μ{a} ≤ ν{a}: min = ��{a}, so first factor = 0
    rw [min_eq_left h, tsub_self, zero_mul]
  · -- ν{a} ≤ μ{a}: min = ν{a}, so second factor = 0
    rw [min_eq_right h, tsub_self, mul_zero]

/-- The product of residual measures has zero mass on the diagonal.

Since `residμ({a}) * residν({a}) = 0` for all a, the product measure
puts zero mass on {(a,a) | a in S} = diagonal S. -/
theorem residual_prod_diagonal_zero
    [Countable S] [MeasurableSingletonClass S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (μ - μ ⊓ ν).prod (ν - μ ⊓ ν) (diagonal S) = 0 := by
  set residμ := μ - μ ⊓ ν
  set residν := ν - μ ⊓ ν
  -- The diagonal in S x S is the countable union of {(a, a)} for a : S
  have hdiag_eq : diagonal S = ⋃ a : S, {(a, a)} := by
    ext ⟨x, y⟩; simp [diagonal]
  rw [hdiag_eq]
  -- Measure of countable union ≤ sum of measures (equality for disjoint)
  apply le_antisymm _ (zero_le)
  calc (residμ.prod residν) (⋃ a : S, {(a, a)})
      ≤ ∑' a, (residμ.prod residν) {(a, a)} := measure_iUnion_le _
    _ = ∑' a, residμ {a} * residν {a} := by
        congr 1; ext a
        have : ({(a, a)} : Set (S × S)) = {a} ×ˢ {a} := by
          ext ⟨x, y⟩; simp [Prod.mk.injEq]
        rw [this, Measure.prod_prod]
    _ = ∑' _ : S, (0 : ENNReal) := by
        congr 1; ext a; exact residual_singleton_disjoint μ ν a
    _ = 0 := tsum_zero

/-- The canonical coupling achieves the total variation distance:
`P({(a,b) | a != b}) = tvNorm(mu, nu)`.

The diagonal part puts zero mass on {a != b} (since it's supported
on the diagonal). The off-diagonal part has total mass c^2, which
after normalization by c^{-1} gives c = tvNorm. -/
theorem canonicalMaximalCoupling_ne
    [Countable S] [MeasurableSingletonClass S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((canonicalMaximalCoupling μ ν) {p | p.1 ≠ p.2}).toReal = tvNorm μ ν := by
  apply le_antisymm
  · -- P(ne).toReal ≤ tvNorm: direct computation
    -- P(ne) = diag_part(ne) + c⁻¹ • prod_part(ne)
    -- diag_part(ne) = 0, prod_part(ne) = c² (since diag has measure 0)
    -- So P(ne) = c⁻¹ • c² = c, and c.toReal = tvNorm
    unfold canonicalMaximalCoupling
    have hne_meas : MeasurableSet {p : S × S | p.1 ≠ p.2} := measurableSet_diagonal.compl
    -- Diagonal part: 0
    have hdiag_ne : ((μ ⊓ ν).map (fun a => (a, a))) {p : S × S | p.1 ≠ p.2} = 0 := by
      rw [Measure.map_apply measurable_diag hne_meas]
      convert (μ ⊓ ν).empty
      ext x; simp
    -- Product part on {ne} = total mass of product (since diagonal has 0 mass)
    have hprod_ne : ((μ - μ ⊓ ν).prod (ν - μ ⊓ ν)) {p : S × S | p.1 ≠ p.2} =
        ((μ - μ ⊓ ν).prod (ν - μ ⊓ ν)) Set.univ := by
      have hne_eq : {p : S × S | p.1 ≠ p.2} = (diagonal S)ᶜ := by ext ⟨x, y⟩; simp [diagonal]
      rw [hne_eq, ← measure_add_measure_compl measurableSet_diagonal,
          residual_prod_diagonal_zero μ ν, zero_add]
    -- Total mass of product = c²
    have hprod_mass : ((μ - μ ⊓ ν).prod (ν - μ ⊓ ν)) Set.univ =
        (μ - μ ⊓ ν) Set.univ * (ν - μ ⊓ ν) Set.univ := by
      rw [← Set.univ_prod_univ, Measure.prod_prod]
    rw [Measure.add_apply, Measure.smul_apply, hdiag_ne, zero_add, hprod_ne, hprod_mass,
        ← residual_mass_eq μ ν]
    -- Goal: (c⁻¹ * (c * c)).toReal ≤ tvNorm μ ν
    -- c⁻¹ * c * c = c (when c < ⊤)
    have hc_ne_top : (μ - μ ⊓ ν) Set.univ ≠ ⊤ := measure_ne_top (μ - μ ⊓ ν) Set.univ
    by_cases hc0 : (μ - μ ⊓ ν) Set.univ = 0
    · -- c = 0: 0⁻¹ • (0 * 0) = 0, so toReal = 0 ≤ tvNorm
      rw [hc0]; simp only [mul_zero, smul_eq_mul, mul_zero, ENNReal.toReal_zero]
      rw [← maximalCoupling_ne μ ν]; exact ENNReal.toReal_nonneg
    · -- c⁻¹ • (c * c) = c (as ENNReal smul = mul, then cancel)
      rw [smul_eq_mul]
      set c := (μ - μ ⊓ ν) Set.univ with hc_def
      rw [show c⁻¹ * (c * c) = c from by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hc_ne_top, one_mul]]
      -- c.toReal = tvNorm μ ν
      -- c = (μ - μ⊓ν)(univ), and overlapMeasure_mass says (μ⊓ν)(univ).toReal = 1 - tvNorm
      -- so c = μ(univ) - (μ⊓ν)(univ) = 1 - (μ⊓ν)(univ)
      -- and c.toReal = 1 - (μ⊓ν)(univ).toReal = 1 - (1 - tvNorm) = tvNorm
      have hc_real : c.toReal = tvNorm μ ν := by
        rw [hc_def, Measure.sub_apply MeasurableSet.univ inf_le_left]
        rw [ENNReal.toReal_sub_of_le
          (Measure.le_iff.mp inf_le_left Set.univ MeasurableSet.univ)
          (measure_ne_top μ Set.univ)]
        have h_overlap := overlapMeasure_mass μ ν
        unfold overlapMeasure at h_overlap
        rw [measure_univ (μ := μ), ENNReal.toReal_one]
        linarith
      linarith
  · -- tvNorm ≤ P(ne): this follows from tvNorm_le_coupling
    exact tvNorm_le_coupling _ μ ν (canonicalMaximalCoupling_isCoupling μ ν)

/-! ### Step 7: Parametric Giry measurability -/

/-- **Parametric Giry measurability of the canonical coupling.**

For measurable `f g : X -> Measure S` (in the Giry sigma-algebra),
the function `x |-> canonicalMaximalCoupling (f x) (g x)` is measurable.

This is the key result that `.choose`-based `maximalCoupling` cannot provide.
The proof works by showing each operation in the canonical formula
(`inf`, subtraction, `map`, `prod`, scalar multiplication) preserves
measurability of measure-valued functions. -/
-- Helper: for a countable measurable space, μ A = ∑' a, if a ∈ A then μ {a} else 0.
-- This is a convenient reformulation of `tsum_indicator_apply_singleton`.
private lemma measure_eq_tsum_indicator [Countable S] [MeasurableSingletonClass S]
    (μ : Measure S) (A : Set S) (hA : MeasurableSet A) :
    μ A = ∑' a : S, A.indicator (fun a => μ {a}) a :=
  (Measure.tsum_indicator_apply_singleton μ A hA).symm

-- Helper: measurability of evaluation at a singleton for the inf-measure.
-- For countable S, `(f x ⊓ g x) {a} = min (f x {a}) (g x {a})`.
private lemma measurable_inf_singleton
    {X : Type*} [MeasurableSpace X]
    [Countable S] [MeasurableSingletonClass S]
    (f g : X → Measure S) (hf : Measurable f) (hg : Measurable g) (a : S) :
    Measurable (fun x => (f x ⊓ g x) {a}) := by
  simp_rw [measureInf_singleton]
  exact ((Measure.measurable_coe (measurableSet_singleton a)).comp hf).min
    ((Measure.measurable_coe (measurableSet_singleton a)).comp hg)

-- Helper: measurability of the inf-measure evaluation at any measurable set.
-- Uses the countable singleton decomposition `μ A = ∑' a, if a ∈ A then μ {a} else 0`.
private lemma measurable_inf_coe
    {X : Type*} [MeasurableSpace X]
    [Countable S] [MeasurableSingletonClass S]
    (f g : X → Measure S) (hf : Measurable f) (hg : Measurable g)
    (A : Set S) (hA : MeasurableSet A) :
    Measurable (fun x => (f x ⊓ g x) A) := by
  have htsum : ∀ x, (f x ⊓ g x) A =
      ∑' a : S, A.indicator (fun a => (f x ⊓ g x) {a}) a :=
    fun x => measure_eq_tsum_indicator (f x ⊓ g x) A hA
  simp_rw [htsum]
  apply Measurable.ennreal_tsum; intro a
  -- For fixed a, A.indicator (fun a' => (f x ⊓ g x) {a'}) a is either the
  -- inf singleton evaluation or 0, depending on whether a ∈ A.
  by_cases ha : a ∈ A
  · simp only [indicator_of_mem ha]; exact measurable_inf_singleton f g hf hg a
  · simp only [indicator_of_notMem ha]; exact measurable_const

-- Helper: measurability of the residual measure at a singleton.
-- `(f x - f x ⊓ g x) {a} = f x {a} - min(f x {a}, g x {a})`
private lemma measurable_resid_singleton
    {X : Type*} [MeasurableSpace X]
    [Countable S] [MeasurableSingletonClass S]
    (f g : X → Measure S) (hf : Measurable f) (hg : Measurable g)
    [∀ x, IsProbabilityMeasure (f x)] [∀ x, IsFiniteMeasure (g x)] (a : S) :
    Measurable (fun x => (f x - f x ⊓ g x) {a}) := by
  have hsing := measurableSet_singleton a
  have : ∀ x, (f x - f x ⊓ g x) {a} = f x {a} - min (f x {a}) (g x {a}) := by
    intro x
    rw [Measure.sub_apply hsing (overlap_le_left (f x) (g x)), measureInf_singleton]
  simp_rw [this]
  exact (((Measure.measurable_coe hsing).comp hf).sub
    (((Measure.measurable_coe hsing).comp hf).min
     ((Measure.measurable_coe hsing).comp hg)))

-- Helper: measurability of the second residual (g x - f x ⊓ g x) at a singleton.
private lemma measurable_resid_snd_singleton
    {X : Type*} [MeasurableSpace X]
    [Countable S] [MeasurableSingletonClass S]
    (f g : X → Measure S) (hf : Measurable f) (hg : Measurable g)
    [∀ x, IsFiniteMeasure (f x)] [∀ x, IsProbabilityMeasure (g x)] (b : S) :
    Measurable (fun x => (g x - f x ⊓ g x) {b}) := by
  have hsing := measurableSet_singleton b
  have : ∀ x, (g x - f x ⊓ g x) {b} = g x {b} - min (f x {b}) (g x {b}) := by
    intro x
    rw [Measure.sub_apply hsing (overlap_le_right (f x) (g x)), measureInf_singleton]
  simp_rw [this]
  exact (((Measure.measurable_coe hsing).comp hg).sub
    (((Measure.measurable_coe hsing).comp hf).min
     ((Measure.measurable_coe hsing).comp hg)))

theorem canonicalMaximalCoupling_measurable
    {X : Type*} [MeasurableSpace X]
    [Countable S] [MeasurableSingletonClass S]
    (f g : X → Measure S)
    [∀ x, IsProbabilityMeasure (f x)] [∀ x, IsProbabilityMeasure (g x)]
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => canonicalMaximalCoupling (f x) (g x)) := by
  -- Reduce to showing measurability of each set evaluation (Giry measurability)
  apply Measure.measurable_of_measurable_coe
  intro A hA
  show Measurable (fun x => canonicalMaximalCoupling (f x) (g x) A)
  -- Unfold: overlap.map(diag) A + c⁻¹ * (resid_f.prod resid_g) A
  simp only [canonicalMaximalCoupling, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  -- Measurability of c(x)⁻¹ where c(x) = (f x - f x ⊓ g x)(univ)
  have hc_meas : Measurable (fun x => ((f x - f x ⊓ g x) Set.univ)⁻¹) := by
    apply Measurable.inv
    have hc_eq : ∀ x, (f x - f x ⊓ g x) Set.univ = 1 - (f x ⊓ g x) Set.univ := by
      intro x
      haveI : IsFiniteMeasure (f x ⊓ g x) := measureInf_isFiniteMeasure (f x) (g x)
      rw [Measure.sub_apply MeasurableSet.univ (overlap_le_left (f x) (g x)), measure_univ]
    simp_rw [hc_eq]
    exact measurable_const.sub (measurable_inf_coe f g hf hg _ MeasurableSet.univ)
  apply Measurable.add
  · -- Piece 1: x ↦ (f x ⊓ g x).map(diag) A = (f x ⊓ g x) (diag⁻¹' A)
    simp_rw [Measure.map_apply measurable_diag hA]
    exact measurable_inf_coe f g hf hg _ (measurable_diag hA)
  · -- Piece 2: x ↦ c(x)⁻¹ * ((f x - f x ⊓ g x).prod (g x - f x ⊓ g x)) A
    apply Measurable.mul hc_meas
    -- Convert product measure evaluation to a double tsum over singletons.
    -- Step 1: prod_apply gives an integral
    -- Step 2: lintegral_countable' converts to tsum
    -- Step 3: inner measure on a slice decomposes to tsum of singletons
    have hprod_tsum : ∀ x,
        ((f x - f x ⊓ g x).prod (g x - f x ⊓ g x)) A =
        ∑' a : S, (∑' b : S, (Prod.mk a ⁻¹' A).indicator
          (fun b => (g x - f x ⊓ g x) {b}) b) * (f x - f x ⊓ g x) {a} := by
      intro x
      rw [Measure.prod_apply hA, lintegral_countable']
      congr 1; funext a; congr 1
      exact measure_eq_tsum_indicator _ _ (measurable_prodMk_left hA)
    simp_rw [hprod_tsum]
    apply Measurable.ennreal_tsum; intro a
    apply Measurable.mul
    · -- Inner tsum: ∑' b, indicator(slice, resid_g {b})(b)
      apply Measurable.ennreal_tsum; intro b
      by_cases hb : b ∈ (Prod.mk a ⁻¹' A)
      · simp only [indicator_of_mem hb]; exact measurable_resid_snd_singleton f g hf hg b
      · simp only [indicator_of_notMem hb]; exact measurable_const
    · -- Outer term: (f x - f x ⊓ g x) {a}
      exact measurable_resid_singleton f g hf hg a

end
