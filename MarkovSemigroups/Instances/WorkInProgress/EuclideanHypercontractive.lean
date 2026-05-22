/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hypercontractivity of the standard Gaussian OU semigroup

Discharges the per-instance hypotheses of `gross_lsi_implies_hypercontractive_of_hypotheses`
(`CoreSemigroupInvariant`, `GeneratorCompat`, `StroockVaropoulos`, `CoreLpL2Approx`)
for the multivariate standard Gaussian Bakry-Émery bundle
`stdGaussianFin_dirichletMarkovSemigroup`, and assembles the resulting
hypercontractivity statement. This eliminates the `gross_lsi_implies_hypercontractive`
axiom from the downstream `gaussian-hilbert` chain.
-/

import MarkovSemigroups.Abstract.GrossODE
import MarkovSemigroups.Diffusion.StroockVaropoulos
import MarkovSemigroups.Instances.WorkInProgress.EuclideanFinBE
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GaussianFin

private theorem partialDeriv_hasCompactSupport {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : HasCompactSupport f) (i : Fin n) :
    HasCompactSupport (partialDeriv i f) := by
  unfold partialDeriv
  simpa using hf.fderiv_apply ℝ (Pi.single i (1 : ℝ))

private theorem secondPartial_hasCompactSupport {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : HasCompactSupport f) (i : Fin n) :
    HasCompactSupport (secondPartial i f) := by
  unfold secondPartial
  simpa [partialDeriv] using
    (partialDeriv_hasCompactSupport (n := n) hf i).fderiv_apply ℝ (Pi.single i (1 : ℝ))

private theorem isCoreFin_of_hasCompactSupport_contDiff {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf_supp : HasCompactSupport f) (hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f) :
    IsCoreFin f := by
  obtain ⟨Mf, hMf⟩ := hf_supp.exists_bound_of_continuous hf_smooth.continuous
  choose M1 hM1 using fun i : Fin n =>
    (partialDeriv_hasCompactSupport (n := n) hf_supp i).exists_bound_of_continuous
      ((hf_smooth.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const).continuous
  choose M2 hM2 using fun i : Fin n =>
    (secondPartial_hasCompactSupport (n := n) hf_supp i).exists_bound_of_continuous
      ((((hf_smooth.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const).fderiv_right
        (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const).continuous
  refine ⟨hf_smooth, |Mf| + ∑ i, |M1 i| + ∑ i, |M2 i|, ?_⟩
  intro x
  have hsum1_nonneg : 0 ≤ ∑ i, |M1 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsum2_nonneg : 0 ≤ ∑ i, |M2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨le_trans (hMf x) ?_, ?_, ?_⟩
  · calc
      Mf ≤ |Mf| := le_abs_self Mf
      _ ≤ |Mf| + ∑ i, |M1 i| + ∑ i, |M2 i| := by linarith
  · intro i
    have hsum : |M1 i| ≤ ∑ j, |M1 j| := by
      simpa using
        (Finset.single_le_sum (f := fun j : Fin n => |M1 j|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    calc
      ‖partialDeriv i f x‖ ≤ M1 i := hM1 i x
      _ ≤ |M1 i| := le_abs_self (M1 i)
      _ ≤ ∑ j, |M1 j| := hsum
      _ ≤ ∑ j, |M1 j| + ∑ j, |M2 j| := by exact le_add_of_nonneg_right hsum2_nonneg
      _ ≤ |Mf| + (∑ j, |M1 j| + ∑ j, |M2 j|) := by
        exact le_add_of_nonneg_left (abs_nonneg Mf)
      _ = |Mf| + ∑ j, |M1 j| + ∑ j, |M2 j| := by ring
  · intro i
    have hsum : |M2 i| ≤ ∑ j, |M2 j| := by
      simpa using
        (Finset.single_le_sum (f := fun j : Fin n => |M2 j|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    calc
      ‖secondPartial i f x‖ ≤ M2 i := hM2 i x
      _ ≤ |M2 i| := le_abs_self (M2 i)
      _ ≤ ∑ j, |M2 j| := hsum
      _ ≤ ∑ j, |M1 j| + ∑ j, |M2 j| := by exact le_add_of_nonneg_left hsum1_nonneg
      _ ≤ |Mf| + (∑ j, |M1 j| + ∑ j, |M2 j|) := by
        exact le_add_of_nonneg_left (abs_nonneg Mf)
      _ = |Mf| + ∑ j, |M1 j| + ∑ j, |M2 j| := by ring

private def smoothCoreSet (n : ℕ) (r : ℝ≥0∞) : Set (Lp ℝ r (γFin n)) :=
  {u | ∃ g : (Fin n → ℝ) → ℝ,
      ((⇑u) : (Fin n → ℝ) → ℝ) =ᵐ[γFin n] g ∧
      HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g}

private theorem smoothCoreSet_dense {n : ℕ} {r : ℝ≥0∞} (hr_top : r ≠ ∞) [Fact (1 ≤ r)] :
    Dense (smoothCoreSet n r) := by
  simpa [smoothCoreSet] using
    (MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (E := Fin n → ℝ) (F := ℝ) (μ := γFin n) (p := r) hr_top)

private theorem smoothCoreSet_eq_toLp {n : ℕ} {r : ℝ≥0∞} {u : Lp ℝ r (γFin n)}
    (hu : u ∈ smoothCoreSet n r) :
    ∃ g : (Fin n → ℝ) → ℝ, HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧
      ∃ hg_mem : MemLp g r (γFin n), u = hg_mem.toLp g := by
  rcases hu with ⟨g, hug, hg_supp, hg_smooth⟩
  have hg_mem : MemLp g r (γFin n) := hg_smooth.continuous.memLp_of_hasCompactSupport hg_supp
  refine ⟨g, hg_supp, hg_smooth, hg_mem, ?_⟩
  rw [Lp.ext_iff]
  exact hug.trans hg_mem.coeFn_toLp.symm

private noncomputable def smoothPosApprox (δ : ℝ) : ℝ → ℝ :=
  fun t => t * Real.smoothTransition (t / δ)

private theorem smoothPosApprox_contDiff {δ : ℝ} (_hδ : δ ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothPosApprox δ) := by
  unfold smoothPosApprox
  simpa using contDiff_id.mul (Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ))

private theorem smoothPosApprox_zero {δ : ℝ} (_hδ : 0 < δ) :
    smoothPosApprox δ 0 = 0 := by
  unfold smoothPosApprox
  simp

private theorem smoothPosApprox_nonneg {δ t : ℝ} (hδ : 0 < δ) :
    0 ≤ smoothPosApprox δ t := by
  rcases le_or_gt t 0 with ht | ht
  · have hdiv : t / δ ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg ht hδ.le
    rw [show smoothPosApprox δ t = 0 by
      unfold smoothPosApprox
      simp [Real.smoothTransition.zero_of_nonpos hdiv]]
  · unfold smoothPosApprox
    exact mul_nonneg ht.le (Real.smoothTransition.nonneg _)

private theorem smoothPosApprox_eq_zero_of_nonpos {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ 0) :
    smoothPosApprox δ t = 0 := by
  have hdiv : t / δ ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg ht hδ.le
  unfold smoothPosApprox
  simp [Real.smoothTransition.zero_of_nonpos hdiv]

private theorem smoothPosApprox_eq_self_of_le {δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) :
    smoothPosApprox δ t = t := by
  have hdiv : 1 ≤ t / δ := by
    rw [le_div_iff₀ hδ]
    simpa using ht
  unfold smoothPosApprox
  simp [Real.smoothTransition.one_of_one_le hdiv]

private theorem abs_sub_smoothPosApprox_le {δ t : ℝ} (hδ : 0 < δ) :
    |max t 0 - smoothPosApprox δ t| ≤ δ := by
  rcases le_or_gt t 0 with ht | ht
  · rw [max_eq_right ht, smoothPosApprox_eq_zero_of_nonpos hδ ht, sub_zero, abs_zero]
    positivity
  · by_cases htd : δ ≤ t
    · rw [max_eq_left ht.le, smoothPosApprox_eq_self_of_le hδ htd, sub_self, abs_zero]
      positivity
    · have htδ : t < δ := lt_of_not_ge htd
      have hs_nonneg : 0 ≤ smoothPosApprox δ t := smoothPosApprox_nonneg hδ
      have hs_le_t : smoothPosApprox δ t ≤ t := by
        unfold smoothPosApprox
        have hst_le : Real.smoothTransition (t / δ) ≤ 1 := Real.smoothTransition.le_one _
        have ht_nonneg : 0 ≤ t := ht.le
        have := mul_le_mul_of_nonneg_left hst_le ht_nonneg
        simpa using this
      rw [max_eq_left ht.le, abs_of_nonneg (sub_nonneg.mpr hs_le_t)]
      linarith

/-- **`CoreSemigroupInvariant` for the standard Gaussian OU semigroup.** The image
`P_t (coreToL2 g)` of a core element is again the `L²`-class of a core function,
namely `ouSemigroupFin t g`. Uses `ouSemigroupFin_preserves_IsCore` (core closure)
and `ouSemigroupFin_ae_eq_of_aeEq` (a.e.-equality respected by the kernel). -/
theorem stdGaussianFin_coreSemigroupInvariant (n : ℕ) :
    CoreSemigroupInvariant (stdGaussianFin_dirichletMarkovSemigroup n) := by
  set D := stdGaussianFin_dirichletMarkovSemigroup n with hD
  intro t ht g hg
  refine ⟨ouSemigroupFin t g, ouSemigroupFin_preserves_IsCore t ht hg, ?_⟩
  refine Lp.ext_iff.mpr ?_
  have hg_ae : ((D.coreToL2 hg : (Fin n → ℝ) → ℝ)) =ᵐ[γFin n] g :=
    (D.IsCore_memLp hg).coeFn_toLp
  have hP : ((D.P t (D.coreToL2 hg) : (Fin n → ℝ) → ℝ))
      =ᵐ[γFin n] ouSemigroupFin t ((D.coreToL2 hg : (Fin n → ℝ) → ℝ)) :=
    ouSemigroupFinLp_coeFn_ae t ht (D.coreToL2 hg)
  have hmid : ouSemigroupFin t ((D.coreToL2 hg : (Fin n → ℝ) → ℝ))
      =ᵐ[γFin n] ouSemigroupFin t g :=
    ouSemigroupFin_ae_eq_of_aeEq t ht hg_ae
  have hg'_ae : ((D.coreToL2 (ouSemigroupFin_preserves_IsCore t ht hg) : (Fin n → ℝ) → ℝ))
      =ᵐ[γFin n] ouSemigroupFin t g :=
    (D.IsCore_memLp (ouSemigroupFin_preserves_IsCore t ht hg)).coeFn_toLp
  exact hP.trans (hmid.trans hg'_ae.symm)

/-- **`GeneratorCompat` for the standard Gaussian OU semigroup.** The generator
element is `ouGeneratorFinLp hf`; the strong-`L²` difference-quotient convergence is
`ouSemigroupFinLp_diffQuot_tendsto`, and the Dirichlet-form pinning
`⟪coreToL2 g, A f⟫ = -energy g f` is the integration-by-parts identity
`ouGeneratorFin_ibp`. All bridges (`P_t = ouSemigroupFinLp`, `coreToL2 = .toLp`,
`energy = ouEnergyFin`) hold definitionally. -/
theorem stdGaussianFin_generatorCompat (n : ℕ) :
    GeneratorCompat (stdGaussianFin_dirichletMarkovSemigroup n) := by
  intro f hf
  refine ⟨ouGeneratorFinLp hf, ?_, ?_⟩
  · exact ouSemigroupFinLp_diffQuot_tendsto (n := n) hf
  · intro g hg
    exact ouGeneratorFin_ibp hf hg

/-- **The Gaussian OU carré-du-champ satisfies the `rpow` chain rule.**
`Γ(uʳ, g) = r·u^{r-1}·Γ(u, g)` for strictly positive core `u`, via the coordinate
chain rule `partialDeriv_rpow`. This is the diffusion property that powers the
Stroock–Varopoulos *equality* (`BakryEmerySpace.stroockVaropoulos_eq`). -/
theorem rpowChainRule (n : ℕ) : (stdGaussianFin.bakryEmerySpace n).RpowChainRule := by
  intro u hu hu_pos g _hg r x
  have hu' : IsCoreFin u := hu
  have hu_ne : ∀ y, u y ≠ 0 := fun y => (hu_pos y).ne'
  show ouGammaFin (fun y => u y ^ r) g x = r * u x ^ (r - 1) * ouGammaFin u g x
  unfold ouGammaFin
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [partialDeriv_rpow i hu'.contDiff hu_ne r]
  ring

/-- **`StroockVaropoulos` for the standard Gaussian OU semigroup.** The orbit's
strict positivity (`ε ≤ u` a.e. ⇒ everywhere, full support) lets the carré-du-champ
chain rule turn S–V into the *equality* `BakryEmerySpace.stroockVaropoulos_eq`
(no `stroock_varopoulos` axiom). The limit `Au` is identified with the generator
`ouGeneratorFinLp hu` by uniqueness, and the right-hand inner product unfolds to
`energy u (u^{q-1})` via `ouGeneratorFin_ibp`. -/
theorem stdGaussianFin_stroockVaropoulos (n : ℕ) :
    StroockVaropoulos (stdGaussianFin_dirichletMarkovSemigroup n) := by
  set D := stdGaussianFin_dirichletMarkovSemigroup n with hD
  intro u hu hu_pos q hq hu_half hu_one Au hAu
  obtain ⟨ε, hε, hu_ge⟩ := hu_pos
  have hu_pos_all : ∀ x, 0 < u x := fun x =>
    lt_of_lt_of_le hε (le_of_ae_le_of_continuous hu.continuous hu_ge x)
  -- `Au` is the OU generator of `u` (unique strong-L² limit of the difference quotient).
  have hAu_eq : Au = ouGeneratorFinLp hu :=
    tendsto_nhds_unique hAu (ouSemigroupFinLp_diffQuot_tendsto (n := n) hu)
  -- The form pairing identity, in `D.coreToL2`/`D.energy` normal form.
  have hibp : (⟪D.coreToL2 hu_one, ouGeneratorFinLp hu⟫_ℝ : ℝ)
      = - D.energy (fun x => u x ^ (q - 1)) u := ouGeneratorFin_ibp hu hu_one
  have hpair : (⟪D.coreToL2 hu_one, -Au⟫_ℝ : ℝ) = D.energy u (fun x => u x ^ (q - 1)) := by
    rw [hAu_eq, inner_neg_right, hibp, neg_neg, D.energy_symm (fun x => u x ^ (q - 1)) u]
  -- Stroock–Varopoulos is an *equality* for the gradient form.
  have hSV : (4 * (q - 1) / q ^ 2) *
        D.energy (fun x => u x ^ (q / 2)) (fun x => u x ^ (q / 2))
      = D.energy u (fun x => u x ^ (q - 1)) :=
    (stdGaussianFin.bakryEmerySpace n).stroockVaropoulos_eq (rpowChainRule n)
      hu hu_pos_all q hq hu_half hu_one
  rw [hpair]
  exact le_of_eq hSV

/-- **`CoreLpL2Approx` for the standard Gaussian OU semigroup.** Approximate a
nonnegative `f ∈ L²(γFin n) ∩ L^p(γFin n)` by smooth compactly supported
functions in the larger exponent `r = max p 2`, pass to positive parts in `L^r`,
replace the hard positive part by the smooth approximation
`t ↦ t * smoothTransition (t / δ)`, then shift by `δ` to obtain strict
positivity. The resulting core sequence converges to `f` in `L^r`, hence also in
`L^p` and `L²` because `γFin n` is a probability measure. -/
theorem stdGaussianFin_coreLpL2Approx (n : ℕ) :
    CoreLpL2Approx (stdGaussianFin_dirichletMarkovSemigroup n) := by
  intro p hp f hf_p hf_nonneg
  let r : ℝ≥0∞ := max (ENNReal.ofReal p) 2
  have h2_le_r : (2 : ℝ≥0∞) ≤ r := le_max_right _ _
  have hp_le_r : ENNReal.ofReal p ≤ r := le_max_left _ _
  have hr_one : (1 : ℝ≥0∞) ≤ r := le_trans (by norm_num) h2_le_r
  have hr_zero : r ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 2) h2_le_r)
  have hr_top : r ≠ ∞ := by
    dsimp [r]
    exact max_ne_top ENNReal.ofReal_ne_top (by norm_num)
  haveI : Fact (1 ≤ r) := ⟨hr_one⟩
  have hf_nonneg_ae : 0 ≤ᵐ[γFin n] ((f : (Fin n → ℝ) → ℝ)) := (Lp.coeFn_nonneg _).mpr hf_nonneg
  have hf_two : MemLp ((f : (Fin n → ℝ) → ℝ)) 2 (γFin n) := Lp.memLp f
  have hf_r : MemLp ((f : (Fin n → ℝ) → ℝ)) r (γFin n) := by
    by_cases hp2 : ENNReal.ofReal p ≤ 2
    · simpa [r, max_eq_right hp2] using hf_two
    · simpa [r, max_eq_left (le_of_not_ge hp2)] using hf_p
  let fr : Lp ℝ r (γFin n) := hf_r.toLp ((f : (Fin n → ℝ) → ℝ))
  let δ : ℕ → ℝ := fun m => (((m : ℝ) + 1)⁻¹)
  have hδ_pos : ∀ m, 0 < δ m := by
    intro m
    positivity
  have hδ_tendsto : Tendsto δ atTop (nhds 0) := by
    simpa [δ, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto
      (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (nhds 0))
  have hδ_enn_tendsto : Tendsto (fun m => ENNReal.ofReal (δ m)) atTop (nhds 0) := by
    simpa using (ENNReal.continuous_ofReal.tendsto 0).comp hδ_tendsto
  let S : Set (Lp ℝ r (γFin n)) := smoothCoreSet n r
  choose u huS huDist using fun m : ℕ =>
    (smoothCoreSet_dense (n := n) (r := r) hr_top).exists_dist_lt fr (hδ_pos m)
  choose h hh_supp hh_smooth hh_mem hu_eq using fun m : ℕ =>
    smoothCoreSet_eq_toLp (n := n) (r := r) (huS m)
  have hu_tendsto : Tendsto u atTop (nhds fr) := by
    refine tendsto_iff_dist_tendsto_zero.2 ?_
    refine squeeze_zero (fun m => dist_nonneg) ?_ hδ_tendsto
    intro m
    exact le_of_lt (by simpa [dist_comm] using huDist m)
  have hh_tendsto : Tendsto (fun m => (hh_mem m).toLp (h m)) atTop (nhds fr) := by
    have hEq : (fun m => (hh_mem m).toLp (h m)) = u := by
      funext m
      exact (hu_eq m).symm
    simpa [hEq] using hu_tendsto
  have hfr_posPart : MeasureTheory.Lp.posPart fr = fr := by
    rw [Lp.ext_iff]
    filter_upwards [MeasureTheory.Lp.coeFn_posPart fr, hf_r.coeFn_toLp, hf_nonneg_ae] with x hx1 hx2 hx3
    rw [hx1, hx2]
    simpa using max_eq_left hx3
  have hpos_tendsto :
      Tendsto (fun m => MeasureTheory.Lp.posPart ((hh_mem m).toLp (h m))) atTop (nhds fr) := by
    simpa [hfr_posPart] using
      (MeasureTheory.Lp.continuous_posPart.tendsto fr).comp hh_tendsto
  let hpos : ℕ → (Fin n → ℝ) → ℝ := fun m x => max (h m x) 0
  have hpos_mem : ∀ m, MemLp (hpos m) r (γFin n) := by
    intro m
    simpa [hpos] using (hh_mem m).pos_part
  have hpos_toLp :
      ∀ m, (hpos_mem m).toLp (hpos m) = MeasureTheory.Lp.posPart ((hh_mem m).toLp (h m)) := by
    intro m
    rw [Lp.ext_iff]
    filter_upwards [(hpos_mem m).coeFn_toLp, MeasureTheory.Lp.coeFn_posPart ((hh_mem m).toLp (h m)),
      (hh_mem m).coeFn_toLp] with x hx1 hx2 hx3
    rw [hx1, hx2, hx3]
  have hpos_r_tendsto :
      Tendsto (fun m => eLpNorm ((hpos m) - ((f : (Fin n → ℝ) → ℝ))) r (γFin n))
        atTop (nhds 0) := by
    have hposLp_tendsto : Tendsto (fun m => (hpos_mem m).toLp (hpos m)) atTop (nhds fr) := by
      simpa [hpos_toLp] using hpos_tendsto
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun m => hpos m) hpos_mem
        ((f : (Fin n → ℝ) → ℝ)) hf_r).mp hposLp_tendsto
  have hpos_r_tendsto' :
      Tendsto (fun m => eLpNorm (((f : (Fin n → ℝ) → ℝ)) - hpos m) r (γFin n))
        atTop (nhds 0) := by
    refine hpos_r_tendsto.congr' ?_
    filter_upwards with m
    rw [show ((f : (Fin n → ℝ) → ℝ) - hpos m) = -((hpos m) - ((f : (Fin n → ℝ) → ℝ))) by
      ext x
      simp [sub_eq_add_neg], eLpNorm_neg]
  let k : ℕ → (Fin n → ℝ) → ℝ := fun m x => smoothPosApprox (δ m) (h m x)
  have hk_supp : ∀ m, HasCompactSupport (k m) := by
    intro m
    simpa [k] using (hh_supp m).comp_left (smoothPosApprox_zero (hδ_pos m))
  have hk_smooth : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (k m) := by
    intro m
    exact (smoothPosApprox_contDiff (ne_of_gt (hδ_pos m))).comp (hh_smooth m)
  have hk_mem : ∀ m, MemLp (k m) r (γFin n) := by
    intro m
    exact (hk_smooth m).continuous.memLp_of_hasCompactSupport (hk_supp m)
  have hk_core : ∀ m, IsCoreFin (k m) := by
    intro m
    exact isCoreFin_of_hasCompactSupport_contDiff (hk_supp m) (hk_smooth m)
  have hk_err_le : ∀ m, eLpNorm (hpos m - k m) r (γFin n) ≤ ENNReal.ofReal (δ m) := by
    intro m
    have hbound : ∀ x, ‖hpos m x - k m x‖ ≤ δ m := by
      intro x
      simpa [hpos, k, Real.norm_eq_abs, sub_eq_add_neg] using
        abs_sub_smoothPosApprox_le (hδ_pos m) (t := h m x)
    calc
      eLpNorm (hpos m - k m) r (γFin n)
          ≤ eLpNorm (fun _ : Fin n → ℝ => δ m) r (γFin n) :=
        eLpNorm_mono_ae_real <| Filter.Eventually.of_forall hbound
      _ = ENNReal.ofReal (δ m) := by
        rw [eLpNorm_const' (c := δ m) hr_zero hr_top]
        simp [measure_univ, Real.enorm_of_nonneg (hδ_pos m).le]
  have hk_r_tendsto :
      Tendsto (fun m => eLpNorm (((f : (Fin n → ℝ) → ℝ)) - k m) r (γFin n))
        atTop (nhds 0) := by
    have hsum_tendsto :
        Tendsto
          (fun m =>
            eLpNorm (((f : (Fin n → ℝ) → ℝ)) - hpos m) r (γFin n) + ENNReal.ofReal (δ m))
          atTop (nhds 0) := by
      simpa using hpos_r_tendsto'.add hδ_enn_tendsto
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum_tendsto ?_ ?_
    · intro m
      exact bot_le
    · intro m
      have hsplit :
          (((f : (Fin n → ℝ) → ℝ)) - k m) =
            (((f : (Fin n → ℝ) → ℝ)) - hpos m) + (hpos m - k m) := by
        ext x
        simp [sub_eq_add_neg]
      calc
        eLpNorm (((f : (Fin n → ℝ) → ℝ)) - k m) r (γFin n)
            = eLpNorm ((((f : (Fin n → ℝ) → ℝ)) - hpos m) + (hpos m - k m)) r (γFin n) := by
              rw [hsplit]
        _ ≤ eLpNorm (((f : (Fin n → ℝ) → ℝ)) - hpos m) r (γFin n)
              + eLpNorm (hpos m - k m) r (γFin n) :=
            eLpNorm_add_le
              ((hf_r.aestronglyMeasurable.sub (hpos_mem m).aestronglyMeasurable))
              ((hpos_mem m).aestronglyMeasurable.sub (hk_mem m).aestronglyMeasurable)
              hr_one
        _ ≤ eLpNorm (((f : (Fin n → ℝ) → ℝ)) - hpos m) r (γFin n) + ENNReal.ofReal (δ m) := by
            gcongr
            exact hk_err_le m
  let g : ℕ → (Fin n → ℝ) → ℝ := fun m x => k m x + δ m
  have hg_core : ∀ m, IsCoreFin (g m) := by
    intro m
    simpa [g] using IsCoreFin_add (hk_core m) (IsCoreFin_const (n := n) (δ m))
  have hg_mem_r : ∀ m, MemLp (g m) r (γFin n) := by
    intro m
    refine MemLp.of_bound (hg_core m).stronglyMeasurable.aestronglyMeasurable ?B ?hB
    · exact (hg_core m).bound_exists.choose
    · exact Filter.Eventually.of_forall (hg_core m).bound_exists.choose_spec
  have hconst_tendsto :
      Tendsto (fun m => eLpNorm (fun _ : Fin n → ℝ => δ m) r (γFin n)) atTop (nhds 0) := by
    refine hδ_enn_tendsto.congr' ?_
    filter_upwards with m
    rw [eLpNorm_const' (c := δ m) hr_zero hr_top]
    simp [measure_univ, Real.enorm_of_nonneg (hδ_pos m).le]
  have hg_r_tendsto :
      Tendsto (fun m => eLpNorm (((f : (Fin n → ℝ) → ℝ)) - g m) r (γFin n))
        atTop (nhds 0) := by
    have hsum_tendsto :
        Tendsto
          (fun m =>
            eLpNorm (((f : (Fin n → ℝ) → ℝ)) - k m) r (γFin n)
              + eLpNorm (fun _ : Fin n → ℝ => δ m) r (γFin n))
          atTop (nhds 0) := by
      simpa using hk_r_tendsto.add hconst_tendsto
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum_tendsto ?_ ?_
    · intro m
      exact bot_le
    · intro m
      have hsplit :
          (((f : (Fin n → ℝ) → ℝ)) - g m) =
            (((f : (Fin n → ℝ) → ℝ)) - k m) + (fun _ : Fin n → ℝ => -δ m) := by
        ext x
        simp [g]
        ring
      have hconst_neg :
          eLpNorm (fun _ : Fin n → ℝ => -δ m) r (γFin n) =
            eLpNorm (fun _ : Fin n → ℝ => δ m) r (γFin n) := by
        convert (eLpNorm_neg (f := fun _ : Fin n → ℝ => δ m) (p := r) (μ := γFin n)) using 2
      calc
        eLpNorm (((f : (Fin n → ℝ) → ℝ)) - g m) r (γFin n)
            = eLpNorm ((((f : (Fin n → ℝ) → ℝ)) - k m) + fun _ : Fin n → ℝ => -δ m) r (γFin n) := by
              rw [hsplit]
        _ ≤ eLpNorm (((f : (Fin n → ℝ) → ℝ)) - k m) r (γFin n)
              + eLpNorm (fun _ : Fin n → ℝ => -δ m) r (γFin n) :=
            eLpNorm_add_le
              ((hf_r.aestronglyMeasurable.sub (hk_mem m).aestronglyMeasurable))
              aestronglyMeasurable_const hr_one
        _ = eLpNorm (((f : (Fin n → ℝ) → ℝ)) - k m) r (γFin n)
              + eLpNorm (fun _ : Fin n → ℝ => δ m) r (γFin n) := by
            rw [hconst_neg]
  refine ⟨g, hg_core, ?_, ?_, ?_⟩
  · intro m
    refine ⟨δ m, hδ_pos m, ?_⟩
    intro x
    dsimp [g]
    linarith [smoothPosApprox_nonneg (hδ_pos m) (t := h m x)]
  · have hp_tendsto_le :
        ∀ m,
          eLpNorm (((f : (Fin n → ℝ) → ℝ)) - g m) (ENNReal.ofReal p) (γFin n)
            ≤ eLpNorm (((f : (Fin n → ℝ) → ℝ)) - g m) r (γFin n) := by
      intro m
      exact eLpNorm_le_eLpNorm_of_exponent_le hp_le_r
        ((hf_r.aestronglyMeasurable.sub (hg_core m).stronglyMeasurable.aestronglyMeasurable))
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg_r_tendsto
        (fun m => bot_le) hp_tendsto_le
  · have htwo_tendsto_le :
        ∀ m,
          eLpNorm (((f : (Fin n → ℝ) → ℝ)) - g m) 2 (γFin n)
            ≤ eLpNorm (((f : (Fin n → ℝ) → ℝ)) - g m) r (γFin n) := by
      intro m
      exact eLpNorm_le_eLpNorm_of_exponent_le h2_le_r
        ((hf_r.aestronglyMeasurable.sub (hg_core m).stronglyMeasurable.aestronglyMeasurable))
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg_r_tendsto
        (fun m => bot_le) htwo_tendsto_le

/-- The standard Gaussian Bakry-Émery bundle satisfies the log-Sobolev inequality
with constant `1`, inherited from `stdGaussianFin.bakryEmerySpace`. -/
theorem stdGaussianFin_satisfiesLogSobolev (n : ℕ) :
    (stdGaussianFin_dirichletMarkovSemigroup n).SatisfiesLogSobolev 1 :=
  BakryEmerySpace.satisfiesLogSobolev (be := stdGaussianFin.bakryEmerySpace n)

/-- **Hypercontractivity of the standard Gaussian OU semigroup at `ρ = 1`.**

Assembles the LSI with the four discharged hypotheses
(`CoreSemigroupInvariant`, `GeneratorCompat`, `StroockVaropoulos`, `CoreLpL2Approx`)
through the *proved* theorem `gross_lsi_implies_hypercontractive_of_hypotheses`.
Crucially this does **not** use the `gross_lsi_implies_hypercontractive` axiom, so
it eliminates that axiom from the downstream `gaussian-hilbert` chain. -/
theorem stdGaussianFin_isHypercontractive (n : ℕ) :
    (stdGaussianFin_dirichletMarkovSemigroup n).toMarkovSemigroup.IsHypercontractive 1 :=
  gross_lsi_implies_hypercontractive_of_hypotheses
    (stdGaussianFin_dirichletMarkovSemigroup n) 1 one_pos
    (stdGaussianFin_satisfiesLogSobolev n)
    (stdGaussianFin_coreSemigroupInvariant n)
    (stdGaussianFin_generatorCompat n)
    (stdGaussianFin_stroockVaropoulos n)
    (stdGaussianFin_coreLpL2Approx n)

end GaussianFin
