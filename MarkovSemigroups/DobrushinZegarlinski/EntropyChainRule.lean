/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Entropy Chain Rule (Spatial Sweeping)

This file states and (partially) proves the entropy chain rule used
by Zegarlinski's theorem: for a Gibbs measure `μ` on `SpinConfig Λ ℝ`
with specification `γ`, and a sufficiently integrable nonneg
`g : SpinConfig Λ ℝ → ℝ`,

  Ent_μ(g) ≤ Σ_{x ∈ Λ} ∫ Ent_{γ.condDist {x} σ}(g) dμ(σ).

This is the standard *spatial sweeping* / Doob martingale
decomposition of entropy, BGL §5.7 / Stroock–Zegarlinski 1992 §3.

## Status

* `EntropyIntegrable` — bundled integrability hypotheses.
* `entropy_const`, `entropy_zero` — basic identities (proved).
* `entropy_chain_rule_local` — main theorem, statement is real but
  the proof is currently `sorry` (≈3 pages of measure-theoretic
  bookkeeping). Sub-lemmas:
  - `entropy_decomposition_single_site` — the single-site
    decomposition (S1).
  - `entropy_chain_rule_local` proper — induction over `Λ` using S1.

The `entropy` definition is shared with `LocalLSI.lean`.

## References

* Bakry, Gentil, Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, §5.7.4 (chain-rule formulation of entropy).
* Stroock and Zegarlinski, *Comm. Math. Phys.* 144 (1992), §3.
* Georgii, *Gibbs Measures and Phase Transitions*, §15.
-/

import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Probability.Kernel.MeasurableIntegral
import MarkovSemigroups.DobrushinZegarlinski.LocalLSI

noncomputable section

namespace MarkovSemigroups.DobrushinZegarlinski

open MeasureTheory

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Bundled integrability hypotheses sufficient for the entropy
chain rule: `g` is nonneg, integrable, and `g · log g` is integrable.

Note that `g · log g` is bounded below by `-1/e` for nonneg `g`
(minimum of `t · log t` on `[0, ∞)` is at `t = 1/e`), so integrability
of `g log g` is essentially an upper-tail control on `g log g`. -/
structure EntropyIntegrable
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (g : α → ℝ) : Prop where
  nonneg : 0 ≤ g
  measurable : Measurable g
  integrable : Integrable g μ
  log_integrable : Integrable (fun σ => g σ * Real.log (g σ)) μ

/-! ## Basic identities -/

omit [Fintype Λ] [DecidableEq Λ] in
/-- Entropy of a constant function is zero: `Ent_μ(c) = 0`. -/
@[simp] lemma entropy_const {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (c : ℝ) :
    entropy μ (fun _ => c) = 0 := by
  unfold entropy
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

omit [Fintype Λ] [DecidableEq Λ] in
/-- Entropy of the zero function is zero. Uses the Mathlib convention
`Real.log 0 = 0`, so `0 · log 0 = 0`. -/
@[simp] lemma entropy_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    entropy μ (fun _ => (0 : ℝ)) = 0 :=
  entropy_const μ 0

/-! ## Single-site decomposition (key sub-lemma)

For a single site `x : Λ`, the global entropy decomposes as

  Ent_μ(g) = ∫ Ent_{γ.condDist {x} σ}(g) dμ(σ)
           + Ent_μ ((M_x g) ∘ "restrict to Λ \ {x}")

where `(M_x g)(σ) := ∫ g dν` for `ν = γ.condDist {x} σ` is the
single-site smoothing of `g` at site `x`. The marginal-entropy
remainder is nonnegative, so this gives both directions:

  Ent_μ(g) ≥ ∫ Ent_{γ.condDist {x} σ}(g) dμ(σ),

and (combined with iterating to bound the marginal entropy)

  Ent_μ(g) ≤ Σ_{y ∈ Λ} ∫ Ent_{γ.condDist {y} σ}(g) dμ(σ).

The decomposition follows from the disintegration identity (DLR
provides the conditional Gibbs distribution) plus convexity of
`t ↦ t log t`. -/

/-- Single-site smoothing of `g` at site `x`: replaces `g(σ)` with
the conditional expectation `∫ g dν` against the single-site Gibbs
conditional `ν = γ.condDist {x} σ`. -/
def siteSmoothing (spec : GibbsSpec Λ ℝ) (x : Λ)
    (g : SpinConfig Λ ℝ → ℝ) : SpinConfig Λ ℝ → ℝ :=
  fun σ => ∫ τ, g τ ∂(spec.condDist {x} σ)

/-- The smoothing of a constant function is the same constant.
Follows from `IsProbabilityMeasure` of `spec.condDist`: the integral
of a constant against a probability measure is the constant. -/
@[simp] lemma siteSmoothing_const (spec : GibbsSpec Λ ℝ) (x : Λ) (c : ℝ) :
    siteSmoothing spec x (fun _ => c) = (fun _ => c) := by
  funext σ
  unfold siteSmoothing
  rw [integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- The smoothing of a nonneg function is nonneg. -/
lemma siteSmoothing_nonneg (spec : GibbsSpec Λ ℝ) (x : Λ)
    {g : SpinConfig Λ ℝ → ℝ} (hg : 0 ≤ g) :
    0 ≤ siteSmoothing spec x g := by
  intro σ
  unfold siteSmoothing
  exact integral_nonneg (fun _ => hg _)

/-! ### Integral preservation (DLR)

The key DLR identity at the integral level. The proof goes via the
Mathlib `Measure.bind` infrastructure: we show that `μ` is a fixed
point of the bind by `spec.condDist {x}`, hence integration commutes
through.
-/

/-- The single-site Gibbs conditional `σ ↦ spec.condDist {x} σ`,
viewed as a measure-valued map, is measurable.

Proof: `spec.measurable_condDist` provides measurability of
`σ ↦ ((spec.condDist {x} σ) A).toReal` for each measurable `A`. Since
each conditional is a probability measure, `(...) A ≤ 1 < ⊤`, so the
ENNReal-valued function `σ ↦ (spec.condDist {x} σ) A` is the
composition of `ENNReal.ofReal` (measurable) with the Real-valued
hypothesis. Then `Measure.measurable_of_measurable_coe` packages this
into measurability of the measure-valued map. -/
lemma measurable_condDist_singleton
    (spec : GibbsSpec Λ ℝ) (x : Λ) :
    Measurable (fun σ : SpinConfig Λ ℝ => spec.condDist {x} σ) := by
  refine Measure.measurable_of_measurable_coe _ ?_
  intro A hA
  -- Goal: Measurable (fun σ => (spec.condDist {x} σ) A) as ENNReal-valued.
  -- We have Real-valued measurability via `spec.measurable_condDist`.
  have h_real : Measurable (fun σ => ((spec.condDist {x} σ) A).toReal) :=
    spec.measurable_condDist {x} A hA
  have h_key : (fun σ => (spec.condDist {x} σ) A)
               = fun σ => ENNReal.ofReal ((spec.condDist {x} σ) A).toReal := by
    funext σ
    exact (ENNReal.ofReal_toReal (measure_ne_top _ A)).symm
  rw [h_key]
  exact ENNReal.measurable_ofReal.comp h_real

/-- **DLR identity as a fixed-point equation.**

The Gibbs measure `μ` is a fixed point of the kernel
`σ ↦ spec.condDist {x} σ` under the bind operation:

  μ.bind (fun σ => spec.condDist {x} σ) = μ.

Equivalent to the set-version `IsGibbsMeasure.dlr`, but stated in the
Mathlib bind / kernel formalism. -/
lemma bind_condDist_singleton_eq
    (spec : GibbsSpec Λ ℝ) (μ : Measure (SpinConfig Λ ℝ))
    [IsProbabilityMeasure μ] (h_gibbs : IsGibbsMeasure spec μ) (x : Λ) :
    μ.bind (fun σ => spec.condDist {x} σ) = μ := by
  ext A hA
  rw [Measure.bind_apply hA
        (measurable_condDist_singleton spec x).aemeasurable]
  -- Goal: ∫⁻ σ, (spec.condDist {x} σ) A ∂μ = μ A
  -- DLR axiom (Real form):
  have h_dlr : (μ A).toReal
                = ∫ σ, ((spec.condDist {x} σ) A).toReal ∂μ :=
    h_gibbs.dlr {x} A hA
  -- Measurability of the integrand as ENNReal-valued.
  have h_real : Measurable (fun σ => ((spec.condDist {x} σ) A).toReal) :=
    spec.measurable_condDist {x} A hA
  have h_meas : AEMeasurable (fun σ => (spec.condDist {x} σ) A) μ := by
    have : (fun σ => (spec.condDist {x} σ) A)
           = fun σ => ENNReal.ofReal ((spec.condDist {x} σ) A).toReal := by
      funext σ
      exact (ENNReal.ofReal_toReal (measure_ne_top _ A)).symm
    rw [this]
    exact (ENNReal.measurable_ofReal.comp h_real).aemeasurable
  have h_lt_top : ∀ᵐ σ ∂μ, (spec.condDist {x} σ) A < ⊤ :=
    Filter.Eventually.of_forall fun _ => (measure_ne_top _ A).lt_top
  -- Use `integral_toReal` to convert the Bochner integral on the RHS of DLR
  -- into a lintegral.
  rw [integral_toReal h_meas h_lt_top] at h_dlr
  -- h_dlr : (μ A).toReal = (∫⁻ σ, (spec.condDist {x} σ) A ∂μ).toReal
  -- Both sides are ≠ ⊤; conclude equality of the ENNReal values.
  have h_lhs_ne : ∫⁻ σ, (spec.condDist {x} σ) A ∂μ ≠ ⊤ := by
    have h_bd : ∫⁻ σ, (spec.condDist {x} σ) A ∂μ ≤ ∫⁻ _, 1 ∂μ :=
      lintegral_mono fun _ => prob_le_one
    have h1 : ∫⁻ _ : SpinConfig Λ ℝ, (1 : ENNReal) ∂μ = μ Set.univ := by
      simp [lintegral_one]
    rw [h1] at h_bd
    exact ne_top_of_le_ne_top (by simp [measure_ne_top]) h_bd
  exact (ENNReal.toReal_eq_toReal_iff' h_lhs_ne (measure_ne_top _ A)).mp h_dlr.symm

/-- **Integral preservation (DLR), lintegral version.**

For nonneg measurable `f`, integration against `μ` commutes with the
single-site Gibbs smoothing:

  ∫⁻ τ, f τ ∂μ = ∫⁻ σ, ∫⁻ τ, f τ ∂(γ.condDist {x} σ) ∂μ.

This is `Measure.lintegral_bind` applied to the DLR fixed point. -/
lemma lintegral_siteSmoothing
    (spec : GibbsSpec Λ ℝ) (μ : Measure (SpinConfig Λ ℝ))
    [IsProbabilityMeasure μ] (h_gibbs : IsGibbsMeasure spec μ)
    {f : SpinConfig Λ ℝ → ENNReal} (hf : Measurable f) (x : Λ) :
    ∫⁻ τ, f τ ∂μ = ∫⁻ σ, ∫⁻ τ, f τ ∂(spec.condDist {x} σ) ∂μ := by
  conv_lhs => rw [← bind_condDist_singleton_eq spec μ h_gibbs x]
  exact Measure.lintegral_bind
    (measurable_condDist_singleton spec x).aemeasurable hf.aemeasurable

/-- **Integral preservation (DLR), Bochner version, nonneg case.**

For a nonneg measurable integrable `g`, integration of the
single-site smoothing recovers the original integral. -/
theorem integral_siteSmoothing_nonneg
    (spec : GibbsSpec Λ ℝ) (μ : Measure (SpinConfig Λ ℝ))
    [IsProbabilityMeasure μ] (h_gibbs : IsGibbsMeasure spec μ)
    {g : SpinConfig Λ ℝ → ℝ} (hg_meas : Measurable g) (hg_nn : 0 ≤ g)
    (hg_int : Integrable g μ) (x : Λ) :
    ∫ σ, siteSmoothing spec x g σ ∂μ = ∫ σ, g σ ∂μ := by
  -- Helper: `ENNReal.ofReal` of a nonneg integral equals the lintegral.
  have h_g_nn_ae : 0 ≤ᵐ[μ] g := Filter.Eventually.of_forall hg_nn
  have h_g_meas_ae : AEStronglyMeasurable g μ := hg_meas.aestronglyMeasurable
  -- Prepare a few facts about the smoothing of g.
  -- Strong measurability of σ ↦ ∫ τ, g τ ∂(γ.condDist {x} σ) — use the
  -- ProbabilityTheory.Kernel framework via measurable_condDist_singleton.
  have h_smooth_meas :
      AEStronglyMeasurable (siteSmoothing spec x g) μ := by
    have : StronglyMeasurable (siteSmoothing spec x g) := by
      let κ : ProbabilityTheory.Kernel (SpinConfig Λ ℝ) (SpinConfig Λ ℝ) :=
        { toFun := fun σ => spec.condDist {x} σ
          measurable' := measurable_condDist_singleton spec x }
      exact StronglyMeasurable.integral_kernel
        (κ := κ) hg_meas.stronglyMeasurable
    exact this.aestronglyMeasurable
  have h_smooth_nn_ae :
      0 ≤ᵐ[μ] siteSmoothing spec x g :=
    Filter.Eventually.of_forall (siteSmoothing_nonneg spec x hg_nn)
  -- The main calculation: convert both sides to lintegrals, then use
  -- `lintegral_siteSmoothing` and pointwise `ofReal_integral_eq_lintegral_ofReal`.
  rw [integral_eq_lintegral_of_nonneg_ae h_smooth_nn_ae h_smooth_meas,
      integral_eq_lintegral_of_nonneg_ae h_g_nn_ae h_g_meas_ae]
  congr 1
  -- Goal: ∫⁻ σ, ENNReal.ofReal (siteSmoothing γ x g σ) ∂μ
  --     = ∫⁻ σ, ENNReal.ofReal (g σ) ∂μ
  have h_ofReal_meas : Measurable (fun τ : SpinConfig Λ ℝ => ENNReal.ofReal (g τ)) :=
    ENNReal.measurable_ofReal.comp hg_meas
  rw [lintegral_siteSmoothing spec μ h_gibbs h_ofReal_meas x]
  -- Goal: ∫⁻ σ, ENNReal.ofReal (siteSmoothing γ x g σ) ∂μ
  --     = ∫⁻ σ, ∫⁻ τ, ENNReal.ofReal (g τ) ∂(spec.condDist {x} σ) ∂μ
  -- It suffices to show pointwise `μ`-a.e.
  -- We need: g `ν_σ`-integrable for μ-a.e. σ, derived from `hg_int` via
  -- `lintegral_siteSmoothing`.
  -- For nonneg g, integrability of g w.r.t. μ implies the lintegral of
  -- ENNReal.ofReal ∘ g is finite, hence — by lintegral_siteSmoothing — the
  -- inner lintegral is finite μ-a.e., hence g is ν_σ-integrable μ-a.e.
  -- For nonneg `g`, `‖g τ‖ₑ = ENNReal.ofReal (g τ)`.
  have h_ofReal_eq_enorm : (fun τ => ENNReal.ofReal (g τ))
                          = (fun τ => ‖g τ‖ₑ) := by
    funext τ
    exact (Real.enorm_eq_ofReal (hg_nn τ)).symm
  have h_lint_g_lt_top : ∫⁻ τ, ENNReal.ofReal (g τ) ∂μ < ⊤ := by
    rw [h_ofReal_eq_enorm]
    rw [show (fun τ => ‖g τ‖ₑ) = (fun τ => ‖g τ‖ₑ) from rfl]
    exact (hasFiniteIntegral_iff_enorm.mp hg_int.hasFiniteIntegral)
  have h_inner_lint_lt_top :
      ∀ᵐ σ ∂μ, ∫⁻ τ, ENNReal.ofReal (g τ) ∂(spec.condDist {x} σ) < ⊤ := by
    have h_outer : ∫⁻ σ, (∫⁻ τ, ENNReal.ofReal (g τ) ∂(spec.condDist {x} σ)) ∂μ
                    = ∫⁻ τ, ENNReal.ofReal (g τ) ∂μ :=
      (lintegral_siteSmoothing spec μ h_gibbs h_ofReal_meas x).symm
    have h_outer_lt : ∫⁻ σ, (∫⁻ τ, ENNReal.ofReal (g τ) ∂(spec.condDist {x} σ)) ∂μ < ⊤ := by
      rw [h_outer]; exact h_lint_g_lt_top
    -- Measurability of σ ↦ ∫⁻ τ, ENNReal.ofReal (g τ) ∂(spec.condDist {x} σ)
    -- via the kernel framework.
    have h_kernel_meas : Measurable
        (fun σ => ∫⁻ τ, ENNReal.ofReal (g τ) ∂(spec.condDist {x} σ)) := by
      let κ : ProbabilityTheory.Kernel (SpinConfig Λ ℝ) (SpinConfig Λ ℝ) :=
        { toFun := fun σ => spec.condDist {x} σ
          measurable' := measurable_condDist_singleton spec x }
      exact Measurable.lintegral_kernel (κ := κ) h_ofReal_meas
    exact ae_lt_top' h_kernel_meas.aemeasurable h_outer_lt.ne
  have h_ae_int : ∀ᵐ σ ∂μ, Integrable g (spec.condDist {x} σ) := by
    filter_upwards [h_inner_lint_lt_top] with σ hσ
    refine ⟨hg_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, ← h_ofReal_eq_enorm]
    exact hσ
  apply lintegral_congr_ae
  filter_upwards [h_ae_int] with σ hσ
  -- For each such σ: g is ν_σ-integrable and nonneg, so by
  -- `ofReal_integral_eq_lintegral_ofReal`:
  -- ENNReal.ofReal (∫ τ, g τ ∂ν_σ) = ∫⁻ τ, ENNReal.ofReal (g τ) ∂ν_σ.
  exact ofReal_integral_eq_lintegral_ofReal hσ
    (Filter.Eventually.of_forall hg_nn)

/-- **Integrability of the smoothing of a nonneg integrable function.**

For nonneg measurable integrable `f`, the smoothing
`siteSmoothing γ x f` is again integrable. The proof bypasses the
integral identity (which would be circular) by directly bounding
`∫⁻ ‖siteSmoothing γ x f σ‖ₑ ∂μ` via `lintegral_siteSmoothing` and
`ENNReal.ofReal_toReal_le`. -/
lemma integrable_siteSmoothing_of_nonneg
    (spec : GibbsSpec Λ ℝ) (μ : Measure (SpinConfig Λ ℝ))
    [IsProbabilityMeasure μ] (h_gibbs : IsGibbsMeasure spec μ)
    {f : SpinConfig Λ ℝ → ℝ} (hf_meas : Measurable f) (hf_nn : 0 ≤ f)
    (hf_int : Integrable f μ) (x : Λ) :
    Integrable (siteSmoothing spec x f) μ := by
  refine ⟨?_, ?_⟩
  · -- Strong measurability via `StronglyMeasurable.integral_kernel`.
    let κ : ProbabilityTheory.Kernel (SpinConfig Λ ℝ) (SpinConfig Λ ℝ) :=
      { toFun := fun σ => spec.condDist {x} σ
        measurable' := measurable_condDist_singleton spec x }
    exact (StronglyMeasurable.integral_kernel
      (κ := κ) hf_meas.stronglyMeasurable).aestronglyMeasurable
  · -- HasFiniteIntegral: bound `∫⁻ ‖siteSmoothing γ x f σ‖ₑ ∂μ` by
    -- `∫⁻ τ, ENNReal.ofReal (f τ) ∂μ < ⊤`.
    rw [hasFiniteIntegral_iff_enorm]
    -- Replace `‖siteSmoothing γ x f σ‖ₑ` with `ENNReal.ofReal (...)` (nonneg).
    have h_enorm_eq : (fun σ => ‖siteSmoothing spec x f σ‖ₑ)
                      = (fun σ => ENNReal.ofReal (siteSmoothing spec x f σ)) := by
      funext σ
      exact Real.enorm_eq_ofReal (siteSmoothing_nonneg spec x hf_nn σ)
    rw [h_enorm_eq]
    -- Pointwise bound: `ENNReal.ofReal (∫ τ, f τ ∂ν_σ) ≤ ∫⁻ τ, ENNReal.ofReal (f τ) ∂ν_σ`.
    have h_pointwise : ∀ σ, ENNReal.ofReal (siteSmoothing spec x f σ)
                            ≤ ∫⁻ τ, ENNReal.ofReal (f τ) ∂(spec.condDist {x} σ) := by
      intro σ
      change ENNReal.ofReal (∫ τ, f τ ∂(spec.condDist {x} σ)) ≤ _
      rw [integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall hf_nn) hf_meas.aestronglyMeasurable]
      exact ENNReal.ofReal_toReal_le
    refine lt_of_le_of_lt (lintegral_mono h_pointwise) ?_
    -- Outer: `∫⁻ σ, ∫⁻ τ, ENNReal.ofReal (f τ) ∂ν_σ ∂μ = ∫⁻ τ, ENNReal.ofReal (f τ) ∂μ`.
    have h_meas_ofReal : Measurable (fun τ : SpinConfig Λ ℝ => ENNReal.ofReal (f τ)) :=
      ENNReal.measurable_ofReal.comp hf_meas
    rw [← lintegral_siteSmoothing spec μ h_gibbs h_meas_ofReal x]
    -- For nonneg f: `ENNReal.ofReal (f τ) = ‖f τ‖ₑ`, so the bound matches
    -- `f`'s `HasFiniteIntegral`.
    have h_f_lint_eq : (fun τ : SpinConfig Λ ℝ => ENNReal.ofReal (f τ))
                      = (fun τ => ‖f τ‖ₑ) := by
      funext τ
      exact (Real.enorm_eq_ofReal (hf_nn τ)).symm
    rw [h_f_lint_eq]
    exact hf_int.hasFiniteIntegral

/-- **Integral preservation (DLR), Bochner version (general integrable `g`).**

For a measurable integrable `g`, integration of the single-site
smoothing recovers the original integral:

  ∫ σ, (∫ τ, g τ ∂(γ.condDist {x} σ)) ∂μ = ∫ τ, g τ ∂μ.

Proof: decompose `g = g_pos - g_neg` with `g_pos = max(g, 0)`, `g_neg = max(-g, 0)`
(both nonneg integrable). Apply `integral_siteSmoothing_nonneg` and
`integrable_siteSmoothing_of_nonneg` to each piece. The μ-a.e.
linearity of `siteSmoothing` over subtraction holds where both pieces
are ν_σ-integrable, which is μ-a.e. by an `ae_lt_top'` argument. -/
theorem integral_siteSmoothing
    (spec : GibbsSpec Λ ℝ) (μ : Measure (SpinConfig Λ ℝ))
    [IsProbabilityMeasure μ] (h_gibbs : IsGibbsMeasure spec μ)
    {g : SpinConfig Λ ℝ → ℝ} (hg_meas : Measurable g)
    (hg_int : Integrable g μ) (x : Λ) :
    ∫ σ, siteSmoothing spec x g σ ∂μ = ∫ σ, g σ ∂μ := by
  -- Decompose g into nonneg pieces.
  set g_pos : SpinConfig Λ ℝ → ℝ := fun σ => max (g σ) 0 with hg_posdef
  set g_neg : SpinConfig Λ ℝ → ℝ := fun σ => max (-(g σ)) 0 with hg_neg_def
  have hg_pos_meas : Measurable g_pos := hg_meas.max measurable_const
  have hg_neg_meas : Measurable g_neg := hg_meas.neg.max measurable_const
  have hg_pos_nn : 0 ≤ g_pos := fun _ => le_max_right _ _
  have hg_neg_nn : 0 ≤ g_neg := fun _ => le_max_right _ _
  -- Integrability of g_pos, g_neg from |g|.
  have hg_abs_int : Integrable (fun σ => |g σ|) μ := hg_int.abs
  have hg_pos_int : Integrable g_pos μ := by
    refine hg_abs_int.mono hg_pos_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun σ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_pos_nn σ), Real.norm_eq_abs,
        abs_of_nonneg (abs_nonneg _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hg_neg_int : Integrable g_neg μ := by
    refine hg_abs_int.mono hg_neg_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun σ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_neg_nn σ), Real.norm_eq_abs,
        abs_of_nonneg (abs_nonneg _)]
    exact max_le (neg_le_abs _) (abs_nonneg _)
  -- Pointwise: g = g_pos - g_neg.
  have h_decompose : ∀ σ, g σ = g_pos σ - g_neg σ := by
    intro σ
    by_cases h : 0 ≤ g σ
    · simp [g_pos, g_neg, max_eq_left h, max_eq_right (neg_nonpos_of_nonneg h)]
    · push_neg at h
      have h_le : g σ ≤ 0 := h.le
      have h_pos : 0 ≤ -(g σ) := neg_nonneg.mpr h_le
      simp [g_pos, g_neg, max_eq_right h_le, max_eq_left h_pos]
  -- siteSmoothing distributes over subtraction μ-a.e.
  have h_decomp_smooth : ∀ᵐ σ ∂μ,
      siteSmoothing spec x g σ
        = siteSmoothing spec x g_pos σ - siteSmoothing spec x g_neg σ := by
    -- a.e. integrability of g_pos, g_neg w.r.t. each conditional ν_σ.
    have h_ae_int : ∀ {h : SpinConfig Λ ℝ → ℝ} (_hh_meas : Measurable h)
        (_hh_int : Integrable h μ),
        ∀ᵐ σ ∂μ, Integrable h (spec.condDist {x} σ) := by
      intro h hh_meas hh_int
      have h_lint_lt_top : ∫⁻ τ, ‖h τ‖ₑ ∂μ < ⊤ := hh_int.hasFiniteIntegral
      have h_outer_lt :
          ∫⁻ σ, (∫⁻ τ, ‖h τ‖ₑ ∂(spec.condDist {x} σ)) ∂μ < ⊤ := by
        rw [← lintegral_siteSmoothing spec μ h_gibbs hh_meas.enorm x]
        exact h_lint_lt_top
      have h_kernel_meas : Measurable
          (fun σ => ∫⁻ τ, ‖h τ‖ₑ ∂(spec.condDist {x} σ)) := by
        let κ : ProbabilityTheory.Kernel (SpinConfig Λ ℝ) (SpinConfig Λ ℝ) :=
          { toFun := fun σ => spec.condDist {x} σ
            measurable' := measurable_condDist_singleton spec x }
        exact Measurable.lintegral_kernel (κ := κ) hh_meas.enorm
      filter_upwards
        [ae_lt_top' h_kernel_meas.aemeasurable h_outer_lt.ne] with σ hσ
      exact ⟨hh_meas.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr hσ⟩
    have hg_pos_ae := h_ae_int hg_pos_meas hg_pos_int
    have hg_neg_ae := h_ae_int hg_neg_meas hg_neg_int
    filter_upwards [hg_pos_ae, hg_neg_ae] with σ hσ_pos hσ_neg
    show ∫ τ, g τ ∂(spec.condDist {x} σ)
          = ∫ τ, g_pos τ ∂(spec.condDist {x} σ)
            - ∫ τ, g_neg τ ∂(spec.condDist {x} σ)
    rw [show (fun τ => g τ) = (fun τ => g_pos τ - g_neg τ) from funext h_decompose,
        integral_sub hσ_pos hσ_neg]
  -- Combine the pieces.
  have hsm_pos_int : Integrable (siteSmoothing spec x g_pos) μ :=
    integrable_siteSmoothing_of_nonneg spec μ h_gibbs hg_pos_meas hg_pos_nn hg_pos_int x
  have hsm_neg_int : Integrable (siteSmoothing spec x g_neg) μ :=
    integrable_siteSmoothing_of_nonneg spec μ h_gibbs hg_neg_meas hg_neg_nn hg_neg_int x
  calc ∫ σ, siteSmoothing spec x g σ ∂μ
      = ∫ σ, (siteSmoothing spec x g_pos σ - siteSmoothing spec x g_neg σ) ∂μ :=
        integral_congr_ae h_decomp_smooth
    _ = ∫ σ, siteSmoothing spec x g_pos σ ∂μ - ∫ σ, siteSmoothing spec x g_neg σ ∂μ :=
        integral_sub hsm_pos_int hsm_neg_int
    _ = ∫ σ, g_pos σ ∂μ - ∫ σ, g_neg σ ∂μ := by
        rw [integral_siteSmoothing_nonneg spec μ h_gibbs hg_pos_meas hg_pos_nn hg_pos_int x,
            integral_siteSmoothing_nonneg spec μ h_gibbs hg_neg_meas hg_neg_nn hg_neg_int x]
    _ = ∫ σ, (g_pos σ - g_neg σ) ∂μ := (integral_sub hg_pos_int hg_neg_int).symm
    _ = ∫ σ, g σ ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun σ => (h_decompose σ).symm

/-- The integral of `g` against the single-site Gibbs conditional,
viewed as a function of the boundary `σ`, is nothing other than the
smoothing `siteSmoothing γ x g`. -/
lemma siteSmoothing_eq_integral (spec : GibbsSpec Λ ℝ) (x : Λ)
    (g : SpinConfig Λ ℝ → ℝ) (σ : SpinConfig Λ ℝ) :
    siteSmoothing spec x g σ = ∫ τ, g τ ∂(spec.condDist {x} σ) := rfl

/-- Auxiliary integrability assumption: the single-site smoothings of
`g` and of `g · log g` are integrable, and the smoothing of `g`
times its log is integrable.

These are the additional regularity conditions required to make the
algebraic manipulation in `entropy_decomposition_single_site` go
through. They follow from `EntropyIntegrable μ g` plus a uniform
boundedness / domination argument on the family of conditionals; we
package them as a separate hypothesis to keep the API clean.

All three are stated in `siteSmoothing` form so that
`MeasureTheory.integral_sub` can be applied without going through
`siteSmoothing`-vs-`∫ ∂(condDist)` definitional bridges. -/
structure EntropySmoothingIntegrable
    (spec : GibbsSpec Λ ℝ) (μ : Measure (SpinConfig Λ ℝ))
    (g : SpinConfig Λ ℝ → ℝ) (x : Λ) : Prop where
  smoothing_integrable :
    Integrable (siteSmoothing spec x g) μ
  smoothing_log_integrable :
    Integrable (fun σ => siteSmoothing spec x g σ
                          * Real.log (siteSmoothing spec x g σ)) μ
  cond_glog_integrable :
    Integrable (siteSmoothing spec x (fun τ => g τ * Real.log (g τ))) μ

/-- **Single-site entropy decomposition (S1).**

`Ent_μ(g) = ∫ Ent_{γ.condDist {x} σ}(g) dμ(σ) + Ent_μ(siteSmoothing γ x g)`.

This is the additive decomposition of entropy under conditioning on
a single site. Combining DLR (`μ = ∫ γ.condDist {x} σ dμ(σ)`) and
the algebraic identity `(a · log a) - b · log b = ...` it reduces to
the integral preservation identity `integral_siteSmoothing`
applied to `g` and to `g · log g`.

Concretely: expanding both sides and rearranging, the equality is
equivalent to

  ∫∫ g log g dν dμ = ∫ g log g dμ                         (DLR for `g log g`)
  ∫ σ, (∫ g dν_σ) log(∫ g dν_σ) ∂μ = ∫ σ, M_x g σ · log(M_x g σ) ∂μ
                                    -- by definition of `siteSmoothing`
  (∫ σ, M_x g σ ∂μ) = ∫ g dμ                              (DLR for `g`)

The first and third are `integral_siteSmoothing`; the middle is
trivial unfolding of `siteSmoothing`.

The full algebraic reduction is left as `sorry` here pending the
small auxiliary integrability lemmas (`integral_sub`, `integrable_sub`,
etc.) — pure bookkeeping with no analytic content beyond
`integral_siteSmoothing`. -/
theorem entropy_decomposition_single_site
    (spec : GibbsSpec Λ ℝ) (μ : Measure (SpinConfig Λ ℝ))
    [IsProbabilityMeasure μ] (h_gibbs : IsGibbsMeasure spec μ)
    (g : SpinConfig Λ ℝ → ℝ) (hg : EntropyIntegrable μ g) (x : Λ)
    (hint : EntropySmoothingIntegrable spec μ g x) :
    entropy μ g =
      (∫ σ, entropy (spec.condDist {x} σ) g ∂μ)
        + entropy μ (siteSmoothing spec x g) := by
  -- DLR identities at the integral level:
  have h_g : ∫ σ, siteSmoothing spec x g σ ∂μ = ∫ σ, g σ ∂μ :=
    integral_siteSmoothing spec μ h_gibbs hg.measurable hg.integrable x
  have h_glogg_meas : Measurable (fun τ => g τ * Real.log (g τ)) :=
    hg.measurable.mul (Real.measurable_log.comp hg.measurable)
  have h_glogg : ∫ σ, siteSmoothing spec x (fun τ => g τ * Real.log (g τ)) σ ∂μ
                = ∫ σ, g σ * Real.log (g σ) ∂μ :=
    integral_siteSmoothing spec μ h_gibbs h_glogg_meas hg.log_integrable x
  -- Unfold both `entropy μ g` (LHS) and `entropy μ (siteSmoothing _ _ g)` (RHS).
  -- The integrand `entropy (spec.condDist {x} σ) g` on the RHS stays sealed
  -- and is split via `integral_sub` below.
  -- Reduce the integrated-entropy on the RHS to the siteSmoothing form,
  -- then split via integral_sub.
  have h_inner :
      ∫ σ, entropy (spec.condDist {x} σ) g ∂μ
        = (∫ σ, siteSmoothing spec x (fun τ => g τ * Real.log (g τ)) σ ∂μ)
          - ∫ σ, siteSmoothing spec x g σ
                  * Real.log (siteSmoothing spec x g σ) ∂μ := by
    rw [← integral_sub hint.cond_glog_integrable hint.smoothing_log_integrable]
    rfl
  rw [h_inner, h_glogg]
  unfold entropy
  rw [h_g]
  ring

/-- **Marginal entropy is nonneg.** Standard application of Jensen's
inequality to `t ↦ t log t` (convex on `[0, ∞)`).

Used by the chain rule to drop the "remainder" marginal entropy term
in `entropy_decomposition_single_site` to get a one-sided bound. -/
lemma entropy_nonneg
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (g : α → ℝ) (hg : EntropyIntegrable μ g) :
    0 ≤ entropy μ g := by
  -- Goal: 0 ≤ (∫ g log g) - (∫ g) · log (∫ g)
  -- Equivalent to: (∫ g) · log (∫ g) ≤ ∫ g log g
  -- Apply ConvexOn.map_average_le for the convex `· * log ·` on `[0, ∞)`.
  have h_ae : ∀ᵐ x ∂μ, g x ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall (fun x => hg.nonneg x)
  have h_jensen :=
    ConvexOn.map_average_le Real.convexOn_mul_log
      Real.continuous_mul_log.continuousOn isClosed_Ici h_ae
      hg.integrable hg.log_integrable
  rw [average_eq_integral, average_eq_integral] at h_jensen
  -- h_jensen : (∫ g) * log (∫ g) ≤ ∫ g log g
  unfold entropy
  linarith

/-! ## Removed: `entropy_chain_rule_local`

A previous version of this file contained an axiom

  `Ent_μ(g) ≤ Σ_{x ∈ Λ} ∫ Ent_{γ.condDist {x} σ}(g) dμ(σ)`

(with no scaling constant, claimed as a universal property of all
Gibbs measures) cited as BGL §5.7.4 / Stroock-Zegarlinski 1992.

**This axiom was REMOVED on review.** The statement is mathematically
false for general Gibbs measures: at low temperature the single-site
conditionals can be deterministic (Dirac measures with zero entropy),
making the RHS vanish while the LHS remains positive. The cited
Stroock-Zegarlinski result is an *equivalence* between mixing and
LSI, not a universal chain rule.

The actual proof of Zegarlinski's LSI does NOT factor through such a
free-standing chain rule. Instead, it interleaves the single-site
decomposition (`entropy_decomposition_single_site`, *proved*) with
the local LSI bound and the Neumann series for the gradient
interaction matrix; the constant `c · (1 - α)` emerges from this
interleaving directly.

The remaining content of this file (siteSmoothing, S1, integral
DLR identities) is unaffected and still proved.
-/

end MarkovSemigroups.DobrushinZegarlinski

end
