/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ouGeneratorFin` as an `L²(γFin n)` element (G2/G4 base)

Shared prerequisite for the `GeneratorCompat` discharge
(`plans/gross-discharge.md`, G2/G4): the named OU generator
`ouGeneratorFin f = Δf − x·∇f` (from `EuclideanGenerator`) is
square-integrable against the standard multivariate Gaussian for core
`f`, hence defines an element of `Lp ℝ 2 (γFin n)`.

Split out so the strong-`L²` limit (`EuclideanGeneratorLimit`) and the
γ-IBP / assembly (`EuclideanGeneratorCompat`) can be developed in
parallel against a common base.
-/

import MarkovSemigroups.Instances.WorkInProgress.EuclideanFinLp
import MarkovSemigroups.Instances.WorkInProgress.EuclideanGenerator

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace ContDiff

noncomputable section

namespace GaussianFin

variable {n : ℕ}

/-- `ouGeneratorFin f = Δf − x·∇f ∈ L²(γFin n)` for core `f`.

Strategy: `IsCoreFin` gives `f` `ContDiff ℝ ∞` with uniformly bounded
first/second partials, so `∑ᵢ ∂ᵢ²f` is bounded and `∑ᵢ xᵢ ∂ᵢf` has at
most linear growth in `x`; both are square-integrable against the
standard Gaussian `γFin n` (bounded part via `memLp_two_of_bound`;
linear-growth part via Gaussian polynomial moments). -/
theorem memLp_ouGeneratorFin {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    MemLp (ouGeneratorFin f) 2 (γFin n) := by
  obtain ⟨hcd, M, hM⟩ := hf
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) ((hM (fun _ => 0)).1)
  have hcoreF : IsCoreFin f := ⟨hcd, M, hM⟩
  -- Each Gaussian coordinate is in `L²`.
  have hcoord : ∀ i : Fin n, MemLp (fun x : Fin n → ℝ => x i) 2 (γFin n) := by
    intro i
    have heval : MeasurePreserving (Function.eval i) (γFin n) Gaussian1D.γ := by
      simpa [γFin] using
        (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => Gaussian1D.γ) i)
    have hid : MemLp (id : ℝ → ℝ) (2 : ℝ≥0∞) Gaussian1D.γ := by
      have h := memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (2 : ℝ≥0)
      have hcoe : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := by norm_num
      simpa [Gaussian1D.γ, hcoe] using h
    have hcomp := hid.comp_measurePreserving heval
    simpa [Function.comp] using hcomp
  -- Diffusion part `∑ᵢ ∂ᵢ²f` (function-valued Finset sum): bounded ⇒ `L²`.
  have hA : MemLp (∑ i : Fin n, secondPartial i f) 2 (γFin n) := by
    have hsm : StronglyMeasurable (∑ i : Fin n, secondPartial i f) :=
      Finset.stronglyMeasurable_sum _ (fun i _ =>
        (hcoreF.secondPartial_continuous i).stronglyMeasurable)
    refine (memLp_const ((n : ℝ) * M)).mono hsm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_))
    have hnM : (0 : ℝ) ≤ (n : ℝ) * M := by positivity
    have hb : |∑ i : Fin n, secondPartial i f x| ≤ (n : ℝ) * M := by
      calc |∑ i : Fin n, secondPartial i f x|
          ≤ ∑ i : Fin n, |secondPartial i f x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, M := Finset.sum_le_sum
            (fun i _ => by simpa [Real.norm_eq_abs] using (hM x).2.2 i)
        _ = (n : ℝ) * M := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [Finset.sum_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg hnM]
    exact hb
  -- Drift part `∑ᵢ xᵢ ∂ᵢf`: each term is (Gaussian coordinate)·(bounded) ∈ `L²`.
  have hB : MemLp
      (∑ i : Fin n, fun x : Fin n → ℝ => x i * partialDeriv i f x) 2 (γFin n) := by
    refine memLp_finset_sum' _ (fun i _ => ?_)
    have hsm : AEStronglyMeasurable
        (fun x : Fin n → ℝ => x i * partialDeriv i f x) (γFin n) :=
      (((measurable_pi_apply i).stronglyMeasurable).mul
        (hcoreF.partial_continuous i).stronglyMeasurable).aestronglyMeasurable
    refine ((hcoord i).const_mul M).mono hsm
      (Filter.Eventually.of_forall (fun x => ?_))
    have hpm : ‖partialDeriv i f x‖ ≤ M := (hM x).2.1 i
    calc ‖x i * partialDeriv i f x‖
        = ‖x i‖ * ‖partialDeriv i f x‖ := by rw [norm_mul]
      _ ≤ ‖x i‖ * M :=
          mul_le_mul_of_nonneg_left hpm (norm_nonneg _)
      _ = ‖M * x i‖ := by
          rw [norm_mul, Real.norm_eq_abs M, abs_of_nonneg hM0, mul_comm]
  have hougen : ouGeneratorFin f =
      (∑ i : Fin n, secondPartial i f)
        - (∑ i : Fin n, fun x : Fin n → ℝ => x i * partialDeriv i f x) := by
    funext x
    simp [ouGeneratorFin_apply, Finset.sum_apply, Pi.sub_apply]
  rw [hougen]
  exact hA.sub hB

/-- The `L²(γFin n)` element represented by `ouGeneratorFin f`
(`= Δf − x·∇f`), for core `f`. -/
def ouGeneratorFinLp {f : (Fin n → ℝ) → ℝ} (hf : IsCoreFin f) :
    Lp ℝ 2 (γFin n) :=
  (memLp_ouGeneratorFin hf).toLp (ouGeneratorFin f)

/-- **nD Gaussian integration by parts (Dirichlet-form identity)** —
the multivariate Gaussian IBP: for `C^∞` `f, g` with bounded value,
first and pure-second coordinate derivatives, integrating `g` against
the OU generator `Lf = Δf − x·∇f` over the standard Gaussian equals
minus the Dirichlet energy `∫ ⟨∇g,∇f⟩`.

**General (no project definitions)** — stated purely in Mathlib terms
(`fderiv`/`Pi.single`/`MeasureTheory.Measure.pi`/
`ProbabilityTheory.gaussianReal`), so it is a reusable,
vetting-amenable textbook statement; the project-specific
`ouGeneratorFin_ibp_integral` is derived from it by unfolding the
(thin) project definitions. Same strategic pattern as
`gaussianOU_heatEquation_within_zero` (the Gross-G2 deep cruxes are
deferred to general vetted axioms; the discharge route is the
coordinatewise Fubini lift of the *proved* 1D
`Gaussian1D.gaussian_generator_ibp`).

Reference: Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov
Diffusion Operators* (2014), §2.7 / §1.6 (the Dirichlet form
`E(g,f)=∫⟨∇g,∇f⟩` is the generator's energy form: `∫ g·Lf = −E(g,f)`
for the OU generator); Gaussian integration by parts (Stein).
**Vetted Standard / Likely correct** (Gemini `gemini-3-pro-preview`,
2026-05-16; recorded in `AXIOM_AUDIT.md`): sign/normalization exact
(`∇φ/φ = −x` for `N(0,I)` yields the `−x·∇f` drift, coefficient 1, no
factor-2/variance rescale); non-vacuous (`f=g=sin x₀`); pure-second-
partial + boundedness hypotheses sufficient (Gaussian moments absorb
the linear-growth `g·(x·∇f)`; IBP is coordinatewise-Fubini, no
mixed/third partials); `g`'s pure-2nd-partial bound is superfluous-
but-harmless (kept for core-class symmetry). Discharge route: the
coordinatewise Fubini lift of the proved 1D
`Gaussian1D.gaussian_generator_ibp`. -/
axiom gaussianFin_integrationByParts {n : ℕ}
    (f g : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ∞ f) (Mf : ℝ)
    (hf_bd : ∀ x : Fin n → ℝ,
      ‖f x‖ ≤ Mf ∧
      (∀ i : Fin n, ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ Mf) ∧
      (∀ i : Fin n,
        ‖fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x
            (Pi.single i 1)‖ ≤ Mf))
    (hg_smooth : ContDiff ℝ ∞ g) (Mg : ℝ)
    (hg_bd : ∀ x : Fin n → ℝ,
      ‖g x‖ ≤ Mg ∧
      (∀ i : Fin n, ‖fderiv ℝ g x (Pi.single i 1)‖ ≤ Mg) ∧
      (∀ i : Fin n,
        ‖fderiv ℝ (fun z => fderiv ℝ g z (Pi.single i 1)) x
            (Pi.single i 1)‖ ≤ Mg)) :
    ∫ x, g x *
        ((∑ i : Fin n,
            fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x
              (Pi.single i 1))
          - ∑ i : Fin n, x i * fderiv ℝ f x (Pi.single i 1))
      ∂(MeasureTheory.Measure.pi
          (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))
      = - ∫ x,
          (∑ i : Fin n,
            fderiv ℝ g x (Pi.single i 1) * fderiv ℝ f x (Pi.single i 1))
          ∂(MeasureTheory.Measure.pi
              (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1))

/-- **G4 — nD Gaussian integration by parts, integral form**
(`∫ g·(ouGeneratorFin f) dγFin n = -ouEnergyFin g f`). Derived from
the general `gaussianFin_integrationByParts` by unfolding the thin
project definitions. -/
theorem ouGeneratorFin_ibp_integral {f g : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (hg : IsCoreFin g) :
    ∫ x, g x * ouGeneratorFin f x ∂γFin n = - ouEnergyFin g f := by
  obtain ⟨hsf, Mf, hMf⟩ := hf
  obtain ⟨hsg, Mg, hMg⟩ := hg
  simpa only [ouGeneratorFin_apply, ouEnergyFin, ouGammaFin, γFin,
    Gaussian1D.γ, secondPartial, partialDeriv] using
    gaussianFin_integrationByParts (n := n) f g hsf Mf hMf hsg Mg hMg

/-- **G4 — nD Gaussian integration by parts (inner-product form).**
For core `f, g`: `⟪g, ouGeneratorFin f⟫_{L²(γFin n)} = -ouEnergyFin g f`.
The `L²` inner product unfolds (via `L2.inner_def` + `MemLp.coeFn_toLp`
for `coreToL2 g` and `ouGeneratorFinLp f`) to
`∫ g·(ouGeneratorFin f) dγ`, which is `ouGeneratorFin_ibp_integral`.
Lives here (imports only the building base, no `EuclideanGeneratorLimit`)
so it verifies independently of the parallel limit work. -/
theorem ouGeneratorFin_ibp {f g : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (hg : IsCoreFin g) :
    ⟪(stdGaussianFin_dirichletMarkovSemigroup n).coreToL2 hg,
        ouGeneratorFinLp hf⟫_ℝ
      = - ouEnergyFin g f := by
  -- Pure `Lp` wiring (no math): the analytic content is
  -- `ouGeneratorFin_ibp_integral`. Force `coreToL2`/`ouGeneratorFinLp`
  -- to their `.toLp` normal form (`rfl`), then mirror the proven
  -- `EuclideanFinLp` `L².inner_def` incantation via a hand-written
  -- `have` so the `coeFn_toLp` rewrites match syntactically.
  show ⟪(isCoreFin_memLp g hg).toLp g,
        (memLp_ouGeneratorFin hf).toLp (ouGeneratorFin f)⟫_ℝ
      = - ouEnergyFin g f
  rw [MeasureTheory.L2.inner_def]
  have hint :
      ∫ a, ⟪((isCoreFin_memLp g hg).toLp g) a,
          ((memLp_ouGeneratorFin hf).toLp (ouGeneratorFin f)) a⟫_ℝ
        ∂γFin n
        = ∫ x, g x * ouGeneratorFin f x ∂γFin n := by
    refine integral_congr_ae ?_
    filter_upwards [(isCoreFin_memLp g hg).coeFn_toLp,
      (memLp_ouGeneratorFin hf).coeFn_toLp] with x hgx hfx
    simp only [hgx, hfx]
    change RCLike.re (ouGeneratorFin f x * star (g x))
      = g x * ouGeneratorFin f x
    simp [mul_comm]
  rw [hint, ouGeneratorFin_ibp_integral hf hg]

end GaussianFin

end
