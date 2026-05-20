/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hypercontractivity and the Gross Equivalence

A *symmetric Markov semigroup* `P_t` on a probability space is
hypercontractive if it maps `L^p → L^q` for suitable `(p, q, t)`. Nelson
(1973) proved this for the OU semigroup; Gross (1975) showed the
equivalence with the log-Sobolev inequality.

## Main definitions

- `MarkovSemigroup` — a symmetric Markov semigroup on a probability
  space, carried by bounded linear operators on `L²(μ)`
  (`Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`).
- `DirichletMarkovSemigroup` — bundles a `MarkovSemigroup` with the
  semigroup's canonical Dirichlet form (the user supplies the form
  data plus the right-derivative-at-zero compatibility on a core
  algebra).
- `MarkovSemigroup.IsHypercontractive` — `‖P_t f‖_{L^q} ≤ ‖f‖_{L^p}`
  when `q ≤ 1 + (p − 1) e^{2ρt}`, formulated with an `L²` source plus
  an explicit `MemLp` hypothesis for the input `L^p` exponent.

## Main results (postulated as textbook axioms)

- `gross_lsi_implies_hypercontractive` — LSI for the bundled form ⇒
  hypercontractivity of the bundled semigroup.
- `gross_hypercontractive_implies_lsi` — converse.
- `gross_equivalence` — LSI ⇔ hypercontractivity.

## Why bundle?

The form-vs-semigroup link `E(f, g) = -(d/dt)|_{t=0+} ⟨[f], P_t [g]⟩` is
essential for Gross. Without it the two are unrelated and Gross's
theorem has no content. Bundling them into a single structure
(`DirichletMarkovSemigroup`) makes the link a structural invariant
rather than a side hypothesis.

The semigroup is the *primary* datum: for symmetric Markov semigroups,
the Dirichlet form is canonically determined (Fukushima–Oshima–Takeda
construction). The user-supplied `energy`/`IsCore` fields are a
certified presentation of that canonical form on a chosen core
algebra.

## References

- Nelson, "The free Markoff field," J. Funct. Anal. 12 (1973)
- Gross, "Logarithmic Sobolev inequalities," Amer. J. Math. 97 (1975)
- Bakry-Gentil-Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, §1.3-1.4 and §5.2
- Fukushima-Oshima-Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, de Gruyter, 1994, §1.3
- Simon, *The P(φ)₂ Euclidean QFT*, Princeton, 1974, Ch. I
-/

import MarkovSemigroups.Abstract.DirichletForm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ENNReal Set
open scoped ENNReal InnerProductSpace

noncomputable section

/-- A *symmetric Markov semigroup* on a probability space `(X, μ)`.

This is the standard setup for Gross's LSI/HC equivalence: a strongly
continuous *symmetric* contraction semigroup on `L²(μ)` preserving
positivity and any a.e.-constant-`1` element.

Time parameter `t : ℝ` is conventionally only meaningful for `t ≥ 0` —
all properties below are stated under that condition. Restricting to
`t ≥ 0` (rather than allowing all of `ℝ`) avoids the trap where a
two-sided contraction semigroup is forced by Stone's theorem to be a
group of isometries with skew-adjoint generator, incompatible with the
self-adjointness implied by symmetry. -/
structure MarkovSemigroup (X : Type*) [MeasurableSpace X] where
  /-- Reference probability measure. -/
  μ : Measure X
  /-- The measure is a probability measure. -/
  hμ : IsProbabilityMeasure μ
  /-- Bounded linear operator on `L²(μ)` at each time `t`. -/
  P : ℝ → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  /-- `P 0 = id`. -/
  P_zero : P 0 = ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)
  /-- Semigroup property (for `s, t ≥ 0`). -/
  P_semigroup : ∀ s t, 0 ≤ s → 0 ≤ t → P (s + t) = (P s).comp (P t)
  /-- Strong continuity at `t = 0+`. -/
  P_strong_cont : ∀ f : Lp ℝ 2 μ,
    Filter.Tendsto (fun t : ℝ => P t f) (nhdsWithin 0 (Set.Ici 0)) (nhds f)
  /-- Operator-norm contraction on `L²(μ)`. -/
  P_contraction : ∀ t, 0 ≤ t → ‖P t‖ ≤ 1
  /-- Markov property: `P_t` fixes any a.e.-constant-`1` element of `L²(μ)`. -/
  P_conservation : ∀ t, 0 ≤ t → ∀ f : Lp ℝ 2 μ,
    (∀ᵐ x ∂μ, (f : X → ℝ) x = 1) → P t f = f
  /-- Positivity preservation on `L²(μ)`. -/
  P_positivity : ∀ t, 0 ≤ t → ∀ f : Lp ℝ 2 μ, 0 ≤ f → 0 ≤ P t f
  /-- Symmetry of `P_t` on `L²(μ)`. -/
  P_symmetric : ∀ t, 0 ≤ t → ∀ f g : Lp ℝ 2 μ,
    ⟪f, P t g⟫_ℝ = ⟪P t f, g⟫_ℝ

attribute [instance] MarkovSemigroup.hμ

namespace MarkovSemigroup

variable {X : Type*} [MeasurableSpace X]

/-- Each `P_t` is self-adjoint on `L²(μ)` by the symmetry field. -/
lemma isSelfAdjoint (S : MarkovSemigroup X) {t : ℝ} (ht : 0 ≤ t) :
    IsSelfAdjoint (S.P t) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  simpa using (S.P_symmetric t ht f g).symm

/-- **L^∞-contraction.** For a symmetric Markov semigroup with conservation
of constants (i.e., `P_t 1 = 1`), if `|f y| ≤ M` a.e. then
`|(P_t f) y| ≤ M` a.e. Standard textbook fact derivable purely from the
existing `MarkovSemigroup` fields (no extra hypothesis needed): the trick
is `0 ≤ Lp.const M - f` (a.e. from the bound) + `P_positivity` +
`P_conservation` (used to deduce `P_t (Lp.const M) = Lp.const M` via
`Lp.const M = M • Lp.const 1`). -/
lemma Linfty_contraction (S : MarkovSemigroup X) {t : ℝ} (ht : 0 ≤ t)
    {f : Lp ℝ 2 S.μ} {M : ℝ}
    (hf : ∀ᵐ y ∂S.μ, |(f : X → ℝ) y| ≤ M) :
    ∀ᵐ y ∂S.μ, |(S.P t f : X → ℝ) y| ≤ M := by
  haveI : IsFiniteMeasure S.μ := inferInstance
  set Mlp : Lp ℝ 2 S.μ := Lp.const 2 S.μ M with hMlp_def
  have hMlp_coe : (Mlp : X → ℝ) =ᵐ[S.μ] fun _ => M := Lp.coeFn_const 2 S.μ M
  -- Conservation: P_t (Lp.const 1) = Lp.const 1.
  have hPt_const1 : S.P t (Lp.const 2 S.μ (1:ℝ)) = Lp.const 2 S.μ (1:ℝ) := by
    refine S.P_conservation t ht _ ?_
    filter_upwards [Lp.coeFn_const 2 S.μ (1:ℝ)] with x hx
    simpa using hx
  -- Lp.const M = M • Lp.const 1 (Lp identifies a.e. equal functions).
  have hMlp_smul : Mlp = M • Lp.const 2 S.μ (1:ℝ) := by
    refine Lp.ext ?_
    filter_upwards [hMlp_coe, Lp.coeFn_smul M (Lp.const 2 S.μ (1:ℝ)),
                    Lp.coeFn_const 2 S.μ (1:ℝ)] with y h1 h2 h3
    simp [h1, h2, h3]
  -- Hence P_t (Lp.const M) = Lp.const M.
  have hPt_Mlp : S.P t Mlp = Mlp := by
    calc S.P t Mlp
        = S.P t (M • Lp.const 2 S.μ (1:ℝ)) := by rw [hMlp_smul]
      _ = M • S.P t (Lp.const 2 S.μ (1:ℝ)) := (S.P t).map_smul M _
      _ = M • Lp.const 2 S.μ (1:ℝ) := by rw [hPt_const1]
      _ = Mlp := hMlp_smul.symm
  -- Upper bound: P_t f ≤ M pointwise a.e. via 0 ≤ Mlp - f in Lp.
  have h_upper : ∀ᵐ y ∂S.μ, (S.P t f : X → ℝ) y ≤ M := by
    -- The a.e.-pointwise nonneg of ↑↑(Mlp - f), via Lp.coeFn_sub bridge.
    have h_diff_ae : 0 ≤ᵐ[S.μ] (↑↑(Mlp - f) : X → ℝ) := by
      filter_upwards [hf, hMlp_coe, Lp.coeFn_sub Mlp f] with y hy hMy hSubY
      have : (↑↑(Mlp - f) : X → ℝ) y = M - (f : X → ℝ) y := by
        rw [hSubY]; simp [hMy]
      rw [Pi.zero_apply, this]
      linarith [le_of_abs_le hy]
    have h_diff_nn : (0 : Lp ℝ 2 S.μ) ≤ Mlp - f := (Lp.coeFn_nonneg _).mp h_diff_ae
    have h_pt_diff_nn : (0 : Lp ℝ 2 S.μ) ≤ S.P t (Mlp - f) :=
      S.P_positivity t ht _ h_diff_nn
    have h_pt_orbit_sub : S.P t (Mlp - f) = Mlp - S.P t f := by
      rw [map_sub, hPt_Mlp]
    rw [h_pt_orbit_sub] at h_pt_diff_nn
    have h_ae := (Lp.coeFn_nonneg _).mpr h_pt_diff_nn
    filter_upwards [h_ae, Lp.coeFn_sub Mlp (S.P t f), hMlp_coe] with y hy hSub hMy
    have h_pt : (↑↑(Mlp - S.P t f) : X → ℝ) y = M - (S.P t f : X → ℝ) y := by
      rw [hSub]; simp [hMy]
    rw [Pi.zero_apply, h_pt] at hy
    linarith
  -- Lower bound: -M ≤ P_t f pointwise a.e. via 0 ≤ Mlp + f in Lp.
  have h_lower : ∀ᵐ y ∂S.μ, (-M : ℝ) ≤ (S.P t f : X → ℝ) y := by
    have h_sum_ae : 0 ≤ᵐ[S.μ] (↑↑(Mlp + f) : X → ℝ) := by
      filter_upwards [hf, hMlp_coe, Lp.coeFn_add Mlp f] with y hy hMy hAddY
      have : (↑↑(Mlp + f) : X → ℝ) y = M + (f : X → ℝ) y := by
        rw [hAddY]; simp [hMy]
      rw [Pi.zero_apply, this]
      linarith [neg_le_of_abs_le hy]
    have h_sum_nn : (0 : Lp ℝ 2 S.μ) ≤ Mlp + f := (Lp.coeFn_nonneg _).mp h_sum_ae
    have h_pt_sum_nn : (0 : Lp ℝ 2 S.μ) ≤ S.P t (Mlp + f) :=
      S.P_positivity t ht _ h_sum_nn
    have h_pt_orbit_add : S.P t (Mlp + f) = Mlp + S.P t f := by
      rw [map_add, hPt_Mlp]
    rw [h_pt_orbit_add] at h_pt_sum_nn
    have h_ae := (Lp.coeFn_nonneg _).mpr h_pt_sum_nn
    filter_upwards [h_ae, Lp.coeFn_add Mlp (S.P t f), hMlp_coe] with y hy hAdd hMy
    have h_pt : (↑↑(Mlp + S.P t f) : X → ℝ) y = M + (S.P t f : X → ℝ) y := by
      rw [hAdd]; simp [hMy]
    rw [Pi.zero_apply, h_pt] at hy
    linarith
  filter_upwards [h_upper, h_lower] with y hyu hyl
  exact abs_le.mpr ⟨hyl, hyu⟩

/-- **L^∞ orbit ⇒ all L^p memberships.** Companion to `Linfty_contraction`:
once the orbit is uniformly bounded a.e., it lies in every `MemLp p` on
the finite measure `S.μ`. -/
lemma orbit_memLp (S : MarkovSemigroup X) {t : ℝ} (ht : 0 ≤ t)
    {f : Lp ℝ 2 S.μ} {M : ℝ}
    (hf : ∀ᵐ y ∂S.μ, |(f : X → ℝ) y| ≤ M) (p : ℝ≥0∞) :
    MemLp ((S.P t f : X → ℝ)) p S.μ := by
  haveI : IsFiniteMeasure S.μ := inferInstance
  refine MemLp.of_bound (Lp.aestronglyMeasurable _) M ?_
  filter_upwards [S.Linfty_contraction ht hf] with y hy
  simpa using hy

/-- **Lower-bound contraction.** Companion to `Linfty_contraction`: if
`f ≥ ε` a.e., then `(P_t f) ≥ ε` a.e. (for `t ≥ 0`). Same template:
`0 ≤ f - Lp.const ε` (a.e.) + `P_positivity` + `P_t (Lp.const ε) = Lp.const ε`
(via conservation + scalar). The dual of `Linfty_contraction`, but stated
in *one-sided* form because Gross-style positivity arguments only need
the lower bound `(P_s f) ≥ ε`, not |·| ≤ M. -/
lemma orbit_lower_bound (S : MarkovSemigroup X) {t : ℝ} (ht : 0 ≤ t)
    {f : Lp ℝ 2 S.μ} {ε : ℝ}
    (hf : ∀ᵐ y ∂S.μ, ε ≤ (f : X → ℝ) y) :
    ∀ᵐ y ∂S.μ, ε ≤ (S.P t f : X → ℝ) y := by
  haveI : IsFiniteMeasure S.μ := inferInstance
  set εlp : Lp ℝ 2 S.μ := Lp.const 2 S.μ ε with hεlp_def
  have hεlp_coe : (εlp : X → ℝ) =ᵐ[S.μ] fun _ => ε := Lp.coeFn_const 2 S.μ ε
  have hPt_const1 : S.P t (Lp.const 2 S.μ (1:ℝ)) = Lp.const 2 S.μ (1:ℝ) := by
    refine S.P_conservation t ht _ ?_
    filter_upwards [Lp.coeFn_const 2 S.μ (1:ℝ)] with x hx
    simpa using hx
  have hεlp_smul : εlp = ε • Lp.const 2 S.μ (1:ℝ) := by
    refine Lp.ext ?_
    filter_upwards [hεlp_coe, Lp.coeFn_smul ε (Lp.const 2 S.μ (1:ℝ)),
                    Lp.coeFn_const 2 S.μ (1:ℝ)] with y h1 h2 h3
    simp [h1, h2, h3]
  have hPt_εlp : S.P t εlp = εlp := by
    calc S.P t εlp
        = S.P t (ε • Lp.const 2 S.μ (1:ℝ)) := by rw [hεlp_smul]
      _ = ε • S.P t (Lp.const 2 S.μ (1:ℝ)) := (S.P t).map_smul ε _
      _ = ε • Lp.const 2 S.μ (1:ℝ) := by rw [hPt_const1]
      _ = εlp := hεlp_smul.symm
  -- 0 ≤ f - εlp via the a.e. bound.
  have h_diff_ae : 0 ≤ᵐ[S.μ] (↑↑(f - εlp) : X → ℝ) := by
    filter_upwards [hf, hεlp_coe, Lp.coeFn_sub f εlp] with y hy hMy hSubY
    have : (↑↑(f - εlp) : X → ℝ) y = (f : X → ℝ) y - ε := by
      rw [hSubY]; simp [hMy]
    rw [Pi.zero_apply, this]
    linarith
  have h_diff_nn : (0 : Lp ℝ 2 S.μ) ≤ f - εlp := (Lp.coeFn_nonneg _).mp h_diff_ae
  have h_pt_diff_nn : (0 : Lp ℝ 2 S.μ) ≤ S.P t (f - εlp) :=
    S.P_positivity t ht _ h_diff_nn
  have h_pt_orbit_sub : S.P t (f - εlp) = S.P t f - εlp := by
    rw [map_sub, hPt_εlp]
  rw [h_pt_orbit_sub] at h_pt_diff_nn
  have h_ae := (Lp.coeFn_nonneg _).mpr h_pt_diff_nn
  filter_upwards [h_ae, Lp.coeFn_sub (S.P t f) εlp, hεlp_coe] with y hy hSub hMy
  have h_pt : (↑↑(S.P t f - εlp) : X → ℝ) y = (S.P t f : X → ℝ) y - ε := by
    rw [hSub]; simp [hMy]
  rw [Pi.zero_apply, h_pt] at hy
  linarith

/-- A symmetric Markov semigroup is *hypercontractive* with rate `ρ > 0`
if `P_t : L^p → L^q` is a contraction whenever
`q ≤ 1 + (p − 1) · e^{2ρt}`:

  `‖P_t f‖_{L^q(μ)} ≤ ‖f‖_{L^p(μ)}`.

The source is the `L²(μ)` carrier, together with an explicit `MemLp`
hypothesis at exponent `p`. This handles both `p < 2` and `p > 2`
without changing the abstract carrier. -/
def IsHypercontractive (S : MarkovSemigroup X) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ (p q t : ℝ),
    1 < p → p ≤ q → 0 < t →
    q ≤ 1 + (p - 1) * Real.exp (2 * ρ * t) →
    ∀ f : Lp ℝ 2 S.μ,
      MemLp ((⇑f) : X → ℝ) (ENNReal.ofReal p) S.μ →
      eLpNorm (((S.P t f) : X → ℝ)) (ENNReal.ofReal q) S.μ ≤
        eLpNorm ((⇑f) : X → ℝ) (ENNReal.ofReal p) S.μ

end MarkovSemigroup

/-- A *Dirichlet-Markov semigroup*: a symmetric Markov semigroup
bundled with its canonical Dirichlet form.

For a symmetric Markov semigroup the Dirichlet form is uniquely
determined by the semigroup as

  `E(f, g) = lim_{t↘0} (1/t) · ⟨[f], (I − P_t)[g]⟩
          = -(d/dt)|_{t=0+} ⟨[f], P_t[g]⟩`

(Fukushima–Oshima–Takeda construction). The user supplies a candidate
form `energy` together with an admissible core algebra `IsCore`, and
asserts via `energy_eq_deriv` that the candidate equals the canonical
form on the core (as a right-derivative at `0`). -/
structure DirichletMarkovSemigroup (X : Type*) [MeasurableSpace X]
    extends MarkovSemigroup X where
  /-- The Dirichlet form `E(f, g)`. -/
  energy : (X → ℝ) → (X → ℝ) → ℝ
  /-- Energy is symmetric. -/
  energy_symm : ∀ f g, energy f g = energy g f
  /-- Energy is nonnegative on the diagonal. -/
  energy_nonneg : ∀ f, 0 ≤ energy f f
  /-- Admissible core functions. -/
  IsCore : (X → ℝ) → Prop
  /-- Constants are core. -/
  IsCore_const : ∀ c : ℝ, IsCore (fun _ => c)
  /-- Core is closed under addition. -/
  IsCore_add : ∀ {f g}, IsCore f → IsCore g → IsCore (f + g)
  /-- Core is closed under scalar multiplication. -/
  IsCore_smul : ∀ (c : ℝ) {f}, IsCore f → IsCore (c • f)
  /-- **Strict-positive rpow closure** (Gross's strictly-positive escape).
  When `f` is in the core and `f ≥ ε > 0` a.e. for some explicit
  `ε > 0`, then `x ↦ f x ^ r` is also in the core for any real `r`. This
  is the standard "Markovian core" closure under smooth functional
  calculus, restricted to strictly positive elements (which is all we
  need for the Gross argument — see
  `plans/gross-design-strictly-positive-escape.md`). Note that the
  axiom uses `Real.rpow` directly (the syntactic form appearing in
  `grossPow`), so no a.e./pointwise bridging is needed; the null set
  where `f y ≤ 0` is benign because `rpow_def_of_neg` matches the
  convention used everywhere in this file (compare BGL Ch 1, "algebra
  of admissible test functions"). Mathematically, for concrete cores
  like `C^∞_b(ℝ^n)` on Gaussian measure, this is immediate: adding a
  positive constant to a `C^∞_b` element gives `f ≥ ε > 0` *everywhere*,
  and `f^r` is then `C^∞_b` by chain rule. -/
  IsCore_rpow_pos_strict : ∀ {f : X → ℝ} (_ : IsCore f) {ε : ℝ} (_ : 0 < ε),
    (∀ᵐ y ∂μ, ε ≤ f y) → ∀ (r : ℝ), IsCore (fun x => f x ^ r)
  /-- **L^∞ membership.** Every core function is essentially bounded.
  This is the standard BGL hypothesis on the "algebra of admissible
  test functions" (cf. BGL §1.4: "an algebra of *bounded* functions
  in the generator domain"). For `C^∞_b`-style cores (`IsCoreFin`,
  Schwartz-with-Gaussian-tweaks, polynomial cores on probability
  measures) this is immediate from the bounded-derivatives part of
  the definition. Needed by `grossPow_hasDerivWithinAt` to invoke
  `hasDerivAt_integral_rpow_exponent` (which requires a uniform
  bound `|w y| ≤ M` on the integrand) and to combine with `hf_pos`
  for `ε ≤ f ≤ M` framing. -/
  IsCore_memLp_top : ∀ {f : X → ℝ}, IsCore f → ∃ M : ℝ, ∀ᵐ y ∂μ, |f y| ≤ M
  /-- Energy is bilinear on the left. -/
  energy_add_left : ∀ f₁ f₂ g, IsCore f₁ → IsCore f₂ → IsCore g →
    energy (f₁ + f₂) g = energy f₁ g + energy f₂ g
  /-- Energy is homogeneous on the left. -/
  energy_smul_left : ∀ (c : ℝ) f g, IsCore f → IsCore g →
    energy (c • f) g = c * energy f g
  /-- Constants have zero energy. -/
  energy_const : ∀ c : ℝ, energy (fun _ => c) (fun _ => c) = 0
  /-- Every core function lies in `L²(μ)`. -/
  IsCore_memLp : ∀ {f}, IsCore f → MemLp f 2 μ
  /-- **Generator–Dirichlet-form compatibility.** The energy form is
  the (negated) right-derivative-at-zero of the `L²(μ)` pairing
  `⟨[f], P_t[g]⟩`. -/
  energy_eq_deriv : ∀ f g (hf : IsCore f) (hg : IsCore g),
    let coreToL2 : ∀ {h : X → ℝ}, IsCore h → Lp ℝ 2 μ :=
      fun {h} hh => (IsCore_memLp hh).toLp h
    HasDerivWithinAt
      (fun t : ℝ => ⟪coreToL2 hf, P t (coreToL2 hg)⟫_ℝ)
      (-energy f g) (Set.Ici 0) 0

namespace DirichletMarkovSemigroup

variable {X : Type*} [MeasurableSpace X]

/-- View a core function as an element of `L²(μ)`. -/
def coreToL2 (D : DirichletMarkovSemigroup X) {f : X → ℝ} (hf : D.IsCore f) :
    Lp ℝ 2 D.μ :=
  (D.IsCore_memLp hf).toLp f

/-- The Dirichlet form data of a `DirichletMarkovSemigroup` packages
into a `DirichletSpace`. -/
@[reducible]
def toDirichletSpace (D : DirichletMarkovSemigroup X) : DirichletSpace X where
  μ := D.μ
  hμ := D.hμ
  energy := D.energy
  energy_symm := D.energy_symm
  energy_nonneg := D.energy_nonneg
  IsCore := D.IsCore
  IsCore_const := D.IsCore_const
  IsCore_add := D.IsCore_add
  IsCore_smul := D.IsCore_smul
  energy_add_left := D.energy_add_left
  energy_smul_left := D.energy_smul_left
  energy_const := D.energy_const

/-- LSI for the bundled structure: LSI for the underlying Dirichlet form. -/
def SatisfiesLogSobolev (D : DirichletMarkovSemigroup X) (ρ : ℝ) : Prop :=
  let _ : DirichletSpace X := D.toDirichletSpace
  DirichletSpace.SatisfiesLogSobolev (X := X) ρ

/-- Hypercontractivity for the bundled structure: hypercontractivity
of the underlying `L²` semigroup. -/
def IsHypercontractive (D : DirichletMarkovSemigroup X) (ρ : ℝ) : Prop :=
  D.toMarkovSemigroup.IsHypercontractive ρ

end DirichletMarkovSemigroup

/-! ## Stroock–Varopoulos inequality (intermediate-step lemma) -/

/-- **Stroock–Varopoulos inequality.** AXIOM
(textbook bridge, restated on the `L²(μ)`-carrier-based bundled
structure).

For a `DirichletMarkovSemigroup` `D`, any nonnegative `f ∈ D.IsCore`,
any `p ≥ 2`, and assuming `f^{p/2}` and `f^{p-1}` lie in the core:

  `(4(p − 1) / p²) · E(f^{p/2}, f^{p/2}) ≤ E(f, f^{p−1})`.

In operator form (using `E(f, g) = -⟨[f], L[g]⟩` on the core):
  `-⟨[f^{p−1}], L[f]⟩ ≥ (4(p − 1) / p²) · ⟨-[L(f^{p/2})], [f^{p/2}]⟩`.

This is the key intermediate-step lemma in Gross's proof that LSI
implies hypercontractivity. Combined with LSI applied to `f^{p/2}`
and the chain rule for `(d/dt) ‖P_t f‖_p^p`, it closes the
differential inequality `(d/dt) ‖P_t f‖_{q(t)} ≤ 0` along the path
`q(t) = 1 + (p − 1) · e^{2ρt}`. -/
axiom stroock_varopoulos {X : Type*} [MeasurableSpace X]
    (D : DirichletMarkovSemigroup X) (p : ℝ) (hp : 2 ≤ p)
    (f : X → ℝ) (hf : D.IsCore f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_p_half : D.IsCore (fun x => f x ^ (p / 2)))
    (hf_p_one : D.IsCore (fun x => f x ^ (p - 1))) :
    (4 * (p - 1) / p ^ 2) *
      D.energy (fun x => f x ^ (p / 2)) (fun x => f x ^ (p / 2)) ≤
    D.energy f (fun x => f x ^ (p - 1))

/-! ## Gross's theorem (postulated as textbook axioms) -/

/-- **Postulated (Gross 1975, Theorem 1).** LSI implies
hypercontractivity for the bundled `L²(μ)` semigroup.

The proof uses the semigroup interpolation method: differentiate
`‖P_t f‖_{L^{q(t)}}` along `q(t) = 1 + (p − 1) e^{2ρt}` and show the
derivative is `≤ 0` via LSI applied to `|f|^{q/2}`. The Dirichlet form
enters through the compatibility field `energy_eq_deriv`, with
Stroock–Varopoulos supplying the key energy comparison.

**Note on `hρ`**: the explicit `0 < ρ` hypothesis is required to
firewall against a soundness trap. `SatisfiesLogSobolev D ρ` is
**trivially true** for `ρ ≤ 0` (the LSI inequality `ρ · Ent(f²) ≤ 2 · E(f, f)`
has LHS `≤ 0` and RHS `≥ 0`), while `IsHypercontractive` bakes in
`0 < ρ`. Without `hρ` the axiom would prove `0 < ρ` from a vacuous
hypothesis (i.e. `0 < ρ` for any `ρ`), yielding `False`. Flagged by
gemini-3.1-pro-preview 2026-05-13 re-vet of the Lp-carrier refactor. -/
axiom gross_lsi_implies_hypercontractive {X : Type*} [MeasurableSpace X]
    (D : DirichletMarkovSemigroup X) (ρ : ℝ) (hρ : 0 < ρ)
    (h_lsi : D.SatisfiesLogSobolev ρ) :
    D.toMarkovSemigroup.IsHypercontractive ρ

/-- **Postulated (Gross 1975, Theorem 2).** Hypercontractivity of the
bundled `L²(μ)` semigroup implies LSI for the bundled Dirichlet form.

The proof differentiates the hypercontractive bound at `t = 0` with
`p = 2`, `q = 2 + ε`, and takes `ε → 0`. -/
axiom gross_hypercontractive_implies_lsi {X : Type*} [MeasurableSpace X]
    (D : DirichletMarkovSemigroup X) (ρ : ℝ)
    (h_hyp : D.toMarkovSemigroup.IsHypercontractive ρ) :
    D.SatisfiesLogSobolev ρ

/-! ## H0 — hypothesis-parameterised Gross (Route A scaffold)

The discharge route for `gross_lsi_implies_hypercontractive` keeps the
abstract `DirichletMarkovSemigroup` (and its shipped sorry-free
GaussianFin instance) **unchanged**: the strong-generator facts are
explicit `Prop` hypotheses, not new structural fields — the same
leaf-placement design already used for `stroock_varopoulos`,
Gemini-vetted (passes 1–4). They are discharged per instance at the
call-site (GaussianFin in gaussian-hilbert). See
`plans/gross-discharge.md` (§2–§3) and
`plans/gaussianfin-0b-readiness.md`. -/

variable {X : Type*} [MeasurableSpace X]

/-- **Core invariance under the semigroup.** Applying the `L²`
semigroup `P_t` (`t ≥ 0`) to (the `L²` class of) a core function
yields the `L²` class of *some* core function. Phrased `L²`-side
because the abstract structure exposes only the `Lp` operator, not a
function-level action. Discharged for GaussianFin by
`ouSemigroupFin_preserves_IsCore` (`g' := ouSemigroupFin t g`). -/
def CoreSemigroupInvariant (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ {g : X → ℝ} (hg : D.IsCore g),
    ∃ (g' : X → ℝ) (hg' : D.IsCore g'),
      D.P t (D.coreToL2 hg) = D.coreToL2 hg'

/-- **Generator–form compatibility (strong).** `coreToL2 f ∈ dom(A)`
with the difference quotient converging in `L²`-*norm* (not merely
weakly), and the generator value `Af` pinned by the Dirichlet form
against every core test function. Strengthens `energy_eq_deriv`
(weak, scalar-paired). Gemini pass-3 green-lit; uses the explicit
`nhdsWithin (0:ℝ) (Set.Ioi 0)` / `nhds` idiom of this file (matching
`P_strong_cont`). Discharged for GaussianFin via the proved 1D linear
heat equation lifted + pointwise→strong-`L²` DCT. -/
def GeneratorCompat (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ {f : X → ℝ} (hf : D.IsCore f), ∃ Af : Lp ℝ 2 D.μ,
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (D.P t (D.coreToL2 hf) - D.coreToL2 hf))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Af)
    ∧ ∀ {g : X → ℝ} (hg : D.IsCore g),
        ⟪D.coreToL2 hg, Af⟫_ℝ = - D.energy g f

/-- **Stroock–Varopoulos, generator-paired** (Gemini pass-3 trap fix:
`u^{q-1} ∉ core` makes the abstract `E(u,u^{q-1})` unusable; pass-4
binding fix: `GeneratorCompat` is existential, so the generator
element `Au` + its strong-limit witness are passed explicitly rather
than via a global `A`). The core-power hypotheses match the existing
`stroock_varopoulos` axiom (cleaner than `MemLp.toLp` packaging and
equivalent for the GaussianFin discharge, which has the core
powers). `_hq`/`_hu_half` are contract antecedents (the inequality is
only claimed for `q ≥ 2` with `u^{q/2}` core); `_`-prefixed per the
Mathlib convention for binders required by the statement's shape but
not referenced in the body — the discharger still supplies them
positionally. -/
def StroockVaropoulos (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ {u : X → ℝ} (hu : D.IsCore u) (q : ℝ) (_hq : 2 ≤ q)
    (_hu_half : D.IsCore (fun x => u x ^ (q / 2)))
    (hu_one : D.IsCore (fun x => u x ^ (q - 1)))
    (Au : Lp ℝ 2 D.μ),
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (D.P t (D.coreToL2 hu) - D.coreToL2 hu))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Au) →
    (4 * (q - 1) / q ^ 2) *
        D.energy (fun x => u x ^ (q / 2)) (fun x => u x ^ (q / 2))
      ≤ ⟪D.coreToL2 hu_one, - Au⟫_ℝ

/-! **Gross 1975, Theorem 1 — hypothesis-parameterised (Route A
target).** The predicates `CoreSemigroupInvariant` / `GeneratorCompat`
/ `StroockVaropoulos` (above) live here; the **theorem and its proof**
`gross_lsi_implies_hypercontractive_of_hypotheses` (LSI ⇒
hypercontractivity given those three; Gross's differentiation
argument — Phases P2/P3 of `plans/gross-discharge.md`) are relocated
to `MarkovSemigroups.Abstract.GrossODE` (which imports this file), so
the heavy ODE scaffolding does not bloat this module. The existing
`gross_lsi_implies_hypercontractive` axiom is retained (non-breaking —
downstream `gaussian-hilbert` keeps compiling) until the relocated
theorem is proved and the call-site is rewired. -/

namespace DirichletMarkovSemigroup

variable {X : Type*} [MeasurableSpace X]

/-- Gross's theorem (forward direction): LSI ⇒ hypercontractivity.

The `hρ : 0 < ρ` hypothesis firewalls the `ρ ≤ 0` soundness trap
documented at `gross_lsi_implies_hypercontractive`. -/
theorem hypercontractive_of_logSobolev (D : DirichletMarkovSemigroup X)
    (ρ : ℝ) (hρ : 0 < ρ) (h_lsi : D.SatisfiesLogSobolev ρ) :
    D.IsHypercontractive ρ := by
  show D.toMarkovSemigroup.IsHypercontractive ρ
  exact gross_lsi_implies_hypercontractive D ρ hρ h_lsi

/-- Gross's theorem (reverse direction): hypercontractivity ⇒ LSI. -/
theorem logSobolev_of_hypercontractive (D : DirichletMarkovSemigroup X)
    (ρ : ℝ) (h_hyp : D.IsHypercontractive ρ) :
    D.SatisfiesLogSobolev ρ := by
  change D.toMarkovSemigroup.IsHypercontractive ρ at h_hyp
  exact gross_hypercontractive_implies_lsi D ρ h_hyp

/-- The Gross equivalence: LSI ↔ hypercontractivity for a
`DirichletMarkovSemigroup`. The forward direction requires `0 < ρ`
(see `hypercontractive_of_logSobolev`); the reverse derives `ρ > 0`
from the `IsHypercontractive` predicate's built-in `0 < ρ` field. -/
theorem gross_equivalence (D : DirichletMarkovSemigroup X) (ρ : ℝ) (hρ : 0 < ρ) :
    D.SatisfiesLogSobolev ρ ↔ D.IsHypercontractive ρ :=
  ⟨D.hypercontractive_of_logSobolev ρ hρ,
   D.logSobolev_of_hypercontractive ρ⟩

/-! ## Direct consequence: the semigroup improves integrability -/

/-- Direct application of hypercontractivity to an `L²(μ)` function
that also lies in `L^p(μ)`:

  `‖P_t f‖_{L^q(μ)} ≤ ‖f‖_{L^p(μ)}`

whenever `q ≤ 1 + (p − 1) e^{2ρt}`. -/
theorem semigroup_lp_improvement (D : DirichletMarkovSemigroup X)
    (ρ : ℝ) (h_hyp : D.IsHypercontractive ρ)
    (f : Lp ℝ 2 D.μ) (p q : ℝ)
    (hf_memLp : MemLp ((⇑f) : X → ℝ) (ENNReal.ofReal p) D.μ)
    (hp : 1 < p) (hpq : p ≤ q)
    (t : ℝ) (ht : 0 < t)
    (h_bound : q ≤ 1 + (p - 1) * Real.exp (2 * ρ * t)) :
    eLpNorm (((D.P t f) : X → ℝ)) (ENNReal.ofReal q) D.μ ≤
      eLpNorm ((⇑f) : X → ℝ) (ENNReal.ofReal p) D.μ :=
  h_hyp.2 p q t hp hpq ht h_bound f hf_memLp

end DirichletMarkovSemigroup

end
