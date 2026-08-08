/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Two-Point Space: Simplest BakryEmerySpace Instance

The two-point space {0, 1} with uniform measure μ = ½(δ₀ + δ₁)
and continuous-time Markov chain with rate α > 0:

  P_t f(i) = ½(1 + e^{-2αt}) f(i) + ½(1 - e^{-2αt}) f(1-i)

The carré du champ and curvature:
  Γ(f,g)(i) = α · (f 0 - f 1)(g 0 - g 1) / 2
  E(f,f) = α · (f 0 - f 1)² / 2
  ρ = 2α  (spectral gap)

All `BakryEmerySpace` fields are satisfiable for `{0,1}` **except** the
diffusion-specific ones: the Leibniz/chain rule `Γ_leibniz` is *false* for this jump
process, so no `BakryEmerySpace TwoPoint` instance can exist. `gamma_leibniz_fails`
proves that failure explicitly — a finite continuous-time Markov chain is a jump
process, not a diffusion (BGL §1.6).
-/

import MarkovSemigroups.Diffusion.CarreDuChamp
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option linter.unusedSimpArgs false

open MeasureTheory Filter Set Real

noncomputable section

/-- The two-point type. -/
inductive TwoPoint : Type where
  | zero : TwoPoint
  | one : TwoPoint
  deriving DecidableEq

instance : MeasurableSpace TwoPoint := ⊤
instance : MeasurableSingletonClass TwoPoint := ⟨fun _ => trivial⟩

instance : Fintype TwoPoint where
  elems := {.zero, .one}
  complete := fun x => by cases x <;> simp

namespace TwoPoint

/-- The "flip" map: 0 ↦ 1, 1 ↦ 0. -/
def flip : TwoPoint → TwoPoint
  | .zero => .one
  | .one => .zero

@[simp] theorem flip_flip (i : TwoPoint) : flip (flip i) = i := by cases i <;> rfl
@[simp] theorem flip_zero : flip .zero = .one := rfl
@[simp] theorem flip_one : flip .one = .zero := rfl

/-- Cases exhaustion: every function on TwoPoint is determined by its values at .zero and .one. -/
theorem eq_of_values {f g : TwoPoint → ℝ} (h0 : f .zero = g .zero) (h1 : f .one = g .one) :
    f = g := by
  ext i; cases i <;> assumption

/-- The uniform measure on {0, 1}: μ = ½ δ₀ + ½ δ₁. -/
def uniformMeasure : Measure TwoPoint :=
  (2 : ENNReal)⁻¹ • Measure.count

private theorem fintype_card_eq : Fintype.card TwoPoint = 2 := by native_decide

private theorem count_univ_eq : Measure.count (Set.univ : Set TwoPoint) = 2 := by
  rw [Measure.count_apply_finite _ (Set.toFinite _)]
  simp [Set.Finite.toFinset, Finset.card_univ, fintype_card_eq]

private theorem ennreal_half_mul_two :
    (2 : ENNReal)⁻¹ * 2 = 1 :=
  ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance : IsFiniteMeasure uniformMeasure := by
  constructor
  simp only [uniformMeasure, Measure.smul_apply, smul_eq_mul, count_univ_eq, ennreal_half_mul_two]
  exact ENNReal.one_lt_top

/-- The uniform measure is a probability measure. -/
instance : IsProbabilityMeasure uniformMeasure := by
  constructor
  simp only [uniformMeasure, Measure.smul_apply, smul_eq_mul, count_univ_eq, ennreal_half_mul_two]

/-- Every function on TwoPoint is integrable w.r.t. uniformMeasure. -/
theorem integrable_uniformMeasure (f : TwoPoint → ℝ) :
    Integrable f uniformMeasure :=
  Integrable.of_finite

/-- Key integration lemma: ∫ f dμ = (f .zero + f .one) / 2. -/
theorem integral_uniformMeasure (f : TwoPoint → ℝ) :
    ∫ x, f x ∂uniformMeasure = (f .zero + f .one) / 2 := by
  simp only [uniformMeasure, integral_smul_measure]
  rw [integral_count]
  -- ∑ a, f a = f .zero + f .one for TwoPoint
  have : ∑ a : TwoPoint, f a = f .zero + f .one := by
    rw [show (Finset.univ : Finset TwoPoint) = {.zero, .one} from rfl]
    simp [Finset.sum_pair (show TwoPoint.zero ≠ TwoPoint.one from by decide)]
  rw [this]
  simp [ENNReal.toReal_inv]
  ring

/-- Integral of f^2. -/
theorem integral_sq_uniformMeasure (f : TwoPoint → ℝ) :
    ∫ x, (f x) ^ 2 ∂uniformMeasure = (f .zero ^ 2 + f .one ^ 2) / 2 := by
  have h := integral_uniformMeasure (fun x => (f x) ^ 2)
  simpa using h

/-! ## Semigroup, Gamma, and Energy -/

variable (α : ℝ)

/-- The coefficient c(t) = (1 + e^{-2αt})/2 in the semigroup. -/
def coeff (t : ℝ) : ℝ := (1 + exp (-2 * α * t)) / 2

theorem coeff_zero : coeff α 0 = 1 := by
  simp [coeff, exp_zero]

/-- The two-state semigroup with rate α:
  P_t f(i) = c(t) · f(i) + (1 - c(t)) · f(flip i). -/
def semigroup (t : ℝ) (f : TwoPoint → ℝ) : TwoPoint → ℝ :=
  fun i => coeff α t * f i + (1 - coeff α t) * f (flip i)

/-- Key property: the difference P_t f(.zero) - P_t f(.one) = e^{-2αt} · (f(.zero) - f(.one)). -/
theorem semigroup_diff (t : ℝ) (f : TwoPoint → ℝ) :
    semigroup α t f .zero - semigroup α t f .one =
    exp (-2 * α * t) * (f .zero - f .one) := by
  simp only [semigroup, coeff, flip_zero, flip_one]
  ring

/-- The sum P_t f(.zero) + P_t f(.one) = f(.zero) + f(.one). -/
theorem semigroup_sum (t : ℝ) (f : TwoPoint → ℝ) :
    semigroup α t f .zero + semigroup α t f .one = f .zero + f .one := by
  simp only [semigroup, coeff, flip_zero, flip_one]
  ring

/-- The carré du champ: Γ(f,g)(i) = α · (f 0 - f 1)(g 0 - g 1) / 2. -/
def Gamma (f g : TwoPoint → ℝ) : TwoPoint → ℝ :=
  fun _ => α * (f .zero - f .one) * (g .zero - g .one) / 2

/-- The energy: E(f,g) = α · (f 0 - f 1)(g 0 - g 1) / 2. -/
def energy (f g : TwoPoint → ℝ) : ℝ :=
  α * (f .zero - f .one) * (g .zero - g .one) / 2

/-! ## DirichletSpace instance -/

/-- The DirichletSpace instance for TwoPoint with rate α > 0. -/
@[reducible]
def dirichletSpace (hα : 0 < α) : DirichletSpace TwoPoint where
  μ := uniformMeasure
  hμ := inferInstance
  energy := energy α
  energy_symm := fun f g => by simp [energy]; ring
  energy_nonneg := fun f => by
    simp only [energy]
    have h1 : 0 ≤ α := le_of_lt hα
    have h2 : 0 ≤ (f .zero - f .one) * (f .zero - f .one) := mul_self_nonneg _
    nlinarith [mul_nonneg h1 h2]
  IsCore := fun _ => True
  IsCore_const := fun _ => trivial
  IsCore_add := by intros; trivial
  IsCore_smul := by intros; trivial
  energy_add_left := fun f₁ f₂ g _ _ _ => by
    simp only [energy, Pi.add_apply]; ring
  energy_smul_left := fun c f g _ _ => by
    simp only [energy, Pi.smul_apply, smul_eq_mul]; ring
  energy_const := fun c => by
    simp [energy, sub_self, mul_zero]

/-! ## Key algebraic identities for the semigroup -/

/-- exp(-2αt)^2 = exp(-4αt). -/
theorem exp_sq (t : ℝ) : exp (-2 * α * t) ^ 2 = exp (-4 * α * t) := by
  rw [sq, ← exp_add]
  ring_nf

/-- The L² norm squared of P_t f. -/
theorem semigroup_l2_sq_eq (f : TwoPoint → ℝ) (t : ℝ) :
    ∫ x, (semigroup α t f x) ^ 2 ∂uniformMeasure =
    ((f .zero + f .one) / 2) ^ 2 +
    exp (-4 * α * t) * ((f .zero - f .one) / 2) ^ 2 := by
  rw [integral_sq_uniformMeasure]
  simp only [semigroup, coeff, flip_zero, flip_one]
  have he_sq : exp (-2 * α * t) * exp (-2 * α * t) = exp (-4 * α * t) := by
    rw [← exp_add]; ring_nf
  nlinarith [he_sq,
    sq_nonneg (exp (-2 * α * t)),
    sq_nonneg (f .zero), sq_nonneg (f .one),
    sq_nonneg (f .zero - f .one), sq_nonneg (f .zero + f .one),
    sq_nonneg (exp (-2 * α * t) * f .zero - exp (-2 * α * t) * f .one),
    sq_nonneg (exp (-2 * α * t) * f .zero + exp (-2 * α * t) * f .one),
    mul_self_nonneg (exp (-2 * α * t))]

/-- Helper: the Gamma integral formula as a purely algebraic identity. -/
private theorem gamma_integral_aux (e d α_val : ℝ) :
    (α_val * (e * d) * (e * d) / 2 + α_val * (e * d) * (e * d) / 2) / 2 =
    e ^ 2 * (α_val * d ^ 2 / 2) := by ring

/-- The integral of Gamma for the semigroup output. -/
theorem integral_Gamma_semigroup (f : TwoPoint → ℝ) (t : ℝ) :
    ∫ x, Gamma α (semigroup α t f) (semigroup α t f) x ∂uniformMeasure =
    exp (-4 * α * t) * (α * (f .zero - f .one) ^ 2 / 2) := by
  rw [integral_uniformMeasure]
  simp only [Gamma, semigroup_diff]
  rw [gamma_integral_aux, exp_sq]

/-- The energy of the semigroup output. -/
theorem energy_semigroup (f : TwoPoint → ℝ) (t : ℝ) :
    energy α (semigroup α t f) (semigroup α t f) =
    exp (-4 * α * t) * energy α f f := by
  simp only [energy, semigroup_diff]
  rw [show α * (exp (-2 * α * t) * (f .zero - f .one)) *
      (exp (-2 * α * t) * (f .zero - f .one)) / 2 =
      exp (-2 * α * t) ^ 2 * (α * (f .zero - f .one) * (f .zero - f .one) / 2) from by ring]
  rw [exp_sq]

/-- Mean preservation: ∫ P_t f dμ = ∫ f dμ. -/
theorem semigroup_mean_pres (f : TwoPoint → ℝ) (t : ℝ) :
    ∫ x, semigroup α t f x ∂uniformMeasure = ∫ x, f x ∂uniformMeasure := by
  simp only [integral_uniformMeasure, semigroup_sum]

/-- Self-adjointness: ∫ (P_t f) · g dμ = ∫ f · (P_t g) dμ. -/
theorem semigroup_selfAdj (f g : TwoPoint → ℝ) (t : ℝ) :
    ∫ x, semigroup α t f x * g x ∂uniformMeasure =
    ∫ x, f x * semigroup α t g x ∂uniformMeasure := by
  simp only [integral_uniformMeasure, semigroup, coeff, flip_zero, flip_one]
  ring

/-- The L² norm of P_t f is ≤ the L² norm of f (contraction). -/
theorem semigroup_contraction_eq (hα : 0 < α) (f : TwoPoint → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    ∫ x, (semigroup α t f x) ^ 2 ∂uniformMeasure ≤
    ∫ x, (f x) ^ 2 ∂uniformMeasure := by
  rw [semigroup_l2_sq_eq, integral_sq_uniformMeasure]
  have h_ident : (f .zero ^ 2 + f .one ^ 2) / 2 =
      ((f .zero + f .one) / 2) ^ 2 + ((f .zero - f .one) / 2) ^ 2 := by ring
  rw [h_ident]
  have h_exp_le : exp (-4 * α * t) ≤ 1 :=
    exp_le_one_iff.mpr (by nlinarith)
  have h_sq_nn : 0 ≤ ((f .zero - f .one) / 2) ^ 2 := sq_nonneg _
  nlinarith [mul_le_of_le_one_left h_sq_nn h_exp_le]

/-- Variance of P_t f as a function of t. -/
theorem semigroup_variance_eq (f : TwoPoint → ℝ) (t : ℝ) :
    ∫ x, (semigroup α t f x) ^ 2 ∂uniformMeasure -
    (∫ x, f x ∂uniformMeasure) ^ 2 =
    exp (-4 * α * t) * ((f .zero - f .one) / 2) ^ 2 := by
  rw [semigroup_l2_sq_eq, integral_uniformMeasure]
  ring

/-- HasDerivWithinAt for the linear function s ↦ -4αs. -/
private theorem hasDerivWithinAt_neg_four_alpha (t : ℝ) :
    HasDerivWithinAt (fun s => -4 * α * s) (-4 * α) (Ici 0) t := by
  have h1 : HasDerivWithinAt (fun s => s) 1 (Ici 0) t := hasDerivWithinAt_id t _
  have h2 := h1.const_mul (-4 * α)
  simp only [mul_one] at h2
  exact h2

/-- The function t ↦ ∫ (P_t f)^2 dμ has a derivative at any t ≥ 0. -/
theorem semigroup_l2_sq_deriv (f : TwoPoint → ℝ) (t : ℝ) :
    HasDerivWithinAt (fun s => ∫ x, (semigroup α s f x) ^ 2 ∂uniformMeasure)
      (-2 * (exp (-4 * α * t) * (α * (f .zero - f .one) ^ 2 / 2)))
      (Ici 0) t := by
  -- Rewrite ∫ (P_s f)^2 = mean^2 + e^{-4αs} * halfDiff^2
  have heq : EqOn (fun s => ∫ x, (semigroup α s f x) ^ 2 ∂uniformMeasure)
      (fun s => ((f .zero + f .one) / 2) ^ 2 +
        exp (-4 * α * s) * ((f .zero - f .one) / 2) ^ 2) (Ici 0) :=
    fun s _ => semigroup_l2_sq_eq α f s
  apply HasDerivWithinAt.congr _ heq (semigroup_l2_sq_eq α f t)
  -- d/ds [mean^2 + e^{-4αs} * d^2] = (-4α) * e^{-4αs} * d^2
  apply HasDerivWithinAt.const_add
  -- d/ds [e^{-4αs} * d^2] at s = t
  set d2 := ((f .zero - f .one) / 2) ^ 2
  -- HasDerivWithinAt (exp ∘ (-4α·)) (exp(-4αt) * (-4α)) (Ici 0) t
  have h_exp : HasDerivWithinAt (fun s => exp (-4 * α * s))
      (exp (-4 * α * t) * (-4 * α)) (Ici 0) t :=
    (hasDerivWithinAt_neg_four_alpha α t).exp
  -- Multiply by constant d2
  have h_prod := h_exp.mul_const d2
  refine h_prod.congr_deriv ?_
  ring

/-- Ergodicity: Var(P_t f) → 0 as t → ∞. -/
theorem semigroup_ergodic_pf (hα : 0 < α) (f : TwoPoint → ℝ) :
    Tendsto (fun t => ∫ x, (semigroup α t f x) ^ 2 ∂uniformMeasure -
      (∫ x, f x ∂uniformMeasure) ^ 2) atTop (nhds 0) := by
  -- Var(P_t f) = e^{-4αt} * d^2 → 0
  have heq : (fun t => ∫ x, (semigroup α t f x) ^ 2 ∂uniformMeasure -
      (∫ x, f x ∂uniformMeasure) ^ 2) =
      (fun t => exp (-4 * α * t) * ((f .zero - f .one) / 2) ^ 2) :=
    funext (fun t => semigroup_variance_eq α f t)
  rw [heq, show (0 : ℝ) = 0 * ((f .zero - f .one) / 2) ^ 2 from by ring]
  apply Tendsto.mul_const
  -- Need: Tendsto (fun t => exp(-4αt)) atTop (nhds 0)
  -- Use tendsto_exp_neg_atTop_nhds_zero composed with (fun t => 4αt)
  have h4α_pos : 0 < 4 * α := by linarith
  have h_comp : (fun t => exp (-4 * α * t)) = (fun t => exp (-(4 * α * t))) := by
    ext t; ring_nf
  rw [h_comp]
  exact (tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_const_mul_atTop_of_pos h4α_pos).2 tendsto_id)).congr
    (fun t => by simp)

/-! ## Entropy helpers for the two-point space -/

/-- Entropy on TwoPoint is a concrete formula.
  Ent(g) = (g 0 · log(g 0) + g 1 · log(g 1)) / 2 - ((g 0 + g 1) / 2) · log((g 0 + g 1) / 2) -/
theorem entropy_eq (hα : 0 < α) (g : TwoPoint → ℝ) :
    DirichletSpace.entropy (ds := dirichletSpace α hα) g =
    (g .zero * log (g .zero) + g .one * log (g .one)) / 2 -
    ((g .zero + g .one) / 2) * log ((g .zero + g .one) / 2) := by
  simp only [DirichletSpace.entropy]
  have : (dirichletSpace α hα).μ = uniformMeasure := rfl
  rw [this, integral_uniformMeasure, integral_uniformMeasure]

/-- The semigroup value at .zero for g = f*f. -/
theorem semigroup_sq_zero (f : TwoPoint → ℝ) (t : ℝ) :
    semigroup α t (fun x => f x * f x) .zero =
    (f .zero * f .zero + f .one * f .one) / 2 +
    exp (-2 * α * t) * (f .zero * f .zero - f .one * f .one) / 2 := by
  simp only [semigroup, coeff, flip_zero, flip_one]; ring

/-- The semigroup value at .one for g = f*f. -/
theorem semigroup_sq_one (f : TwoPoint → ℝ) (t : ℝ) :
    semigroup α t (fun x => f x * f x) .one =
    (f .zero * f .zero + f .one * f .one) / 2 -
    exp (-2 * α * t) * (f .zero * f .zero - f .one * f .one) / 2 := by
  simp only [semigroup, coeff, flip_zero, flip_one]; ring

/-- Helper: exp(-2αt) → 0 for α > 0. -/
private theorem tendsto_exp_neg_two_alpha (hα : 0 < α) :
    Tendsto (fun t => exp (-2 * α * t)) atTop (nhds 0) := by
  have h2α_pos : 0 < 2 * α := by linarith
  have h_comp : (fun t => exp (-2 * α * t)) = (fun t => exp (-(2 * α * t))) := by
    ext t; ring_nf
  rw [h_comp]
  exact (tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_const_mul_atTop_of_pos h2α_pos).2 tendsto_id)).congr
    (fun t => by simp)

/-- Both semigroup values for f² converge to the mean m = (f0² + f1²)/2 as t → ∞. -/
theorem semigroup_sq_zero_tendsto (hα : 0 < α) (f : TwoPoint → ℝ) :
    Tendsto (fun t => semigroup α t (fun x => f x * f x) .zero)
      atTop (nhds ((f .zero * f .zero + f .one * f .one) / 2)) := by
  have heq : (fun t => semigroup α t (fun x => f x * f x) .zero) =
      (fun t => (f .zero * f .zero + f .one * f .one) / 2 +
        exp (-2 * α * t) * (f .zero * f .zero - f .one * f .one) / 2) :=
    funext (semigroup_sq_zero α f)
  rw [heq]
  suffices h : Tendsto (fun t => exp (-2 * α * t) * (f .zero * f .zero - f .one * f .one) / 2)
      atTop (nhds 0) by
    have h2 : Tendsto (fun t =>
        (f .zero * f .zero + f .one * f .one) / 2 +
        exp (-2 * α * t) * (f .zero * f .zero - f .one * f .one) / 2)
        atTop (nhds ((f .zero * f .zero + f .one * f .one) / 2 + 0)) :=
      tendsto_const_nhds.add h
    rwa [add_zero] at h2
  have heq2 : (fun t => exp (-2 * α * t) * (f .zero * f .zero - f .one * f .one) / 2) =
      (fun t => exp (-2 * α * t) * ((f .zero * f .zero - f .one * f .one) / 2)) := by
    ext t; ring
  rw [heq2, show (0 : ℝ) = 0 * ((f .zero * f .zero - f .one * f .one) / 2) from by ring]
  exact (tendsto_exp_neg_two_alpha α hα).mul_const _

theorem semigroup_sq_one_tendsto (hα : 0 < α) (f : TwoPoint → ℝ) :
    Tendsto (fun t => semigroup α t (fun x => f x * f x) .one)
      atTop (nhds ((f .zero * f .zero + f .one * f .one) / 2)) := by
  -- Use the .zero tendsto + the fact that the sum is constant: one = sum - zero
  have heq : (fun t => semigroup α t (fun x => f x * f x) .one) =
      (fun t => (f .zero * f .zero + f .one * f .one) -
        semigroup α t (fun x => f x * f x) .zero) := by
    ext t; have := semigroup_sum α t (fun x => f x * f x); linarith
  rw [heq, show (f .zero * f .zero + f .one * f .one) / 2 =
    (f .zero * f .zero + f .one * f .one) -
    (f .zero * f .zero + f .one * f .one) / 2 from by ring]
  exact Filter.Tendsto.const_sub _
    (semigroup_sq_zero_tendsto α hα f)

/-- Entropy of the semigroup applied to f² tends to 0.

Both values of P_t(f²) converge to the mean m = (f0² + f1²)/2,
so P_t(f²) converges pointwise to the constant function m.
The entropy of a constant function is m·log(m) - m·log(m) = 0.
By continuity of x·log(x), the entropy converges to 0. -/
theorem semigroup_entropy_sq_ergodic_pf (hα : 0 < α) (f : TwoPoint → ℝ) :
    Tendsto (fun t => DirichletSpace.entropy (ds := dirichletSpace α hα)
      (semigroup α t (fun x => f x * f x))) atTop (nhds 0) := by
  -- Rewrite entropy using the two-point formula
  set m := (f .zero * f .zero + f .one * f .one) / 2
  have h_ent_eq : (fun t => DirichletSpace.entropy (ds := dirichletSpace α hα)
      (semigroup α t (fun x => f x * f x))) =
    (fun t =>
      (semigroup α t (fun x => f x * f x) .zero *
        log (semigroup α t (fun x => f x * f x) .zero) +
       semigroup α t (fun x => f x * f x) .one *
        log (semigroup α t (fun x => f x * f x) .one)) / 2 -
      ((semigroup α t (fun x => f x * f x) .zero +
        semigroup α t (fun x => f x * f x) .one) / 2) *
        log ((semigroup α t (fun x => f x * f x) .zero +
              semigroup α t (fun x => f x * f x) .one) / 2)) :=
    funext (fun t => entropy_eq α hα (semigroup α t (fun x => f x * f x)))
  rw [h_ent_eq]
  -- The sum is preserved: P_t g(.zero) + P_t g(.one) = g(.zero) + g(.one)
  have h_sum : ∀ t, semigroup α t (fun x => f x * f x) .zero +
      semigroup α t (fun x => f x * f x) .one =
      f .zero * f .zero + f .one * f .one :=
    fun t => semigroup_sum α t (fun x => f x * f x)
  -- So the second term is constant
  conv => arg 1; ext t; rw [h_sum t]
  -- Target: ... / 2 - m * log m → 0 where m = (f0² + f1²)/2
  -- We need the first term → m * log m
  -- (a * log a + b * log b) / 2 → (m * log m + m * log m) / 2 = m * log m
  -- since a → m and b → m, and x * log x is continuous
  show Tendsto (fun t =>
    (semigroup α t (fun x => f x * f x) .zero *
      log (semigroup α t (fun x => f x * f x) .zero) +
     semigroup α t (fun x => f x * f x) .one *
      log (semigroup α t (fun x => f x * f x) .one)) / 2 -
    ((f .zero * f .zero + f .one * f .one) / 2) *
      log ((f .zero * f .zero + f .one * f .one) / 2))
    atTop (nhds 0)
  rw [show (0 : ℝ) =
    (m * log m + m * log m) / 2 - m * log m from by ring]
  apply Tendsto.sub
  · apply Tendsto.div_const
    apply Tendsto.add
    · exact (continuous_mul_log.tendsto m).comp (semigroup_sq_zero_tendsto α hα f)
    · exact (continuous_mul_log.tendsto m).comp (semigroup_sq_one_tendsto α hα f)
  · exact tendsto_const_nhds

/-! ## BakryEmerySpace instance -/

variable (hα : 0 < α)

/-- **The two-point space is not a diffusion.** Its carré-du-champ `Gamma α`
violates the Leibniz/diffusion identity `Γ(f·g, h) = f·Γ(g,h) + g·Γ(f,h)`: taking
`f = g = h` the indicator of `.zero`, at `x = .zero` the left-hand side is `α/2`
while the right-hand side is `α`. Hence **no `BakryEmerySpace TwoPoint` instance can
exist** — the `{0,1}` continuous-time Markov chain is a jump process, not a diffusion
(so the `Γ_leibniz` field, and the entropy-decay bound that depends on it, are false
here). -/
theorem gamma_leibniz_fails (hα : 0 < α) :
    ¬ ∀ (f g h : TwoPoint → ℝ) (x : TwoPoint),
        Gamma α (f * g) h x = f x * Gamma α g h x + g x * Gamma α f h x := by
  intro H
  classical
  set e : TwoPoint → ℝ := fun i => if i = TwoPoint.zero then 1 else 0 with he
  have e0 : e TwoPoint.zero = 1 := by simp [he]
  have e1 : e TwoPoint.one = 0 := by simp [he]
  have key := H e e e TwoPoint.zero
  simp only [Gamma, Pi.mul_apply, e0, e1] at key
  norm_num at key
  linarith

end TwoPoint
