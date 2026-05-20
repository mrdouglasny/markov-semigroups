/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Gross differentiation ODE: LSI ⇒ hypercontractivity

This file carries the **proof** of
`gross_lsi_implies_hypercontractive_of_hypotheses` (the abstract
Gross 1975 forward direction), decomposed per `plans/gross-discharge.md`
into:

* **P2** — the Gross ODE. The right `t`-derivative of
  `s ↦ ∫ (P_s f)^{q(s)} dμ` (equivalently of `Λ(s) = log ‖P_s f‖_{q(s)}`),
  obtained from `GeneratorCompat` (strong-`L²` right difference
  quotient: `h_core` ⇒ `P_s f ∈ core` ⇒ `h_gen` gives `A(P_s f)`
  directly) together with the chain rule for `t ↦ x^{q(t)}`.
  Right-derivative only — self-contained, no `C₀`-semigroup theory.

* **P3** — the algebraic closure. With the exponent path
  `q(s) = 1 + (p-1) e^{2ρ s}` (so `q' = 2ρ(q-1)`, `q(0) = p`), the
  Gross cancellation

  `Λ'(s) = (q'/(q² F))·Entμ(u^q) − E(u, u^{q-1})/F`,  `u = P_s f`,
           `F = ∫ u^q`,

  is `≤ 0` because LSI on `v = u^{q/2}` gives
  `Entμ(u^q) = Entμ(v²) ≤ (2/ρ) E(v,v)`, the coupling turns
  `2q'/(ρ q²)` into `4(q-1)/q²`, and Stroock–Varopoulos gives
  `(4(q-1)/q²) E(u^{q/2},u^{q/2}) ≤ E(u,u^{q-1})`. Then
  `antitoneOn_of_hasDerivWithinAt_nonpos` on `Set.Ici 0` yields
  `N(t) ≤ N(0) = ‖f‖_p`, and `Lᵖ`-norm monotonicity (probability
  measure) closes `‖P_t f‖_q ≤ ‖f‖_p` for `q ≤ q(t)`.

## Status

Scaffold: the exponent calculus is proved; `P2` (`grossLogNorm_…`)
is a single documented `sorry`; `P3`'s algebraic core and the
`eLpNorm ↔ ∫·^q` / `Lᵖ`-monotonicity bridges are documented `sorry`s
with the proof recorded above. The logical skeleton — including the
`antitoneOn` closure — compiles.

## References

Gross, *Logarithmic Sobolev inequalities*, Amer. J. Math. 97 (1975).
Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion
Operators*, §5.2.
-/

import MarkovSemigroups.Abstract.Hypercontractivity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory ENNReal Set
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GrossODE

variable {X : Type*} [MeasurableSpace X]

/-! ## The Gross exponent path `q(s) = 1 + (p-1) e^{2ρ s}` -/

/-- The Gross exponent path: the critical curve along which the
`L^{q(s)}` norm of `P_s f` is non-increasing. `q(0) = p` and
`q'(s) = 2ρ (q(s) - 1)` (the coupling that drives the cancellation). -/
def grossExponent (ρ p s : ℝ) : ℝ := 1 + (p - 1) * Real.exp (2 * ρ * s)

@[simp] theorem grossExponent_zero (ρ p : ℝ) : grossExponent ρ p 0 = p := by
  simp [grossExponent]

theorem one_lt_grossExponent {p : ℝ} (hp : 1 < p) (ρ s : ℝ) :
    1 < grossExponent ρ p s := by
  have : 0 < (p - 1) * Real.exp (2 * ρ * s) :=
    mul_pos (by linarith) (Real.exp_pos _)
  simpa [grossExponent] using this

theorem grossExponent_pos {p : ℝ} (hp : 1 < p) (ρ s : ℝ) :
    0 < grossExponent ρ p s := by
  have := one_lt_grossExponent hp ρ s; linarith

/-- `q'(s) = 2ρ (q(s) - 1)` — the Gross coupling, as a `HasDerivAt`. -/
theorem hasDerivAt_grossExponent (ρ p s : ℝ) :
    HasDerivAt (grossExponent ρ p) (2 * ρ * (grossExponent ρ p s - 1)) s := by
  have hbase : HasDerivAt (fun s : ℝ => 2 * ρ * s) (2 * ρ) s := by
    simpa using ((hasDerivAt_id s).const_mul (2 * ρ))
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (2 * ρ * s))
      (Real.exp (2 * ρ * s) * (2 * ρ)) s := by
    simpa using (Real.hasDerivAt_exp (2 * ρ * s)).comp s hbase
  have hcomb : HasDerivAt (fun s : ℝ => 1 + (p - 1) * Real.exp (2 * ρ * s))
      ((p - 1) * (Real.exp (2 * ρ * s) * (2 * ρ))) s :=
    (hexp.const_mul (p - 1)).const_add 1
  have : HasDerivAt (grossExponent ρ p)
      ((p - 1) * (Real.exp (2 * ρ * s) * (2 * ρ))) s := hcomb
  convert this using 1
  simp only [grossExponent]; ring

/-- The exponent path is monotone in `s` (for `p > 1`, `ρ ≥ 0`). -/
theorem grossExponent_le_of_le {p : ℝ} (hp : 1 < p) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {s t : ℝ} (hst : s ≤ t) : grossExponent ρ p s ≤ grossExponent ρ p t := by
  have hmono : Real.exp (2 * ρ * s) ≤ Real.exp (2 * ρ * t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hp' : 0 ≤ p - 1 := by linarith
  simpa [grossExponent] using
    add_le_add_left (mul_le_mul_of_nonneg_left hmono hp') 1

/-! ## P2 — the Gross ODE (the analytic bottleneck) -/

/-- `‖P_s f‖_{q(s)}^{q(s)} = ∫ |P_s f|^{q(s)} dμ`, the quantity whose
log gives `Λ`. `f` is supplied through its core witness `hf`; the
semigroup acts on the `L²` carrier. -/
def grossPow (D : DirichletMarkovSemigroup X) {f : X → ℝ} (hf : D.IsCore f)
    (ρ p s : ℝ) : ℝ :=
  ∫ x, |((D.P s (D.coreToL2 hf) : X → ℝ) x)| ^ grossExponent ρ p s ∂D.μ

/-- `Λ(s) = log ‖P_s f‖_{q(s)} = q(s)⁻¹ · log (∫ |P_s f|^{q(s)})`. -/
def grossLogNorm (D : DirichletMarkovSemigroup X) {f : X → ℝ}
    (hf : D.IsCore f) (ρ p s : ℝ) : ℝ :=
  (grossExponent ρ p s)⁻¹ * Real.log (grossPow D hf ρ p s)

/-- The Gross derivative value
`Λ'(s) = (q'/(q² F))·Entμ(u^q) − E(u, u^{q-1})/F` (`u = P_s f`,
`q = q(s)`, `F = grossPow`). P2 asserts `Λ` has this as its right
derivative; P3 asserts it is `≤ 0`. -/
def grossLogNormDeriv (D : DirichletMarkovSemigroup X) {f : X → ℝ}
    (hf : D.IsCore f) (ρ p s : ℝ) : ℝ :=
  2 * ρ * (grossExponent ρ p s - 1)
      / (grossExponent ρ p s ^ 2 * grossPow D hf ρ p s)
      * D.toDirichletSpace.entropy
          (fun x => |((D.P s (D.coreToL2 hf) : X → ℝ) x)|
            ^ grossExponent ρ p s)
    - D.energy ((D.P s (D.coreToL2 hf) : X → ℝ))
        (fun x => |((D.P s (D.coreToL2 hf) : X → ℝ) x)|
          ^ (grossExponent ρ p s - 1))
      / grossPow D hf ρ p s

/-- `∫ |u_s|^{q(s)} · log |u_s| dμ` — the entropy-carrying integral
that appears in `F'` and in the entropy identity. -/
def grossLogIntegral (D : DirichletMarkovSemigroup X) {f : X → ℝ}
    (hf : D.IsCore f) (ρ p s : ℝ) : ℝ :=
  ∫ x, |((D.P s (D.coreToL2 hf) : X → ℝ) x)| ^ grossExponent ρ p s
      * Real.log |((D.P s (D.coreToL2 hf) : X → ℝ) x)| ∂D.μ

/-- `F'(s) = q'(s)·∫ uq log u − q(s)·E(u, u^{q-1})` — the right
derivative of `grossPow`. The first term is the exponent-path
contribution (`∂_s |u|^{q(s)} = |u|^{q} log|u| · q'`); the second is
the semigroup contribution (`∂_s u = A u`, `∫ u^{q-1} A u =
−E(u,u^{q-1})` by `GeneratorCompat`). -/
def grossPowDeriv (D : DirichletMarkovSemigroup X) {f : X → ℝ}
    (hf : D.IsCore f) (ρ p s : ℝ) : ℝ :=
  2 * ρ * (grossExponent ρ p s - 1) * grossLogIntegral D hf ρ p s
    - grossExponent ρ p s
        * D.energy ((D.P s (D.coreToL2 hf) : X → ℝ))
            (fun x => |((D.P s (D.coreToL2 hf) : X → ℝ) x)|
              ^ (grossExponent ρ p s - 1))

/-- `F(s) = ∫ |u_s|^{q(s)} > 0`. Holds whenever `P_s f` is not μ-a.e.
zero (`f ≢ 0`; the `f ≡ 0` case is handled separately in the
assembly). **Status: documented `sorry`.** -/
theorem grossPow_pos (D : DirichletMarkovSemigroup X) (ρ p : ℝ)
    (hρ : 0 < ρ) (hp : 1 < p) {f : X → ℝ} (hf : D.IsCore f)
    (hf_nonneg : ∀ x, 0 ≤ f x) {s : ℝ} (hs : 0 ≤ s) :
    0 < grossPow D hf ρ p s := by
  sorry

/-- **Entropy identity.** `Entμ(u^q) = q · (∫ uq log u) − F · log F`,
i.e. `D.toDirichletSpace.entropy (|u|^q) = q · grossLogIntegral −
grossPow · log grossPow`. Pure log-of-power algebra on the definition
`entropy g = ∫ g log g − (∫ g)·log(∫ g)` (with `g = |u|^q`,
`log(|u|^q) = q log|u|`, `∫ g = F`). **Status: documented `sorry`**
(needs the integrability of `g log g` from the core `L^∞` bounds). -/
theorem grossEntropy_eq (D : DirichletMarkovSemigroup X) (ρ p : ℝ)
    {f : X → ℝ} (hf : D.IsCore f) {s : ℝ} :
    D.toDirichletSpace.entropy
        (fun x => |((D.P s (D.coreToL2 hf) : X → ℝ) x)|
          ^ grossExponent ρ p s)
      = grossExponent ρ p s * grossLogIntegral D hf ρ p s
        - grossPow D hf ρ p s * Real.log (grossPow D hf ρ p s) := by
  sorry

/-! ### Decomposition of the P2 bottleneck

`grossPow_hasDerivWithinAt` differentiates `F(s) = ∫ |u_s|^{q(s)}`
where *both* the exponent path `q(s)` and the semigroup orbit
`u_s = P_s f` move. We split it (no axiom — axiomatizing the Gross
differentiation itself would be circular) into:

* **`hasDerivAt_integral_rpow_exponent`** — *general, Mathlib-native*:
  the exponent-path half, orbit frozen. Elementary parametric-integral
  calculus (pointwise `rpow`-exponent derivative + a constant
  dominator on a finite measure since `|w| ≤ M`). Reusable; no
  semigroup theory.

* **`hasDerivWithinAt_integral_of_strongL2Deriv`** — *general,
  Mathlib-native*: a Bochner–Leibniz rule passing a strong-`L²` right
  derivative of the integrand through `∫ ψ(·)`. The semigroup half,
  exponent frozen. To be **proved** from Mathlib's
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` family + the
  `L² → L¹` Cauchy–Schwarz step — *not* an axiom (it is generic
  infrastructure, not the Gross theorem).

`grossPow_hasDerivWithinAt` is then thin glue: the diagonal
`σ ↦ H(σ,σ)` total derivative `= ∂₁ + ∂₂` of the two halves, with the
semigroup half's `∫ ψ'(u)·(A u)` rewritten as `−q·E(u, u^{q-1})` by
`h_gen`'s form pairing (`u' = A u` from `GeneratorCompat`, `u ∈ core`
from `h_core`). -/

/-- **Pointwise `rpow`-exponent derivative** (the elementary calculus
core, fully proved). For `c : ℝ` and a path `a` with
`HasDerivAt a a' s`, all values of `a` positive,
`∂_σ |c|^{a σ} = |c|^{a s} · log|c| · a'` at `s`. The `|c| = 0` case
is the constant `0` (`0^{a σ} = 0` since `a > 0`), consistent with
`0^{a s}·log 0·a' = 0`. -/
theorem hasDerivAt_abs_rpow_exponent (c : ℝ) {a : ℝ → ℝ} {a' s : ℝ}
    (ha : HasDerivAt a a' s) (ha_pos : ∀ σ, 0 < a σ) :
    HasDerivAt (fun σ => |c| ^ a σ)
      (|c| ^ a s * Real.log |c| * a') s := by
  rcases eq_or_lt_of_le (abs_nonneg c) with hc | hc
  · -- `|c| = 0`: the function is constantly `0`.
    have hzero : (fun σ => |c| ^ a σ) = fun _ => (0 : ℝ) := by
      funext σ; rw [← hc, Real.zero_rpow (ha_pos σ).ne']
    rw [hzero]
    have hd : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 s := hasDerivAt_const s 0
    convert hd using 1
    rw [← hc, Real.zero_rpow (ha_pos s).ne']; ring
  · -- `|c| > 0`: `|c|^{a σ} = exp (log|c| · a σ)`.
    have hrw : (fun σ => |c| ^ a σ)
        = fun σ => Real.exp (Real.log |c| * a σ) := by
      funext σ; rw [Real.rpow_def_of_pos hc]
    rw [hrw]
    have hmul : HasDerivAt (fun σ => Real.log |c| * a σ)
        (Real.log |c| * a') s := ha.const_mul _
    have hexp := (Real.hasDerivAt_exp (Real.log |c| * a s)).comp s hmul
    convert hexp using 1
    rw [Real.rpow_def_of_pos hc]; ring

/-- **General (Mathlib-native): parametric `rpow`-exponent Leibniz.**
For a bounded measurable `w` on a finite measure space and a
differentiable positive exponent path `a`,
`σ ↦ ∫ |w|^{a σ}` is differentiable with derivative
`a'(s) · ∫ |w|^{a s} · log|w|`. Elementary: the pointwise exponent
derivative is `∂_σ |w y|^{a σ} = |w y|^{a σ} · log|w y| · a'`
(Mathlib `rpow`; the `w y = 0` case is the constant `0` since
`a > 0`), dominated by the constant `(sup_{[0,M]} t^{a} |log t|)·|a'|`
which is `ν`-integrable as `ν` is finite. No project structure.

**Status: documented `sorry` — elementary parametric-integral
plumbing (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`).** -/
theorem hasDerivAt_integral_rpow_exponent {Y : Type*}
    [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    {w : Y → ℝ} (hw : Measurable w) {M : ℝ} (hM : ∀ y, |w y| ≤ M)
    {a : ℝ → ℝ} {a' s : ℝ} (ha : HasDerivAt a a' s)
    (ha_pos : ∀ σ, 0 < a σ) :
    HasDerivAt (fun σ => ∫ y, |w y| ^ a σ ∂ν)
      (a' * ∫ y, |w y| ^ a s * Real.log |w y| ∂ν) s := by
  sorry

/-- A family of real-valued functions on a finite measure space that is uniformly bounded almost
everywhere by a constant is uniformly integrable in `L²`. This is the `p = 2` specialization of
Mathlib's finite-measure criterion, packaged for the bounded coefficient families used in the P2
Leibniz kernel. -/
lemma uniformIntegrable_two_of_ae_bound {ι Y : Type*}
    [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (f : ι → Y → ℝ) (hf_meas : ∀ i, AEStronglyMeasurable (f i) ν)
    {K : NNReal} (hK : ∀ i, ∀ᵐ y ∂ν, ‖f i y‖₊ ≤ K) :
    MeasureTheory.UniformIntegrable f (2 : ℝ≥0∞) ν := by
  refine MeasureTheory.uniformIntegrable_of (μ := ν) (f := f) (p := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num) hf_meas ?_
  intro ε hε
  refine ⟨K + 1, fun i => ?_⟩
  have hempty : {y : Y | K + 1 ≤ ‖f i y‖₊}.indicator (f i) =ᵐ[ν] 0 := by
    filter_upwards [hK i] with y hy
    by_cases hmem : y ∈ {y : Y | K + 1 ≤ ‖f i y‖₊}
    · exfalso
      exact (not_le_of_gt (lt_of_le_of_lt hy (lt_add_one K))) hmem
    · simp [Set.indicator_of_notMem, hmem]
  calc
    eLpNorm ({x : Y | K + 1 ≤ ‖f i x‖₊}.indicator (f i)) 2 ν
        = eLpNorm (0 : Y → ℝ) 2 ν := eLpNorm_congr_ae hempty
    _ = 0 := by simp
    _ ≤ ENNReal.ofReal ε := by positivity

/-- **Pointwise FTC: averaged-derivative form of the increment.** For `ψ : ℝ → ℝ`
of class `C¹` and any two reals `a, b`,
`ψ a - ψ b = (a - b) * ∫ t in 0..1, deriv ψ (b + t · (a - b))`.

Foundational step of the P2 Leibniz kernel: applied pointwise in `y` with
`a := (u σ : Y → ℝ) y` and `b := (u s : Y → ℝ) y`, it factors the increment as
`ψ(u_σ y) − ψ(u_s y) = (u_σ y − u_s y) · M_σ(y)` where
`M_σ(y) := ∫_0^1 deriv ψ (u_s y + t · (u_σ y − u_s y)) dt`. Replaces a
product-measure Fubini argument with a 1D parametric integral. -/
lemma sub_eq_mul_intervalIntegral_deriv {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (a b : ℝ) :
    ψ a - ψ b = (a - b) * ∫ t in (0:ℝ)..1, deriv ψ (b + t * (a - b)) := by
  have hψ_diff : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => b + s * (a - b)) (a - b) t := fun t => by
    simpa using ((hasDerivAt_id t).mul_const (a - b)).const_add b
  have hh : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => ψ (b + s * (a - b)))
        (deriv ψ (b + t * (a - b)) * (a - b)) t := fun t =>
    (hψ_diff.differentiableAt.hasDerivAt).comp t (hg t)
  have hcont : Continuous (fun t : ℝ => deriv ψ (b + t * (a - b)) * (a - b)) := by
    have : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
    fun_prop
  have hftc : (∫ t in (0:ℝ)..1, deriv ψ (b + t * (a - b)) * (a - b))
      = ψ (b + 1 * (a - b)) - ψ (b + 0 * (a - b)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hh t)
      (hcont.intervalIntegrable 0 1)
  have e1 : b + 1 * (a - b) = a := by ring
  have e0 : b + 0 * (a - b) = b := by ring
  rw [e1, e0] at hftc
  have hmul :
      (∫ t in (0:ℝ)..1, deriv ψ (b + t * (a - b)) * (a - b))
        = (∫ t in (0:ℝ)..1, deriv ψ (b + t * (a - b))) * (a - b) :=
    intervalIntegral.integral_mul_const (a - b)
      (fun t => deriv ψ (b + t * (a - b)))
  rw [mul_comm, ← hmul]
  exact hftc.symm

/-- **The averaged-derivative field `M_σ`.** Pointwise in `y`,
`M_σ(y) := ∫_0^1 deriv ψ (u_s(y) + t · (u_σ(y) − u_s(y))) dt`. This is the
y-fiber t-integral that factors the increment `ψ(u_σ y) − ψ(u_s y)` per
`sub_eq_mul_intervalIntegral_deriv`. The whole P2 Leibniz proof reduces to
controlling this field and its L²-convergence as `σ → s⁺`. -/
def averagedDerivField {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (u : ℝ → Lp ℝ 2 ν) (ψ : ℝ → ℝ) (σ s : ℝ) (y : Y) : ℝ :=
  ∫ t in (0:ℝ)..1,
    deriv ψ ((u s : Y → ℝ) y + t * ((u σ : Y → ℝ) y - (u s : Y → ℝ) y))

/-- **Factorization identity.** `ψ(u_σ y) − ψ(u_s y) = (u_σ y − u_s y) · M_σ(y)`.
Pointwise specialization of `sub_eq_mul_intervalIntegral_deriv` with
`a = (u σ) y`, `b = (u s) y`. Folded across `y`, this rewrites the
increment `∫ ψ(u_σ) − ∫ ψ(u_s)` as `∫ (u_σ − u_s) · M_σ` (= the L²
inner product after division by `(σ − s)`). -/
lemma psi_sub_eq_diff_mul_averagedDerivField {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} (u : ℝ → Lp ℝ 2 ν) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (σ s : ℝ) (y : Y) :
    ψ ((u σ : Y → ℝ) y) - ψ ((u s : Y → ℝ) y)
      = ((u σ : Y → ℝ) y - (u s : Y → ℝ) y) * averagedDerivField u ψ σ s y :=
  sub_eq_mul_intervalIntegral_deriv hψ ((u σ : Y → ℝ) y) ((u s : Y → ℝ) y)

/-- **`M_σ` is `AEStronglyMeasurable`.** Factors through a jointly-continuous map
`(a, b) ↦ ∫_0^1 ψ'(b + t · (a − b)) dt` applied to the `AEStronglyMeasurable` pair
`(u_σ y, u_s y)`. The joint continuity is the parametric-interval-integral lemma
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`. -/
lemma averagedDerivField_aestronglyMeasurable {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} (u : ℝ → Lp ℝ 2 ν) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (σ s : ℝ) :
    AEStronglyMeasurable (averagedDerivField u ψ σ s) ν := by
  have hu_σ : AEStronglyMeasurable (fun y : Y => (u σ : Y → ℝ) y) ν :=
    Lp.aestronglyMeasurable _
  have hu_s : AEStronglyMeasurable (fun y : Y => (u s : Y → ℝ) y) ν :=
    Lp.aestronglyMeasurable _
  have h_deriv_cont : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  -- The averaged-derivative map g(a, b) := ∫_0^1 ψ'(b + t · (a - b)) dt is jointly
  -- continuous in (a, b), by `continuous_parametric_intervalIntegral_of_continuous'`
  -- on the jointly continuous integrand `((a,b), t) ↦ ψ'(b + t · (a - b))`.
  have h_inner_cont : Continuous
      (Function.uncurry (fun (p : ℝ × ℝ) (t : ℝ) =>
        deriv ψ (p.2 + t * (p.1 - p.2)))) := by
    have h_arg : Continuous
        (fun (q : (ℝ × ℝ) × ℝ) => q.1.2 + q.2 * (q.1.1 - q.1.2)) := by fun_prop
    exact h_deriv_cont.comp h_arg
  have h_param :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume)
      (f := fun (p : ℝ × ℝ) (t : ℝ) => deriv ψ (p.2 + t * (p.1 - p.2)))
      h_inner_cont (0:ℝ) 1
  -- h_param : Continuous fun p : ℝ × ℝ => ∫ t in 0..1, deriv ψ (p.2 + t · (p.1 - p.2))
  -- Repackage as continuity of g.uncurry where g a b = ∫ t in 0..1, ψ'(b + t · (a - b)).
  have h_joint : Continuous
      (Function.uncurry (fun (a b : ℝ) =>
        ∫ t in (0:ℝ)..1, deriv ψ (b + t * (a - b)))) := h_param
  exact h_joint.comp_aestronglyMeasurable₂ hu_σ hu_s

/-- **a.e. bound on `M_σ` from a.e. bounds on the orbit endpoints.** If
`|(u_s y)| ≤ M` and `|(u_σ y)| ≤ M` a.e., and `|deriv ψ|` is bounded by `K`
on `[-M, M]`, then `|M_σ(y)| ≤ K` a.e. The interpolant
`u_s y + t·(u_σ y − u_s y)` is a convex combination of `u_s y` and `u_σ y`
for `t ∈ [0,1]`, hence lives in `[-M, M]`. -/
lemma averagedDerivField_ae_bound {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} {u : ℝ → Lp ℝ 2 ν} {ψ : ℝ → ℝ}
    {σ s : ℝ} {M K : ℝ}
    (hψ_bound : ∀ x ∈ Set.Icc (-M) M, |deriv ψ x| ≤ K)
    (hu_σ : ∀ᵐ y ∂ν, |(u σ : Y → ℝ) y| ≤ M)
    (hu_s : ∀ᵐ y ∂ν, |(u s : Y → ℝ) y| ≤ M) :
    ∀ᵐ y ∂ν, |averagedDerivField u ψ σ s y| ≤ K := by
  -- Implementation below; the wrapper `averagedDerivField_memLp_two` packages this together
  -- with the measurability for direct `MemLp 2 ν` consumption.
  filter_upwards [hu_σ, hu_s] with y hyσ hys
  unfold averagedDerivField
  -- Step 1: convex-combination bound on the interpolant
  have hconvex : ∀ t ∈ Set.Icc (0:ℝ) 1,
      |(u s : Y → ℝ) y + t * ((u σ : Y → ℝ) y - (u s : Y → ℝ) y)| ≤ M := by
    rintro t ⟨h0, h1⟩
    have hrw : (u s : Y → ℝ) y + t * ((u σ : Y → ℝ) y - (u s : Y → ℝ) y)
        = (1 - t) * (u s : Y → ℝ) y + t * (u σ : Y → ℝ) y := by ring
    rw [hrw]
    have h1t_nn : (0:ℝ) ≤ 1 - t := by linarith
    calc |(1 - t) * (u s : Y → ℝ) y + t * (u σ : Y → ℝ) y|
        ≤ |(1 - t) * (u s : Y → ℝ) y| + |t * (u σ : Y → ℝ) y| := abs_add_le _ _
      _ = (1 - t) * |(u s : Y → ℝ) y| + t * |(u σ : Y → ℝ) y| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h1t_nn, abs_of_nonneg h0]
      _ ≤ (1 - t) * M + t * M := by gcongr
      _ = M := by ring
  -- Step 2: the interpolant lives in [-M, M]
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1,
      (u s : Y → ℝ) y + t * ((u σ : Y → ℝ) y - (u s : Y → ℝ) y) ∈ Set.Icc (-M) M :=
    fun t ht => Set.mem_Icc.mpr (abs_le.mp (hconvex t ht))
  -- Step 3: pointwise bound on the integrand
  have hpointwise : ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖deriv ψ ((u s : Y → ℝ) y + t * ((u σ : Y → ℝ) y - (u s : Y → ℝ) y))‖ ≤ K := by
    intro t ht
    have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := by
      have : Set.uIoc (0:ℝ) 1 = Set.Ioc 0 1 := by
        simp [Set.uIoc, min_eq_left (by linarith : (0:ℝ) ≤ 1),
              max_eq_right (by linarith : (0:ℝ) ≤ 1)]
      rw [this] at ht
      exact ⟨ht.1.le, ht.2⟩
    simpa [Real.norm_eq_abs] using hψ_bound _ (hmem t ht_Icc)
  -- Step 4: interval-integral bound `‖∫ 0..1, g‖ ≤ K · |1-0| = K`
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1)
    (f := fun t => deriv ψ ((u s : Y → ℝ) y + t * ((u σ : Y → ℝ) y - (u s : Y → ℝ) y)))
    (C := K) hpointwise
  have hone : |(1:ℝ) - 0| = 1 := by norm_num
  rw [hone, mul_one] at h
  simpa [Real.norm_eq_abs] using h

/-- **Pointwise `|M_σ(y) − ψ'(u_s y)| ≤ ω`** from a local modulus on `ψ'`.
If both `u_s y` and `u_σ y` lie in `[-M, M]` and `|u_σ y − u_s y| ≤ δ`, and `ψ'`
varies by at most `ω` over `[-M, M]` within distance `δ` of `u_s y`, then
`|M_σ(y) − ψ'(u_s y)| ≤ ω`. Heart of the in-measure convergence step: the
exceptional set `{y : |M_σ y − ψ'(u_s y)| > ω}` is contained in
`{|u_σ − u_s| > δ} ∪ {bounds violated}`, and the first goes to zero in measure
by `tendstoInMeasure_of_tendsto_Lp`. -/
lemma averagedDerivField_sub_le_of_close
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {u : ℝ → Lp ℝ 2 ν} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    {σ s : ℝ} {y : Y} {M δ ω : ℝ}
    (hys : |(u s : Y → ℝ) y| ≤ M)
    (hyσ : |(u σ : Y → ℝ) y| ≤ M)
    (hyclose : |(u σ : Y → ℝ) y - (u s : Y → ℝ) y| ≤ δ)
    (h_psi_modulus : ∀ x ∈ Set.Icc (-M) M,
        |x - (u s : Y → ℝ) y| ≤ δ →
        |deriv ψ x - deriv ψ ((u s : Y → ℝ) y)| ≤ ω) :
    |averagedDerivField u ψ σ s y - deriv ψ ((u s : Y → ℝ) y)| ≤ ω := by
  unfold averagedDerivField
  set a : ℝ := (u σ : Y → ℝ) y with ha
  set b : ℝ := (u s : Y → ℝ) y with hb
  -- For t ∈ [0,1]: interpolant b + t·(a - b) is in [-M, M] (convex combination)
  -- and within distance |a - b| ≤ δ of b. Hence by h_psi_modulus,
  -- |ψ'(interpolant) - ψ'(b)| ≤ ω.
  have h_inner_bound : ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖deriv ψ (b + t * (a - b)) - deriv ψ b‖ ≤ ω := by
    intro t ht
    -- Reduce to t ∈ Icc 0 1.
    have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := by
      have : Set.uIoc (0:ℝ) 1 = Set.Ioc 0 1 := by
        simp [Set.uIoc, min_eq_left (by linarith : (0:ℝ) ≤ 1),
              max_eq_right (by linarith : (0:ℝ) ≤ 1)]
      rw [this] at ht
      exact ⟨ht.1.le, ht.2⟩
    obtain ⟨ht0, ht1⟩ := ht_Icc
    have h1t_nn : (0:ℝ) ≤ 1 - t := by linarith
    -- The interpolant `b + t·(a - b) = (1 - t)·b + t·a` is a convex combination.
    have h_interp_eq : b + t * (a - b) = (1 - t) * b + t * a := by ring
    -- |interpolant| ≤ M.
    have h_in_Icc : (b + t * (a - b)) ∈ Set.Icc (-M) M := by
      rw [Set.mem_Icc, ← abs_le]
      rw [h_interp_eq]
      calc |(1 - t) * b + t * a|
          ≤ |(1 - t) * b| + |t * a| := abs_add_le _ _
        _ = (1 - t) * |b| + t * |a| := by
            rw [abs_mul, abs_mul, abs_of_nonneg h1t_nn, abs_of_nonneg ht0]
        _ ≤ (1 - t) * M + t * M := by gcongr
        _ = M := by ring
    -- |interpolant - b| = t·|a - b| ≤ δ.
    have h_close : |(b + t * (a - b)) - b| ≤ δ := by
      have : (b + t * (a - b)) - b = t * (a - b) := by ring
      rw [this, abs_mul, abs_of_nonneg ht0]
      calc t * |a - b| ≤ 1 * |a - b| := by gcongr
        _ = |a - b| := one_mul _
        _ ≤ δ := hyclose
    -- Apply the modulus.
    simpa [Real.norm_eq_abs] using h_psi_modulus _ h_in_Icc h_close
  -- Now write M_σ y - ψ'(b) as the interval integral of [ψ'(interpolant) - ψ'(b)].
  have h_const_integral : (∫ _t in (0:ℝ)..1, deriv ψ b) = deriv ψ b := by
    simp
  have h_psi_b_intervalIntegrable :
      IntervalIntegrable (fun _ : ℝ => deriv ψ b) MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  have h_psi_interp_cont :
      Continuous (fun t : ℝ => deriv ψ (b + t * (a - b))) := by
    have hdψ : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
    fun_prop
  have h_psi_interp_intervalIntegrable :
      IntervalIntegrable (fun t : ℝ => deriv ψ (b + t * (a - b)))
        MeasureTheory.volume 0 1 :=
    h_psi_interp_cont.intervalIntegrable 0 1
  have h_diff_eq :
      (∫ t in (0:ℝ)..1, deriv ψ (b + t * (a - b))) - deriv ψ b
        = ∫ t in (0:ℝ)..1, deriv ψ (b + t * (a - b)) - deriv ψ b := by
    have hsub := intervalIntegral.integral_sub
      h_psi_interp_intervalIntegrable h_psi_b_intervalIntegrable
    -- hsub : ∫ (f - g) = (∫ f) - (∫ g); chain via h_const_integral.
    rw [hsub, h_const_integral]
  rw [h_diff_eq]
  -- Apply the integral-norm bound.
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1)
    (f := fun t : ℝ => deriv ψ (b + t * (a - b)) - deriv ψ b)
    (C := ω) h_inner_bound
  have hone : |(1:ℝ) - 0| = 1 := by norm_num
  rw [hone, mul_one] at h
  simpa [Real.norm_eq_abs] using h

/-- **a.e. sub bound conditional on `|u_σ − u_s| ≤ δ`.** If both `u_σ` and `u_s`
are a.e. `M`-bounded and `ψ'` has uniform modulus `(δ, ω)` on `[-M, M]`, then
on the a.e.-set where `|u_σ y − u_s y| ≤ δ`, we have
`|M_σ(y) − ψ'(u_s y)| ≤ ω`. Direct conditional input to the in-measure step:
combined with a.e.-bound + in-measure of `u_σ → u_s`, the bad set
`{ε ≤ |M_σ − ψ'(u_s)|}` is contained (a.e.) in `{δ < |u_σ − u_s|}`. -/
lemma averagedDerivField_ae_sub_le_of_close
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {u : ℝ → Lp ℝ 2 ν} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    {σ s : ℝ} {M δ ω : ℝ}
    (hu_σ : ∀ᵐ y ∂ν, |(u σ : Y → ℝ) y| ≤ M)
    (hu_s : ∀ᵐ y ∂ν, |(u s : Y → ℝ) y| ≤ M)
    (hψ'_modulus : ∀ x ∈ Set.Icc (-M) M, ∀ z ∈ Set.Icc (-M) M,
        |x - z| ≤ δ → |deriv ψ x - deriv ψ z| ≤ ω) :
    ∀ᵐ y ∂ν,
      |(u σ : Y → ℝ) y - (u s : Y → ℝ) y| ≤ δ →
      |averagedDerivField u ψ σ s y - deriv ψ ((u s : Y → ℝ) y)| ≤ ω := by
  filter_upwards [hu_σ, hu_s] with y hyσ hys hyclose
  refine averagedDerivField_sub_le_of_close hψ hys hyσ hyclose ?_
  intro x hx hxclose
  exact hψ'_modulus x hx _ (Set.mem_Icc.mpr (abs_le.mp hys)) hxclose

/-- **`M_σ ∈ MemLp 2 ν` from the a.e. bound + finite measure.** Combines
`averagedDerivField_aestronglyMeasurable` (measurability) and
`averagedDerivField_ae_bound` (a.e. boundedness) via `MemLp.of_bound`.
This is the direct input the Vitali step wants: each `M_σ` is in `L²`
with uniform-in-σ norm, hence the family `{M_σ}` is uniformly integrable
(via `uniformIntegrable_two_of_ae_bound`). -/
lemma averagedDerivField_memLp_two {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [IsFiniteMeasure ν]
    {u : ℝ → Lp ℝ 2 ν} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    {σ s : ℝ} {M K : ℝ}
    (hψ_bound : ∀ x ∈ Set.Icc (-M) M, |deriv ψ x| ≤ K)
    (hu_σ : ∀ᵐ y ∂ν, |(u σ : Y → ℝ) y| ≤ M)
    (hu_s : ∀ᵐ y ∂ν, |(u s : Y → ℝ) y| ≤ M) :
    MemLp (averagedDerivField u ψ σ s) 2 ν := by
  refine MemLp.of_bound (averagedDerivField_aestronglyMeasurable u hψ σ s) K ?_
  filter_upwards [averagedDerivField_ae_bound hψ_bound hu_σ hu_s] with y hy
  simpa [Real.norm_eq_abs] using hy

/-- **In-measure convergence: `M_σ → ψ'(u_s)` as `σ → s` from within `Set.Ici 0`.**
Heart of Step 3 of the discharge plan. The chain:
* Heine–Cantor on `deriv ψ` over the compact `[-M, M]` gives a modulus `(δ, εr/2)`.
* `tendstoInMeasure_of_tendsto_Lp` applied to `hu.continuousWithinAt` gives
  `u_σ → u_s` in measure.
* The a.e.-set inclusion (from `averagedDerivField_ae_sub_le_of_close` with
  `ω = εr/2 < εr`):
    `{y | ε ≤ edist(M_σ y, ψ'(u_s y))} ⊆ᵐ {y | ENNReal.ofReal δ ≤ edist(u_σ y, u_s y)}`
  (the latter has ν-measure → 0 by the u-side in-measure).
Combined with `uniformIntegrable_two_of_ae_bound`, this is the input Vitali needs
to upgrade to L²-convergence; closure of the main P2 kernel via `Filter.Tendsto.inner`. -/
lemma averagedDerivField_tendstoInMeasure
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [IsFiniteMeasure ν]
    {u : ℝ → Lp ℝ 2 ν} {u' : Lp ℝ 2 ν} {s : ℝ}
    (hu : HasDerivWithinAt u u' (Set.Ici 0) s)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    {M : ℝ}
    (h_u_bound : ∀ᶠ σ in nhdsWithin s (Set.Ici 0),
        ∀ᵐ y ∂ν, |(u σ : Y → ℝ) y| ≤ M)
    (h_u_s_bound : ∀ᵐ y ∂ν, |(u s : Y → ℝ) y| ≤ M) :
    TendstoInMeasure ν (fun σ => (averagedDerivField u ψ σ s : Y → ℝ))
      (nhdsWithin s (Set.Ici 0))
      (fun y => deriv ψ ((u s : Y → ℝ) y)) := by
  -- Heine–Cantor on the compact `[-M, M]`.
  have hψ'_uc : UniformContinuousOn (deriv ψ) (Set.Icc (-M) M) :=
    IsCompact.uniformContinuousOn_of_continuous isCompact_Icc
      (hψ.continuous_deriv le_rfl).continuousOn
  -- L² → in-measure for `u`.
  have hu_im : TendstoInMeasure ν (fun σ => ((u σ : Lp ℝ 2 ν) : Y → ℝ))
      (nhdsWithin s (Set.Ici 0)) (u s) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp hu.continuousWithinAt
  -- Reduce to finite ε.
  refine MeasureTheory.tendstoInMeasure_of_ne_top ?_
  intro ε hε_pos hε_finite
  set εr : ℝ := ε.toReal with hεr_def
  have hεr_pos : 0 < εr := ENNReal.toReal_pos hε_pos.ne' hε_finite
  set ω : ℝ := εr / 2
  have hω_pos : 0 < ω := by positivity
  have hω_lt_εr : ω < εr := by show εr / 2 < εr; linarith
  -- Extract δ from UC for the modulus `(·, ω)`.
  obtain ⟨δ', hδ'_pos, hδ'⟩ := Metric.uniformContinuousOn_iff.mp hψ'_uc ω hω_pos
  set δ : ℝ := δ' / 2
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt : δ < δ' := by show δ' / 2 < δ'; linarith
  -- Convert strict UC bound to a ≤-form modulus.
  have hψ'_modulus : ∀ x ∈ Set.Icc (-M) M, ∀ z ∈ Set.Icc (-M) M,
      |x - z| ≤ δ → |deriv ψ x - deriv ψ z| ≤ ω := by
    intros x hx z hz hxz
    refine le_of_lt ?_
    have hd : dist x z < δ' := by rw [Real.dist_eq]; linarith
    have := hδ' x hx z hz hd
    rwa [Real.dist_eq] at this
  -- In-measure on `u` at `δ`.
  have hu_δ : Filter.Tendsto
      (fun σ => ν {y | ENNReal.ofReal δ ≤
        edist ((u σ : Y → ℝ) y) ((u s : Y → ℝ) y)})
      (nhdsWithin s (Set.Ici 0)) (nhds 0) :=
    hu_im (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ_pos)
  -- Squeeze: 0 ≤ ν(bad σ) ≤ ν(u-bad σ) → 0.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ => (0 : ℝ≥0∞)) (h := fun σ => ν {y | ENNReal.ofReal δ ≤
        edist ((u σ : Y → ℝ) y) ((u s : Y → ℝ) y)})
    tendsto_const_nhds hu_δ
    (Filter.Eventually.of_forall fun _ => zero_le _) ?_
  -- Show eventually-σ: ν(bad σ) ≤ ν(u-bad σ) via a.e. set inclusion.
  filter_upwards [h_u_bound] with σ hσ
  refine MeasureTheory.measure_mono_ae ?_
  have h_ae_sub := averagedDerivField_ae_sub_le_of_close (σ := σ) (s := s)
    hψ hσ h_u_s_bound hψ'_modulus
  filter_upwards [h_ae_sub] with y h_imp h_bad
  -- h_bad : y ∈ {x | ε ≤ edist (M_σ x) (ψ'(u_s x))} (i.e. ε ≤ edist (M_σ y) (ψ'(u_s y)))
  -- Goal: y ∈ {x | ENNReal.ofReal δ ≤ edist (u_σ x) (u_s x)}
  have h_bad : ε ≤ edist (averagedDerivField u ψ σ s y) (deriv ψ ((u s : Y → ℝ) y)) := h_bad
  show ENNReal.ofReal δ ≤ edist ((u σ : Y → ℝ) y) ((u s : Y → ℝ) y)
  by_contra h_not_u_bad
  have h_not_u_bad :
      edist ((u σ : Y → ℝ) y) ((u s : Y → ℝ) y) < ENNReal.ofReal δ :=
    not_le.mp h_not_u_bad
  -- h_not_u_bad : edist (u_σ y) (u_s y) < ENNReal.ofReal δ
  -- Convert edist→Real on the u-side.
  have hedist_u :
      edist ((u σ : Y → ℝ) y) ((u s : Y → ℝ) y) =
        ENNReal.ofReal |(u σ : Y → ℝ) y - (u s : Y → ℝ) y| := by
    rw [edist_dist, Real.dist_eq]
  rw [hedist_u] at h_not_u_bad
  have hu_lt : |(u σ : Y → ℝ) y - (u s : Y → ℝ) y| < δ := by
    by_contra hge
    push_neg at hge
    exact absurd h_not_u_bad (not_lt.mpr (ENNReal.ofReal_le_ofReal hge))
  have hM_bound := h_imp hu_lt.le
  -- hM_bound : |M_σ y - ψ'(u_s y)| ≤ ω
  -- Convert edist→Real on the M-side.
  have hedist_M :
      edist (averagedDerivField u ψ σ s y) (deriv ψ ((u s : Y → ℝ) y)) =
        ENNReal.ofReal |averagedDerivField u ψ σ s y - deriv ψ ((u s : Y → ℝ) y)| := by
    rw [edist_dist, Real.dist_eq]
  rw [hedist_M] at h_bad
  -- ε ≤ ENNReal.ofReal |...|; convert to εr ≤ |...|.
  have hε_ofReal : ε = ENNReal.ofReal εr :=
    (ENNReal.ofReal_toReal hε_finite).symm
  rw [hε_ofReal] at h_bad
  have hεr_le : εr ≤ |averagedDerivField u ψ σ s y - deriv ψ ((u s : Y → ℝ) y)| :=
    (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).mp h_bad
  linarith [hM_bound, hω_lt_εr, hεr_le]

/-- **L²-membership of `ψ'(u_s)` from the orbit bound + finite measure.** Direct
input for the Vitali step: the target `g := deriv ψ ∘ u_s` of the L²-convergence
needs to be in `Lp ℝ 2 ν`. From `|u_s y| ≤ M` a.e. plus the bound on `|deriv ψ|`
over `[-M, M]`, this follows immediately via `MemLp.of_bound`. -/
lemma psiDeriv_uS_memLp_two
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [IsFiniteMeasure ν]
    {u : ℝ → Lp ℝ 2 ν} {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    {s : ℝ} {M K : ℝ}
    (hψ_bound : ∀ x ∈ Set.Icc (-M) M, |deriv ψ x| ≤ K)
    (h_u_s_bound : ∀ᵐ y ∂ν, |(u s : Y → ℝ) y| ≤ M) :
    MemLp (fun y : Y => deriv ψ ((u s : Y → ℝ) y)) 2 ν := by
  refine MemLp.of_bound ?_ K ?_
  · exact (hψ.continuous_deriv le_rfl).comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)
  · filter_upwards [h_u_s_bound] with y hys
    have : (u s : Y → ℝ) y ∈ Set.Icc (-M) M := Set.mem_Icc.mpr (abs_le.mp hys)
    simpa [Real.norm_eq_abs] using hψ_bound _ this

/-- **General (Mathlib-native): Bochner–Leibniz through a strong-`L²`
right derivative.** If `u : ℝ → Lp ℝ 2 ν` has the strong-`L²` right
derivative `u'` at `s` on `[0,∞)`, `ψ : ℝ → ℝ` is `C¹`, and the orbit
`u_σ` is uniformly `L^∞`-bounded as `σ → s` from within `Set.Ici 0`
(`h_u_bound`), then `σ ↦ ∫ ψ(u_σ) dν` has the right derivative
`∫ ψ'(u_s)·u' dν`.

**Hypothesis history:** the originally drafted form bounded `ψ'` only
at `σ = s` (pointwise in `y`). That statement is **false** —
Gemini-deep-think-vetted counterexample (2026-05-19): `ν =`
Lebesgue `[0,1]`, `v(y) = |y|^{-1/3} ∈ L²`, `u σ y = y + σ·v y`,
`ψ(x) = x⁴`. At `σ = 0` the old hypothesis holds with `Cψ = 4`, but
for `σ > 0`, `ψ(u σ y)` contains `σ⁴·|y|^{-4/3}` which is not
Lebesgue-integrable, so `∫ ψ(u_σ) dν = +∞` and no derivative exists.
The MVT/FTC segment passes off the curve `u_σ`, so a pointwise bound
on `ψ'(u_σ)` alone (uniform in `σ` or not) cannot dominate `ψ'` on
the intermediate segment. The minimal Mathlib-upstream-ready fix is
to bound the orbit `u_σ` itself uniformly in a right-neighborhood of
`s`; then both endpoints and the MVT segment live in `[-M, M]` where
`ψ'` is bounded by continuity.

This is **not an axiom** — generic measure theory. Vetted proof
route (Gemini deep-think 2026-05-19, gemini-3.1-pro): pointwise FTC
`ψ(u_σ) − ψ(u_s) = M_σ · (u_σ − u_s)` with
`M_σ(y) := ∫_0^1 ψ'(u_s + t·(u_σ − u_s)) dt`; the difference quotient
is the `L²` inner product `⟨M_σ, Δσ⟩`; close via
`Filter.Tendsto.inner` after showing `M_σ → ψ'(u_s)` in `L²` (route:
L²→in-measure→a.e.-subsequence→pointwise DCT on `t` using the `[-M,M]`
dominator→back to `L²` via `tendsto_Lp_of_tendstoInMeasure`).
**No Fubini, no manual Term-A/Term-B Cauchy–Schwarz split.**

Stated with no project definitions; Mathlib-upstreamable once proved.

**Status: documented `sorry` — the reusable analytic kernel of P2
(to be proved, ~300–400 L after the simplifications above). Full
discharge plan: `plans/p2-strongL2-leibniz-discharge.md`.** -/
theorem hasDerivWithinAt_integral_of_strongL2Deriv {Y : Type*}
    [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (u : ℝ → Lp ℝ 2 ν) (u' : Lp ℝ 2 ν) {s : ℝ} (hs : 0 ≤ s)
    (hu : HasDerivWithinAt u u' (Set.Ici 0) s)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (h_u_bound : ∃ M : ℝ,
        ∀ᶠ σ in nhdsWithin s (Set.Ici 0),
          ∀ᵐ y ∂ν, |(u σ : Y → ℝ) y| ≤ M) :
    HasDerivWithinAt (fun σ => ∫ y, ψ ((u σ : Y → ℝ) y) ∂ν)
      (∫ y, deriv ψ ((u s : Y → ℝ) y) * (u' : Y → ℝ) y ∂ν)
      (Set.Ici 0) s := by
  sorry

/-- **P2 core — the differentiation-under-the-integral.**
`grossPow` has right derivative `grossPowDeriv` on `[0,∞)`.

**Decomposed** (no axiom): the diagonal total derivative of
`H(σ,τ) = ∫ |u_σ|^{q(τ)}` is `∂₂H(s,s) + ∂₁H(s,s)` where

* `∂₂H(s,s) = q'(s)·∫ |u_s|^{q(s)} log|u_s|` — exponent half, from
  the general `hasDerivAt_integral_rpow_exponent` (orbit frozen at
  `w := u_s`, `a := q`);
* `∂₁H(s,s) = ∫ ψ'(u_s)·A(u_s)` with `ψ = |·|^{q(s)}` — semigroup
  half, from the general `hasDerivWithinAt_integral_of_strongL2Deriv`
  (`u' = A(u_s)` supplied by `h_gen`; `u_s ∈ core` by `h_core`; the
  uniform `L^∞` orbit bound `h_u_bound` is supplied from `D.IsCore f`
  + Markov-semigroup `L^∞`-contractivity `D.semigroup_contraction`,
  giving `‖P_σ f‖_∞ ≤ ‖f‖_∞` uniformly in `σ ≥ 0`), rewritten
  `= −q(s)·E(u_s, u_s^{q(s)-1})` via `h_gen`'s form pairing.

The remaining glue is the standard partial-⇒-total step (continuity
of one partial) plus matching `∫ ψ'·(A u)` to the `energy` pairing.

**Status: documented `sorry` — now reduced to two isolated general
lemmas + this glue.** -/
theorem grossPow_hasDerivWithinAt
    (D : DirichletMarkovSemigroup X) (ρ p : ℝ) (hρ : 0 < ρ) (hp : 1 < p)
    (h_core : CoreSemigroupInvariant D)
    (h_gen : GeneratorCompat D)
    {f : X → ℝ} (hf : D.IsCore f) (hf_nonneg : ∀ x, 0 ≤ f x)
    {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (grossPow D hf ρ p)
      (grossPowDeriv D hf ρ p s) (Set.Ici 0) s := by
  sorry

/-- **P2 — the Gross ODE (right-derivative form).** For nonnegative
core `f` with `ρ > 0`, `p > 1`, the log-norm `Λ(s) = q(s)⁻¹ log F(s)`
has right derivative `grossLogNormDeriv` on `[0,∞)`.

**Assembled (proved here)** from `grossPow_hasDerivWithinAt` (`F'`,
the bottleneck), `grossPow_pos` (`F > 0`), `hasDerivAt_grossExponent`
(`q' = 2ρ(q-1)`) and `grossEntropy_eq` via the chain rule for
`q⁻¹ · log F`: the resulting `−(q'/q²)log F + q⁻¹·F'/F` equals
`grossLogNormDeriv = (q'/(q²F))·Ent(uq) − E/F` after substituting
`Ent(uq) = q·∫uq log u − F log F` and `F' = q'·∫uq log u − q·E`. -/
theorem grossLogNorm_hasDerivWithinAt
    (D : DirichletMarkovSemigroup X) (ρ p : ℝ) (hρ : 0 < ρ) (hp : 1 < p)
    (h_core : CoreSemigroupInvariant D)
    (h_gen : GeneratorCompat D)
    {f : X → ℝ} (hf : D.IsCore f) (hf_nonneg : ∀ x, 0 ≤ f x)
    {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (grossLogNorm D hf ρ p)
      (grossLogNormDeriv D hf ρ p s) (Set.Ici 0) s := by
  set q := grossExponent ρ p s with hq_def
  have hqpos : 0 < q := grossExponent_pos hp ρ s
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hFpos : 0 < grossPow D hf ρ p s :=
    grossPow_pos D ρ p hρ hp hf hf_nonneg hs
  have hFne : grossPow D hf ρ p s ≠ 0 := ne_of_gt hFpos
  -- q has the within-derivative `q' = 2ρ(q-1)`.
  have hq : HasDerivWithinAt (grossExponent ρ p)
      (2 * ρ * (q - 1)) (Set.Ici 0) s :=
    (hasDerivAt_grossExponent ρ p s).hasDerivWithinAt
  -- 1/q has within-derivative `-(q')/q²`.
  have hinv : HasDerivWithinAt (fun s => (grossExponent ρ p s)⁻¹)
      (-(2 * ρ * (q - 1)) / q ^ 2) (Set.Ici 0) s := by
    simpa using hq.inv hqne
  -- F = grossPow has within-derivative `F' = grossPowDeriv`.
  have hF : HasDerivWithinAt (grossPow D hf ρ p)
      (grossPowDeriv D hf ρ p s) (Set.Ici 0) s :=
    grossPow_hasDerivWithinAt D ρ p hρ hp h_core h_gen hf hf_nonneg hs
  -- log F has within-derivative `F'/F`.
  have hlog : HasDerivWithinAt
      (fun s => Real.log (grossPow D hf ρ p s))
      ((grossPow D hf ρ p s)⁻¹ * grossPowDeriv D hf ρ p s)
      (Set.Ici 0) s := by
    simpa [mul_comm] using
      (Real.hasDerivAt_log hFne).comp_hasDerivWithinAt s hF
  -- Λ = (1/q) · log F by the product rule; reconcile the chain value
  -- with `grossLogNormDeriv` via the entropy identity.
  have hmul := hinv.mul hlog
  have hval : (-(2 * ρ * (q - 1)) / q ^ 2)
        * Real.log (grossPow D hf ρ p s)
      + (grossExponent ρ p s)⁻¹
        * ((grossPow D hf ρ p s)⁻¹ * grossPowDeriv D hf ρ p s)
      = grossLogNormDeriv D hf ρ p s := by
    rw [grossLogNormDeriv, grossEntropy_eq D ρ p hf, grossPowDeriv,
      grossLogIntegral, ← hq_def]
    field_simp
    ring
  have : HasDerivWithinAt (grossLogNorm D hf ρ p)
      ((-(2 * ρ * (q - 1)) / q ^ 2) * Real.log (grossPow D hf ρ p s)
        + (grossExponent ρ p s)⁻¹
          * ((grossPow D hf ρ p s)⁻¹ * grossPowDeriv D hf ρ p s))
      (Set.Ici 0) s := by
    simpa [grossLogNorm] using hmul
  rwa [hval] at this

/-! ## P3 — algebraic closure -/

/-- **P3 (the Gross cancellation).** The P2 derivative value is
`≤ 0`: LSI on `v = u^{q/2}` gives `Entμ(u^q) ≤ (2/ρ) E(v,v)`; the
coupling `q' = 2ρ(q-1)` turns `2q'/(ρ q²)` into `4(q-1)/q²`; and
Stroock–Varopoulos gives `(4(q-1)/q²) E(u^{q/2},u^{q/2}) ≤
E(u,u^{q-1})`. Hence the whole expression collapses to
`F⁻¹·[(4(q-1)/q²)E(u^{q/2},u^{q/2}) − E(u,u^{q-1})] ≤ 0`.

**Status: `sorry` — P3 algebra (`plans/gross-discharge.md`,
~200–400 L); proof recorded above and in the module docstring.** -/
theorem grossLogNorm_deriv_nonpos
    (D : DirichletMarkovSemigroup X) (ρ p : ℝ) (hρ : 0 < ρ) (hp : 1 < p)
    (h_lsi : D.SatisfiesLogSobolev ρ)
    (h_sv : StroockVaropoulos D)
    {f : X → ℝ} (hf : D.IsCore f) (hf_nonneg : ∀ x, 0 ≤ f x)
    {s : ℝ} (hs : 0 < s) :
    grossLogNormDeriv D hf ρ p s ≤ 0 := by
  sorry

/-- `Λ` is antitone on `[0,∞)`: continuity (P2 gives a right
derivative everywhere on the interior, hence continuity there;
endpoint continuity from the difference quotient) + the nonpositive
right derivative, via `antitoneOn_of_hasDerivWithinAt_nonpos`. -/
theorem grossLogNorm_antitoneOn
    (D : DirichletMarkovSemigroup X) (ρ p : ℝ) (hρ : 0 < ρ) (hp : 1 < p)
    (h_lsi : D.SatisfiesLogSobolev ρ)
    (h_core : CoreSemigroupInvariant D)
    (h_gen : GeneratorCompat D)
    (h_sv : StroockVaropoulos D)
    {f : X → ℝ} (hf : D.IsCore f) (hf_nonneg : ∀ x, 0 ≤ f x) :
    AntitoneOn (grossLogNorm D hf ρ p) (Set.Ici 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (f' := grossLogNormDeriv D hf ρ p) ?_ ?_ ?_
  · -- continuity on `[0,∞)`: each point has a within-derivative (P2),
    -- so `Λ` is continuous there.
    sorry
  · intro x hx
    have hx0 : 0 ≤ x := le_of_lt (by simpa using hx)
    -- `interior (Ici 0) = Ioi 0`; restrict the P2 within-derivative.
    exact (grossLogNorm_hasDerivWithinAt D ρ p hρ hp h_core h_gen hf
      hf_nonneg hx0).mono interior_subset
  · intro x hx
    exact grossLogNorm_deriv_nonpos D ρ p hρ hp h_lsi h_sv hf hf_nonneg
      (by simpa using hx)

end GrossODE

/-! ## Assembly -/

variable {X : Type*} [MeasurableSpace X]

/-- **Gross 1975, forward direction — hypothesis-parameterised.**
LSI ⇒ hypercontractivity for any `DirichletMarkovSemigroup` also
satisfying core-invariance, generator–form compatibility, and
Stroock–Varopoulos. Carries the proof relocated out of
`Hypercontractivity.lean` (where only the predicates live).

Scaffolded: reduces to `grossLogNorm_antitoneOn` (P2 ⊕ P3) plus the
`eLpNorm ↔ ∫·^q` identification and `Lᵖ`-norm monotonicity for a
probability measure (the `WLOG f ≥ 0, f ∈ core, dense core` reduction
of `IsHypercontractive`). Those reduction bridges are documented
`sorry`s; the Gross-ODE spine is in place. -/
theorem gross_lsi_implies_hypercontractive_of_hypotheses
    (D : DirichletMarkovSemigroup X) (ρ : ℝ) (hρ : 0 < ρ)
    (h_lsi : D.SatisfiesLogSobolev ρ)
    (h_core : CoreSemigroupInvariant D)
    (h_gen : GeneratorCompat D)
    (h_sv : StroockVaropoulos D) :
    D.toMarkovSemigroup.IsHypercontractive ρ := by
  refine ⟨hρ, ?_⟩
  intro p q t hp hpq ht hqt f hf_mem
  -- Reduction (documented): `WLOG f ≥ 0` (replace by `|f|`); approximate
  -- by core; identify `eLpNorm · (ofReal r)` with `(∫ ·^r)^{1/r}`;
  -- then `‖P_t f‖_q ≤ ‖P_t f‖_{q(t)}` (probability measure, `q ≤ q(t)`
  -- since `hqt`) `= exp (grossLogNorm … t) ≤ exp (grossLogNorm … 0)`
  -- (by `GrossODE.grossLogNorm_antitoneOn` applied to `0 ≤ t`)
  -- `= ‖f‖_p = ‖f‖_p`.
  sorry
