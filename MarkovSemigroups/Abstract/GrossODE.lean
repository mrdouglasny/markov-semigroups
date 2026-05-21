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
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

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

/-- `grossExponent ρ p` is `C^∞` (and hence `C^1`). Composition of constants,
linear maps, and `Real.exp`. -/
theorem contDiff_grossExponent (ρ p : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (grossExponent ρ p) := by
  unfold grossExponent
  have h_lin : ContDiff ℝ n (fun s : ℝ => 2 * ρ * s) :=
    (contDiff_const.mul contDiff_id)
  have h_exp : ContDiff ℝ n (fun s : ℝ => Real.exp (2 * ρ * s)) :=
    Real.contDiff_exp.comp h_lin
  have h_mul : ContDiff ℝ n (fun s : ℝ => (p - 1) * Real.exp (2 * ρ * s)) :=
    contDiff_const.mul h_exp
  exact contDiff_const.add h_mul

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

/-- `F(s) = ∫ |u_s|^{q(s)} > 0`. Holds whenever
* `f` is *not* `μ`-a.e. zero (the `f ≡ 0` case is handled separately
  in the assembly), AND
* the orbit `|P_s f|^{q(s)}` is integrable (otherwise Mathlib's
  convention `∫ (non-integrable) = 0` makes the conclusion false even
  for nonzero `f`; in concrete Gross applications this comes from
  L^{q(s)}-regularity of the orbit, which is part of what
  hypercontractivity asserts and is supplied externally here).

**Proof strategy (Gemini-vetted 2026-05-20):** `f ≥ 0` and `f ≢ᵐ 0`
imply `∫ f dμ > 0` (Bochner `integral_pos_iff_support_of_nonneg_ae`);
symmetry of `P_s` plus `P_conservation` (`P_s 1 = 1`) gives
`∫ P_s f dμ = ⟨P_s f, 1⟩ = ⟨f, P_s 1⟩ = ⟨f, 1⟩ = ∫ f dμ > 0`; combined
with `P_positivity` (`P_s f ≥ 0` a.e.), the orbit `P_s f` has positive
support, and `q(s) > 0` then implies `|P_s f|^{q(s)} > 0` on the same
positive-measure set ⇒ `0 < ∫ |P_s f|^{q(s)} dμ`.

**Status: documented `sorry` — vetted signature fix landed 2026-05-20
(was provably false-as-stated for `f := 0`, since `IsCore_const 0`
puts `0` in the core; counterexample-vetted by Gemini deep-think,
`gemini-3.1-pro-preview`). Body proof + integrability hypothesis
strengthening deferred.** -/
theorem grossPow_pos (D : DirichletMarkovSemigroup X) (ρ p : ℝ)
    (hρ : 0 < ρ) (hp : 1 < p) {f : X → ℝ} (hf : D.IsCore f)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_ne : ¬ f =ᵐ[D.μ] 0)
    {s : ℝ} (hs : 0 ≤ s)
    (h_int : Integrable (fun x => |((D.P s (D.coreToL2 hf) : X → ℝ) x)|
                          ^ grossExponent ρ p s) D.μ) :
    0 < grossPow D hf ρ p s := by
  haveI : IsFiniteMeasure D.μ := inferInstance
  set u_Lp : Lp ℝ 2 D.μ := D.P s (D.coreToL2 hf) with hu_Lp_def
  set u : X → ℝ := (u_Lp : X → ℝ) with hu_def
  set q : ℝ := grossExponent ρ p s with hq_def
  have hq_pos : 0 < q := grossExponent_pos hp ρ s
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  -- Step A: u ≥ 0 a.e. (from f ≥ 0 + P_positivity).
  have hcoe_f : (D.coreToL2 hf : X → ℝ) =ᵐ[D.μ] f :=
    (D.IsCore_memLp hf).coeFn_toLp
  have hf_Lp_nonneg : (0 : Lp ℝ 2 D.μ) ≤ D.coreToL2 hf := by
    rw [← Lp.coeFn_nonneg]
    filter_upwards [hcoe_f] with x hx
    rw [hx]; exact hf_nonneg x
  have hu_Lp_nonneg : (0 : Lp ℝ 2 D.μ) ≤ u_Lp :=
    D.P_positivity s hs _ hf_Lp_nonneg
  have hu_nonneg_ae : 0 ≤ᵐ[D.μ] u := (Lp.coeFn_nonneg _).mpr hu_Lp_nonneg
  -- Step B: ∫ u dμ = ∫ f dμ via P_symmetric + P_conservation.
  set one_Lp : Lp ℝ 2 D.μ := Lp.const 2 D.μ (1 : ℝ) with hone_Lp_def
  have hone_coe : (one_Lp : X → ℝ) =ᵐ[D.μ] (fun _ => (1 : ℝ)) := by
    exact Lp.coeFn_const 2 D.μ (1 : ℝ)
  have hPone : D.P s one_Lp = one_Lp := by
    apply D.P_conservation s hs one_Lp
    filter_upwards [hone_coe] with x hx; simpa using hx
  have h_inner_one : ∀ (g_Lp : Lp ℝ 2 D.μ),
      @inner ℝ (Lp ℝ 2 D.μ) _ g_Lp one_Lp = ∫ x, (g_Lp : X → ℝ) x ∂D.μ := by
    intro g_Lp
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hone_coe] with x hx
    show @inner ℝ ℝ _ ((g_Lp : X → ℝ) x) ((one_Lp : X → ℝ) x) = (g_Lp : X → ℝ) x
    rw [hx]
    show 1 * (g_Lp : X → ℝ) x = (g_Lp : X → ℝ) x
    ring
  have hsymm : @inner ℝ (Lp ℝ 2 D.μ) _ (D.coreToL2 hf) (D.P s one_Lp)
              = @inner ℝ (Lp ℝ 2 D.μ) _ u_Lp one_Lp :=
    D.P_symmetric s hs (D.coreToL2 hf) one_Lp
  rw [hPone, h_inner_one, h_inner_one] at hsymm
  -- hsymm : ∫ (coreToL2 hf) = ∫ u.
  have h_u_eq_f : ∫ x, u x ∂D.μ = ∫ x, f x ∂D.μ := by
    rw [← hsymm]; exact integral_congr_ae hcoe_f
  -- Step C: ∫ f > 0 from f ≥ 0 + f ≢ᵐ 0.
  have hf_int : Integrable f D.μ := (D.IsCore_memLp hf).integrable one_le_two
  have hf_int_pos : 0 < ∫ x, f x ∂D.μ := by
    rw [integral_pos_iff_support_of_nonneg_ae
        (Filter.Eventually.of_forall hf_nonneg) hf_int]
    by_contra h
    push_neg at h
    refine hf_ne ?_
    rw [Filter.EventuallyEq, ae_iff]
    exact le_antisymm h (zero_le _)
  -- Step D: 0 < ∫ |u|^q. Use integral_pos_iff_support + support (|u|^q) = support u.
  show 0 < ∫ x, |u x| ^ q ∂D.μ
  rw [integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (abs_nonneg _) _)) h_int]
  -- Goal: 0 < μ (support (|u|^q)).
  have hsupp_eq : Function.support (fun x => |u x| ^ q) = Function.support u := by
    ext x
    simp only [Function.mem_support]
    constructor
    · intro hne
      intro hux
      apply hne
      rw [hux, abs_zero, Real.zero_rpow hq_ne]
    · intro hne hux
      apply hne
      rw [Real.rpow_eq_zero_iff_of_nonneg (abs_nonneg _)] at hux
      exact abs_eq_zero.mp hux.1
  rw [hsupp_eq]
  -- support u = {x : u x ≠ 0}. Suffices: 0 < ∫ u.
  rw [← integral_pos_iff_support_of_nonneg_ae hu_nonneg_ae]
  · rw [h_u_eq_f]; exact hf_int_pos
  · -- Integrable u: from MemLp 2 + finite measure.
    exact (Lp.memLp _).integrable one_le_two

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
  -- Pure log-of-power algebra: log(|u|^q) = q · log|u| pointwise (handling
  -- |u| = 0 via Mathlib's `0^q = 0` / `log 0 = 0` conventions).
  unfold DirichletSpace.entropy grossPow grossLogIntegral
  set u : X → ℝ := ((D.P s (D.coreToL2 hf) : X → ℝ))
  set q : ℝ := grossExponent ρ p s
  -- The second term `(∫ g)·log(∫ g) = F · log F` is exactly the second term of
  -- the entropy minus the RHS minus part; the first term `∫ g log g`
  -- pointwise-equals `q · (|u|^q · log|u|)`, which integrates to
  -- `q · grossLogIntegral` via `integral_const_mul`.
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with x
  -- Pointwise: |u x|^q · log(|u x|^q) = q · (|u x|^q · log|u x|).
  by_cases hq : q = 0
  · simp [hq, Real.rpow_zero]
  · rcases eq_or_ne |u x| 0 with hux | hux
    · simp [hux, Real.zero_rpow hq, Real.log_zero]
    · have hu_pos : 0 < |u x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hux)
      rw [Real.log_rpow hu_pos]
      ring

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
`C¹`-differentiable positive exponent path `a`,
`σ ↦ ∫ |w|^{a σ}` is differentiable at `s` with derivative
`a'(s) · ∫ |w|^{a s} · log|w|`. The pointwise exponent
derivative is `∂_σ |w y|^{a σ} = |w y|^{a σ} · log|w y| · a'`
(`hasDerivAt_abs_rpow_exponent` above; the `w y = 0` case is constant
`0` since `a > 0`).

**Strategy** (apply Mathlib
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`):

* Nbhd `Metric.ball s 1` ⊆ `Icc (s-1) (s+1)`; compactness +
  `ContDiff ℝ 1 a` give bounds `a_min ≤ a σ ≤ a_max` on `Icc` and
  `|deriv a σ| ≤ K`. `a_min > 0` from `ha_pos`.
* Bound on `|F'(σ, y)| = |w y|^{a σ} · |log |w y|| · |deriv a σ|`:
    - `|w y| ∈ [0, M]` (or `[0, max(M, 1)]`).
    - For `|w y| ∈ (0, 1]`: `t^a · |log t| ≤ 1/(e · a) ≤ 1/(e · a_min)`
      (max of `t ↦ t^a · log(1/t)` on `(0,1]` at `t = e^{-1/a}`).
    - For `|w y| ∈ [1, M]` (M ≥ 1): `t^a · log t ≤ M^{a_max} · log M`.
    - For `|w y| = 0`: value is 0 (`Real.zero_rpow (ha_pos σ).ne'`).
  Total bound `B := K · max(1/(e·a_min), max(M, 1)^{a_max} · log max(M, 1))`,
  a constant ⇒ integrable on finite measure.
* `h_diff` from `hasDerivAt_abs_rpow_exponent (w y) (ha_cd.differentiable
  le_rfl).differentiableAt.hasDerivAt ha_pos`.
* The resulting `∫ F' s = (deriv a s) · ∫ |w|^{a s} · log|w|` via
  `integral_mul_const`; identify `deriv a s = a'` via `ha.deriv`.

**Effort:** ~150–200 LOC; the `t^a · |log t|` analytic supremum
(`(e · a)⁻¹` on `(0,1]`) requires a manual proof (not in Mathlib as a
direct lemma). No project definitions; Mathlib-upstreamable.

**Status: documented `sorry` — signature has the corrected
`ContDiff ℝ 1 a` hypothesis (the original `HasDerivAt a a' s` at a
single point was too weak to apply the parametric DCT; pointed out by
the `hasDerivAt_integral_of_dominated_loc_of_deriv_le` interface which
needs `h_diff` in a neighborhood). Body deferred. -/
theorem hasDerivAt_integral_rpow_exponent {Y : Type*}
    [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    {w : Y → ℝ} (hw : AEStronglyMeasurable w ν) {M : ℝ}
    (hM : ∀ᵐ y ∂ν, |w y| ≤ M)
    {a : ℝ → ℝ} {a' s : ℝ}
    (ha_cd : ContDiff ℝ 1 a) (ha : HasDerivAt a a' s)
    (ha_pos : ∀ σ, 0 < a σ) :
    HasDerivAt (fun σ => ∫ y, |w y| ^ a σ ∂ν)
      (a' * ∫ y, |w y| ^ a s * Real.log |w y| ∂ν) s := by
  -- Notation + continuity from ContDiff 1.
  have ha_cont : Continuous a := ha_cd.continuous
  have ha_diff : Differentiable ℝ a := ha_cd.differentiable (by decide)
  have ha_deriv_cont : Continuous (deriv a) := ha_cd.continuous_deriv le_rfl
  -- Compact J = [s-1, s+1]; bounds.
  set J : Set ℝ := Set.Icc (s - 1) (s + 1) with hJ_def
  have hJ_cpt : IsCompact J := isCompact_Icc
  have hJ_ne : J.Nonempty := ⟨s, by constructor <;> linarith⟩
  obtain ⟨σ_amin, _, h_amin⟩ := hJ_cpt.exists_isMinOn hJ_ne ha_cont.continuousOn
  set a_min : ℝ := a σ_amin with ha_min_def
  have ha_min_pos : 0 < a_min := ha_pos σ_amin
  obtain ⟨σ_amax, _, h_amax⟩ := hJ_cpt.exists_isMaxOn hJ_ne ha_cont.continuousOn
  set a_max : ℝ := a σ_amax with ha_max_def
  have ha_max_pos : 0 < a_max := ha_pos σ_amax
  obtain ⟨σ_K, _, h_K⟩ := hJ_cpt.exists_isMaxOn hJ_ne
    (continuous_abs.comp ha_deriv_cont).continuousOn
  set K : ℝ := |deriv a σ_K| with hK_def
  have hK_nn : 0 ≤ K := abs_nonneg _
  set M' : ℝ := max M 1 with hM'_def
  have hM'_one : (1 : ℝ) ≤ M' := le_max_right _ _
  have hM'_pos : 0 < M' := lt_of_lt_of_le one_pos hM'_one
  have hM'_log_nn : 0 ≤ Real.log M' := Real.log_nonneg hM'_one
  have hw_le_M' : ∀ᵐ y ∂ν, |w y| ≤ M' := by
    filter_upwards [hM] with y hy
    exact le_trans hy (le_max_left _ _)
  set Cprod : ℝ := 1 / (Real.exp 1 * a_min) + M' ^ a_max * Real.log M' with hCprod_def
  have hCprod_nn : 0 ≤ Cprod := by
    refine add_nonneg ?_ ?_
    · positivity
    · exact mul_nonneg (Real.rpow_nonneg hM'_pos.le _) hM'_log_nn
  set B : ℝ := K * Cprod with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hK_nn hCprod_nn
  -- Open neighborhood `ball s 1 ⊆ J`.
  set U : Set ℝ := Metric.ball s 1 with hU_def
  have hU_subJ : U ⊆ J := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    refine ⟨?_, ?_⟩ <;> [linarith [abs_lt.mp hx]; linarith [abs_lt.mp hx]]
  have hU_nhds : U ∈ nhds s := Metric.ball_mem_nhds s one_pos
  -- Pointwise bound on `t ^ a σ * log t` for `t ∈ [0, M']` and `a σ ∈ [a_min, a_max]`.
  have h_prod_bound : ∀ (t : ℝ) (_ : 0 ≤ t) (_ : t ≤ M') (σ : ℝ) (_ : σ ∈ J),
      |t ^ a σ * Real.log t| ≤ Cprod := by
    intro t ht_nn ht_M' σ hσ
    have ha_σ_pos : 0 < a σ := ha_pos σ
    have h_amin_le : a_min ≤ a σ := h_amin hσ
    have h_amax_ge : a σ ≤ a_max := h_amax hσ
    have hM'_term_nn : 0 ≤ M' ^ a_max * Real.log M' :=
      mul_nonneg (Real.rpow_nonneg hM'_pos.le _) hM'_log_nn
    have hEmin_nn : (0:ℝ) ≤ 1 / (Real.exp 1 * a_min) := by positivity
    rcases eq_or_lt_of_le ht_nn with ht_eq | ht_pos
    · -- t = 0: |0^{a σ} * log 0| = 0 ≤ Cprod.
      have h0 : |t ^ a σ * Real.log t| = 0 := by
        rw [show t = 0 from ht_eq.symm, Real.zero_rpow ha_σ_pos.ne']
        simp
      linarith
    rcases le_or_gt t 1 with ht_le1 | ht_gt1
    · -- t ∈ (0, 1].
      have hlog_np : Real.log t ≤ 0 := Real.log_nonpos ht_nn ht_le1
      have h_abs : |t ^ a σ * Real.log t| = t ^ a σ * (-Real.log t) := by
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht_nn _),
            abs_of_nonpos hlog_np]
      rw [h_abs]
      -- y := a σ · (-log t) ≥ 0. Apply mul_exp_neg_le_exp_neg_one.
      have h_y_bd :
          a σ * (-Real.log t) * Real.exp (-(a σ * (-Real.log t))) ≤ Real.exp (-1) :=
        Real.mul_exp_neg_le_exp_neg_one _
      have h_exp_eq : Real.exp (-(a σ * (-Real.log t))) = t ^ a σ := by
        have h_eq : -(a σ * (-Real.log t)) = Real.log t * a σ := by ring
        rw [h_eq, ← Real.rpow_def_of_pos ht_pos]
      rw [h_exp_eq] at h_y_bd
      -- (-log t) · t^{a σ} ≤ exp(-1) / (a σ) = 1/(e·a σ) ≤ 1/(e·a_min).
      have h_div : t ^ a σ * (-Real.log t) ≤ 1 / (Real.exp 1 * a σ) := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < Real.exp 1 * a σ)]
        have h_calc :
            t ^ a σ * (-Real.log t) * (Real.exp 1 * a σ)
              = a σ * (-Real.log t) * t ^ a σ * Real.exp 1 := by ring
        rw [h_calc]
        have hexp1_nn : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
        calc a σ * (-Real.log t) * t ^ a σ * Real.exp 1
            ≤ Real.exp (-1) * Real.exp 1 :=
                mul_le_mul_of_nonneg_right h_y_bd hexp1_nn
          _ = 1 := by
                rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have h_div_amin : 1 / (Real.exp 1 * a σ) ≤ 1 / (Real.exp 1 * a_min) := by
        apply one_div_le_one_div_of_le
        · positivity
        · exact mul_le_mul_of_nonneg_left h_amin_le (Real.exp_pos 1).le
      linarith
    · -- t ∈ (1, M'].
      have ht_pos : 0 < t := lt_trans one_pos ht_gt1
      have hlog_nn : 0 ≤ Real.log t := Real.log_nonneg ht_gt1.le
      have h_abs : |t ^ a σ * Real.log t| = t ^ a σ * Real.log t := by
        rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht_nn _) hlog_nn)]
      rw [h_abs]
      have h_pow_le_t_amax : t ^ a σ ≤ t ^ a_max :=
        Real.rpow_le_rpow_of_exponent_le ht_gt1.le h_amax_ge
      have h_t_amax_le : t ^ a_max ≤ M' ^ a_max :=
        Real.rpow_le_rpow ht_nn ht_M' ha_max_pos.le
      have h_pow_le : t ^ a σ ≤ M' ^ a_max := le_trans h_pow_le_t_amax h_t_amax_le
      have h_log_le : Real.log t ≤ Real.log M' :=
        Real.log_le_log ht_pos ht_M'
      have h_prod_le : t ^ a σ * Real.log t ≤ M' ^ a_max * Real.log M' := by
        gcongr
      linarith
  -- Apply the parametric Leibniz lemma.
  have ha'_eq : a' = deriv a s := ha.deriv.symm
  -- F σ y := |w y|^{a σ}; F' σ y := |w y|^{a σ} · log|w y| · deriv a σ.
  set F : ℝ → Y → ℝ := fun σ y => |w y| ^ a σ with hF_def
  set F' : ℝ → Y → ℝ := fun σ y => |w y| ^ a σ * Real.log |w y| * deriv a σ
    with hF'_def
  -- AEStronglyMeasurable of `F σ` and `F' σ`.
  have hF_aesm : ∀ σ, AEStronglyMeasurable (F σ) ν := fun σ => by
    show AEStronglyMeasurable (fun y => |w y| ^ a σ) ν
    exact (continuous_abs.rpow_const
      (fun _ => Or.inr (ha_pos σ).le)).comp_aestronglyMeasurable hw
  have hF'_aesm : ∀ σ, AEStronglyMeasurable (F' σ) ν := fun σ => by
    show AEStronglyMeasurable (fun y => |w y| ^ a σ * Real.log |w y| * deriv a σ) ν
    refine ((hF_aesm σ).mul ?_).mul_const _
    -- AEStronglyMeasurable (fun y => Real.log |w y|) ν.
    refine (Real.measurable_log.comp_aemeasurable ?_).aestronglyMeasurable
    exact (continuous_abs.comp_aestronglyMeasurable hw).aemeasurable
  -- Bound: ‖F' σ y‖ ≤ B for σ ∈ U, a.e. y.
  have h_F'_bound : ∀ᵐ y ∂ν, ∀ σ ∈ U, ‖F' σ y‖ ≤ B := by
    filter_upwards [hw_le_M'] with y hy_M' σ hσU
    have hσ_J : σ ∈ J := hU_subJ hσU
    have hd_le : |deriv a σ| ≤ K := h_K hσ_J
    have hprod := h_prod_bound (|w y|) (abs_nonneg _) hy_M' σ hσ_J
    have : ‖F' σ y‖ = |F' σ y| := Real.norm_eq_abs _
    rw [this]
    show |(|w y| ^ a σ * Real.log |w y|) * deriv a σ| ≤ K * Cprod
    rw [abs_mul]
    calc |(|w y| ^ a σ * Real.log |w y|)| * |deriv a σ|
        ≤ Cprod * K := mul_le_mul hprod hd_le (abs_nonneg _) hCprod_nn
      _ = K * Cprod := by ring
  -- Integrable F s.
  have hFs_int : Integrable (F s) ν := by
    refine Integrable.mono' (g := fun _ => M' ^ a_max + 1) (integrable_const _)
      (hF_aesm s) ?_
    filter_upwards [hw_le_M'] with y hy_M'
    show ‖|w y| ^ a s‖ ≤ M' ^ a_max + 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hs_J : s ∈ J := ⟨by linarith, by linarith⟩
    have has_max : a s ≤ a_max := h_amax hs_J
    rcases le_or_gt (|w y|) 1 with hle | hgt
    · have : |w y| ^ a s ≤ 1 := Real.rpow_le_one (abs_nonneg _) hle (ha_pos s).le
      linarith [Real.rpow_nonneg hM'_pos.le a_max]
    · have h_pow : |w y| ^ a s ≤ M' ^ a_max := by
        calc |w y| ^ a s ≤ |w y| ^ a_max :=
              Real.rpow_le_rpow_of_exponent_le hgt.le has_max
          _ ≤ M' ^ a_max := Real.rpow_le_rpow (abs_nonneg _) hy_M' ha_max_pos.le
      linarith
  -- h_diff: pointwise differentiability for σ ∈ U (holds for all y).
  have h_diff : ∀ᵐ y ∂ν, ∀ σ ∈ U, HasDerivAt (fun σ' => |w y| ^ a σ') (F' σ y) σ := by
    refine Filter.Eventually.of_forall (fun y σ _ => ?_)
    exact hasDerivAt_abs_rpow_exponent (w y) (ha_diff.differentiableAt.hasDerivAt) ha_pos
  -- Apply hasDerivAt_integral_of_dominated_loc_of_deriv_le.
  have h_main :
      Integrable (F' s) ν ∧
      HasDerivAt (fun σ => ∫ y, F σ y ∂ν) (∫ y, F' s y ∂ν) s := by
    apply hasDerivAt_integral_of_dominated_loc_of_deriv_le hU_nhds
      (Filter.Eventually.of_forall hF_aesm) hFs_int (hF'_aesm s)
      h_F'_bound
      (integrable_const _)
      h_diff
  -- Identify ∫ F' s = a' * ∫ |w|^{a s} · log|w|.
  have h_int_F's : ∫ y, F' s y ∂ν =
      deriv a s * ∫ y, |w y| ^ a s * Real.log |w y| ∂ν := by
    show ∫ y, |w y| ^ a s * Real.log |w y| * deriv a s ∂ν
        = deriv a s * ∫ y, |w y| ^ a s * Real.log |w y| ∂ν
    rw [integral_mul_const, mul_comm]
  convert h_main.2 using 1
  rw [h_int_F's, ha.deriv]

/-- Mean value theorem packaged with an unordered interval witness. -/
lemma exists_hasDerivAt_eq_slope_uIcc {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≠ b) (hfc : Continuous f) (hff' : ∀ x : ℝ, HasDerivAt f (f' x) x) :
    ∃ c ∈ Set.uIcc a b, (f b - f a) / (b - a) = f' c := by
  rcases lt_or_gt_of_ne hab with hab' | hba'
  · obtain ⟨c, hc, hceq⟩ :=
      exists_hasDerivAt_eq_slope f f' hab' hfc.continuousOn (fun x _ => hff' x)
    refine ⟨c, ?_, hceq.symm⟩
    simpa [Set.uIcc, min_eq_left hab'.le, max_eq_right hab'.le] using
      Set.mem_Icc.mpr ⟨hc.1.le, hc.2.le⟩
  · obtain ⟨c, hc, hceq⟩ :=
      exists_hasDerivAt_eq_slope (a := b) (b := a) f f' hba' hfc.continuousOn
        (fun x _ => hff' x)
    have hquot : (f b - f a) / (b - a) = (f a - f b) / (a - b) := by
      have h1 : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
      have h2 : a - b ≠ 0 := sub_ne_zero.mpr hab
      field_simp [h1, h2]
      ring
    refine ⟨c, ?_, hquot.trans hceq.symm⟩
    simpa [Set.uIcc, min_eq_right hba'.le, max_eq_left hba'.le] using
      Set.mem_Icc.mpr ⟨hc.1.le, hc.2.le⟩

/-- For a real-valued function, the integral of the absolute value is the `L¹` seminorm. -/
lemma integral_abs_eq_eLpNorm_one_toReal {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {f : Y → ℝ} (hf : Integrable (fun y => |f y|) ν) :
    ∫ y, |f y| ∂ν = (eLpNorm f 1 ν).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => abs_nonneg _) hf.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm]
  congr 1
  apply lintegral_congr_ae
  filter_upwards with y
  simp [Real.enorm_eq_ofReal_abs]

/-- On a probability space, `L² → 0` implies the integral of the absolute value tends to `0`. -/
lemma tendsto_integral_abs_of_tendsto_eLpNorm_two_zero {ι Y : Type*}
    [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν] {l : Filter ι}
    (F : ι → Y → ℝ)
    (hF_meas : ∀ i, AEStronglyMeasurable (F i) ν)
    (hF_int : ∀ᶠ i in l, Integrable (fun y => |F i y|) ν)
    (hF_two : Filter.Tendsto (fun i => eLpNorm (F i) 2 ν) l (nhds 0)) :
    Filter.Tendsto (fun i => ∫ y, |F i y| ∂ν) l (nhds 0) := by
  have hF_one : Filter.Tendsto (fun i => eLpNorm (F i) 1 ν) l (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF_two ?_ ?_
    · intro i
      exact bot_le
    · intro i
      exact eLpNorm_le_eLpNorm_of_exponent_le (μ := ν) (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (by norm_num) (hF_meas i)
  have hF_one_real : Filter.Tendsto (fun i => (eLpNorm (F i) 1 ν).toReal) l (nhds 0) := by
    exact (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hF_one
  have heq : ∀ᶠ i in l, ∫ y, |F i y| ∂ν = (eLpNorm (F i) 1 ν).toReal := by
    filter_upwards [hF_int] with i hi
    exact integral_abs_eq_eLpNorm_one_toReal hi
  exact hF_one_real.congr' <| heq.mono fun i hi => hi.symm

/-- **Pointwise derivative of `v ↦ v^r · log v` for `v > 0`.**
`(v^r · log v)' = v^{r-1} · (r · log v + 1)`. -/
lemma hasDerivAt_rpow_mul_log {r v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w : ℝ => w ^ r * Real.log w)
      (v ^ (r - 1) * (r * Real.log v + 1)) v := by
  have h1 : HasDerivAt (fun w : ℝ => w ^ r) (r * v ^ (r - 1)) v :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hv))
  have h2 : HasDerivAt Real.log v⁻¹ v := Real.hasDerivAt_log (ne_of_gt hv)
  have h3 := h1.mul h2
  convert h3 using 1
  -- Goal: v^(r-1)·(r·log v + 1) = r·v^(r-1)·log v + v^r·v⁻¹.
  have hvr : v ^ r * v⁻¹ = v ^ (r - 1) := by
    rw [← Real.rpow_neg_one v, ← Real.rpow_add hv, sub_eq_add_neg]
  rw [hvr]; ring

/-- **Uniform Lipschitz bound for `v ↦ v^r · log v`** on a compact positive
interval `[a, b]` (`0 < a`), uniform over the exponent `r ∈ [r₀, r₁]`. Used
in the `h_second` MVT step: the integrand `|u|^{q(τ)}·log|u|` is uniformly
Lipschitz in the orbit value `|u| ∈ [a, b]` over `τ` near `s` (where
`q(τ) ∈ [r₀, r₁]`), because strict positivity keeps both `v^{r-1}` and
`log v` bounded. -/
lemma exists_lipschitz_rpow_mul_log {a b r₀ r₁ : ℝ} (ha : 0 < a) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ r ∈ Set.Icc r₀ r₁, ∀ v ∈ Set.Icc a b, ∀ w ∈ Set.Icc a b,
      |w ^ r * Real.log w - v ^ r * Real.log v| ≤ L * |w - v| := by
  -- The v-derivative `D r v := v^{r-1}·(r·log v + 1)`, continuous on the
  -- compact box `[r₀,r₁]×[a,b]`, is bounded by some `L`.
  set D : ℝ × ℝ → ℝ := fun p => p.2 ^ (p.1 - 1) * (p.1 * Real.log p.2 + 1) with hD_def
  set box : Set (ℝ × ℝ) := Set.Icc r₀ r₁ ×ˢ Set.Icc a b with hbox_def
  have hsnd_pos : ∀ p ∈ box, (0:ℝ) < p.2 := by
    intro p hp; exact lt_of_lt_of_le ha (Set.mem_prod.mp hp).2.1
  have hD_cont : ContinuousOn D box := by
    refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.rpow continuousOn_snd
        (continuousOn_fst.sub continuousOn_const) ?_
      intro p hp; exact Or.inl (ne_of_gt (hsnd_pos p hp))
    · refine ContinuousOn.add (ContinuousOn.mul continuousOn_fst ?_) continuousOn_const
      refine Real.continuousOn_log.comp continuousOn_snd ?_
      intro p hp; exact ne_of_gt (hsnd_pos p hp)
  have hbox_cpt : IsCompact box := (isCompact_Icc).prod (isCompact_Icc)
  -- Bound |D| on box by L := sup |D| (0 if box empty).
  obtain ⟨L, hL_nn, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ box, |D p| ≤ L := by
    rcases box.eq_empty_or_nonempty with hempty | hne
    · exact ⟨0, le_refl 0, fun p hp => absurd hp (by rw [hempty]; exact id)⟩
    · obtain ⟨p₀, hp₀, hmax⟩ :=
        hbox_cpt.exists_isMaxOn hne (continuous_abs.comp_continuousOn hD_cont)
      exact ⟨|D p₀|, abs_nonneg _, fun p hp => hmax hp⟩
  refine ⟨L, hL_nn, ?_⟩
  intro r hr v hv w hw
  -- Apply MVT bound on [a,b] (convex) with derivative D r ·.
  have hbound : ∀ x ∈ Set.Icc a b, ‖D (r, x)‖ ≤ L := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact hL (r, x) (Set.mk_mem_prod hr hx)
  have hderiv : ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt (fun w : ℝ => w ^ r * Real.log w) (D (r, x)) (Set.Icc a b) x := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
    exact (hasDerivAt_rpow_mul_log hx_pos).hasDerivWithinAt
  have := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hv hw
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at this

/-- **Continuity of the frozen-orbit log-integral.** For a measurable `w` that
is bounded away from `0` and `∞` (`ε ≤ |w| ≤ M` a.e., `ε > 0`) on a finite
measure space, and a continuous exponent path `a`, the map
`τ ↦ ∫ |w|^{a τ} · log|w|` is continuous at every `τ₀`. This is the
continuity-at-`s` half of the `h_second` MVT step (DCT: the strict bounds
`ε ≤ |w| ≤ M` dominate the integrand by a constant). -/
lemma continuousAt_integral_rpow_mul_log {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν] {w : Y → ℝ}
    (hw : AEStronglyMeasurable w ν) {ε M : ℝ} (hε : 0 < ε)
    (hwε : ∀ᵐ y ∂ν, ε ≤ |w y|) (hwM : ∀ᵐ y ∂ν, |w y| ≤ M)
    {a : ℝ → ℝ} (ha : Continuous a) (ha_pos : ∀ τ, 0 < a τ) (τ₀ : ℝ) :
    ContinuousAt (fun τ => ∫ y, |w y| ^ a τ * Real.log |w y| ∂ν) τ₀ := by
  set logB : ℝ := max |Real.log ε| |Real.log M| with hlogB_def
  have hlogB_nn : 0 ≤ logB := le_trans (abs_nonneg _) (le_max_left _ _)
  set C : ℝ := Real.exp ((|a τ₀| + 1) * logB) * logB with hC_def
  -- Per-`y` continuity in `τ`.
  have h_cont : ∀ᵐ y ∂ν,
      ContinuousAt (fun τ => |w y| ^ a τ * Real.log |w y|) τ₀ := by
    filter_upwards [hwε] with y hy
    have hpos : 0 < |w y| := lt_of_lt_of_le hε hy
    have h1 : Continuous (fun τ => |w y| ^ a τ) :=
      (Real.continuous_const_rpow (ne_of_gt hpos)).comp ha
    exact (h1.mul continuous_const).continuousAt
  -- Domination by the constant `C`, eventually in `τ`.
  have h_bound : ∀ᶠ τ in nhds τ₀, ∀ᵐ y ∂ν,
      ‖|w y| ^ a τ * Real.log |w y|‖ ≤ C := by
    have ha_loc : ∀ᶠ τ in nhds τ₀, |a τ| ≤ |a τ₀| + 1 := by
      have : Filter.Tendsto (fun τ => |a τ|) (nhds τ₀) (nhds |a τ₀|) :=
        (ha.continuousAt).abs
      exact this.eventually_le_const (by linarith)
    filter_upwards [ha_loc] with τ haτ
    filter_upwards [hwε, hwM] with y hyε hyM
    set t : ℝ := |w y| with ht_def
    have hpos : 0 < t := lt_of_lt_of_le hε hyε
    -- |log t| ≤ logB.
    have hlog_le : |Real.log t| ≤ logB := by
      rcases le_or_gt 1 t with h1le | h1lt
      · have hub : Real.log t ≤ Real.log M := Real.log_le_log hpos hyM
        have hge : 0 ≤ Real.log t := Real.log_nonneg h1le
        rw [abs_of_nonneg hge]
        exact le_trans (le_trans hub (le_abs_self _)) (le_max_right _ _)
      · have hle0 : Real.log t ≤ 0 := Real.log_nonpos hpos.le h1lt.le
        have hge : Real.log ε ≤ Real.log t := Real.log_le_log hε hyε
        rw [abs_of_nonpos hle0]
        have hneg : -Real.log t ≤ -Real.log ε := by linarith
        exact le_trans (le_trans hneg (neg_le_abs _)) (le_max_left _ _)
    -- t^{a τ} ≤ exp((|a τ₀|+1)·logB).
    have hpow_le : t ^ a τ ≤ Real.exp ((|a τ₀| + 1) * logB) := by
      rw [Real.rpow_def_of_pos hpos]
      apply Real.exp_le_exp.mpr
      calc Real.log t * a τ ≤ |Real.log t * a τ| := le_abs_self _
        _ = |Real.log t| * |a τ| := abs_mul _ _
        _ ≤ logB * (|a τ₀| + 1) :=
            mul_le_mul hlog_le haτ (abs_nonneg _) hlogB_nn
        _ = (|a τ₀| + 1) * logB := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
    calc t ^ a τ * |Real.log t|
        ≤ Real.exp ((|a τ₀| + 1) * logB) * logB :=
          mul_le_mul hpow_le hlog_le (abs_nonneg _) (Real.exp_pos _).le
      _ = C := rfl
  -- Measurability.
  have hF_meas : ∀ᶠ τ in nhds τ₀,
      AEStronglyMeasurable (fun y => |w y| ^ a τ * Real.log |w y|) ν := by
    filter_upwards with τ
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (continuous_abs.rpow_const
        (fun _ => Or.inr (ha_pos τ).le)).comp_aestronglyMeasurable hw
    · exact (Real.measurable_log.comp_aemeasurable
        (continuous_abs.comp_aestronglyMeasurable hw).aemeasurable).aestronglyMeasurable
  exact continuousAt_of_dominated hF_meas h_bound (integrable_const C) h_cont

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

/-- **Vitali closure: L²-convergence `M_σ → ψ'(u_s)`** as `σ → s` along
`nhdsWithin s (Set.Ici 0)`. Combines `averagedDerivField_tendstoInMeasure`
(Step 3f), `uniformIntegrable_two_of_ae_bound` (UI), and the previous
lemma `psiDeriv_uS_memLp_two` (target `MemLp`) via Mathlib's
`tendsto_Lp_of_tendstoInMeasure` (Vitali).

The general filter is reduced to `atTop` sequences via
`Filter.tendsto_iff_seq_tendsto` (`nhdsWithin s (Set.Ici 0)` is
countably generated since ℝ is first-countable). For each sequence
`σ_seq → s`, the eventually-σ orbit bound is converted to a uniform-n
bound on the *shifted* sequence `σ_seq (· + N)`. Apply Vitali to the
shift; lift back via `Filter.tendsto_add_atTop_iff_nat`. `UnifTight`
is trivial on a finite measure (take the witness set `= univ`). -/
lemma averagedDerivField_tendsto_eLpNorm
    {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [IsFiniteMeasure ν]
    {u : ℝ → Lp ℝ 2 ν} {u' : Lp ℝ 2 ν} {s : ℝ}
    (hu : HasDerivWithinAt u u' (Set.Ici 0) s)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    {M K : ℝ} (hK_nn : 0 ≤ K)
    (hψ_bound : ∀ x ∈ Set.Icc (-M) M, |deriv ψ x| ≤ K)
    (h_u_bound : ∀ᶠ σ in nhdsWithin s (Set.Ici 0),
        ∀ᵐ y ∂ν, |(u σ : Y → ℝ) y| ≤ M)
    (h_u_s_bound : ∀ᵐ y ∂ν, |(u s : Y → ℝ) y| ≤ M) :
    Filter.Tendsto (fun σ =>
        eLpNorm (fun y => averagedDerivField u ψ σ s y -
          deriv ψ ((u s : Y → ℝ) y)) 2 ν)
      (nhdsWithin s (Set.Ici 0)) (nhds 0) := by
  set g : Y → ℝ := fun y => deriv ψ ((u s : Y → ℝ) y) with hg_def
  have hg_memLp : MemLp g 2 ν :=
    psiDeriv_uS_memLp_two hψ hψ_bound h_u_s_bound
  set Knn : NNReal := ⟨K, hK_nn⟩ with hKnn_def
  -- Reduce to atTop sequences.
  rw [Filter.tendsto_iff_seq_tendsto]
  intro σ_seq hσ_seq
  -- Extract N from the eventually-σ bound.
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp (hσ_seq.eventually h_u_bound)
  -- Shifted sequence τ_n := σ_seq (n + N). For each n, the orbit bound holds.
  have h_τ_bound : ∀ n, ∀ᵐ y ∂ν, |(u (σ_seq (n + N)) : Y → ℝ) y| ≤ M :=
    fun n => hN (n + N) (Nat.le_add_left N n)
  -- AEStronglyMeasurable of the shifted M_τ family.
  have hτ_meas : ∀ n, AEStronglyMeasurable
      (averagedDerivField u ψ (σ_seq (n + N)) s) ν :=
    fun n => averagedDerivField_aestronglyMeasurable u hψ _ s
  -- UniformIntegrable via the user's helper, with the a.e. bound `|M_τ_n y| ≤ K`.
  have hUI : UniformIntegrable
      (fun n => (averagedDerivField u ψ (σ_seq (n + N)) s : Y → ℝ)) 2 ν := by
    refine uniformIntegrable_two_of_ae_bound ν _ hτ_meas (K := Knn) ?_
    intro n
    filter_upwards [averagedDerivField_ae_bound (M := M) (K := K)
      hψ_bound (h_τ_bound n) h_u_s_bound] with y hy
    -- hy : |M_τ_n y| ≤ K. Want: ‖M_τ_n y‖₊ ≤ Knn.
    have hcoe : ((‖averagedDerivField u ψ (σ_seq (n + N)) s y‖₊ : NNReal) : ℝ)
        ≤ ((Knn : NNReal) : ℝ) := by
      show ‖averagedDerivField u ψ (σ_seq (n + N)) s y‖ ≤ K
      simpa [Real.norm_eq_abs] using hy
    exact_mod_cast hcoe
  -- UnifIntegrable + UnifTight from UI / finite measure.
  have hui_τ : UnifIntegrable
      (fun n => (averagedDerivField u ψ (σ_seq (n + N)) s : Y → ℝ)) 2 ν :=
    hUI.2.1
  have hut_τ : UnifTight
      (fun n => (averagedDerivField u ψ (σ_seq (n + N)) s : Y → ℝ)) 2 ν := by
    intro ε _
    refine ⟨Set.univ, measure_ne_top ν _, fun _ => ?_⟩
    simp
  -- TendstoInMeasure of the shifted family to g.
  have htim_τ : TendstoInMeasure ν
      (fun n => (averagedDerivField u ψ (σ_seq (n + N)) s : Y → ℝ))
      Filter.atTop g := by
    intro ε hε
    have hshift : Filter.Tendsto (fun n => σ_seq (n + N)) Filter.atTop
        (nhdsWithin s (Set.Ici 0)) :=
      hσ_seq.comp (Filter.tendsto_add_atTop_nat N)
    exact (averagedDerivField_tendstoInMeasure hu hψ h_u_bound h_u_s_bound ε hε).comp hshift
  -- Apply Vitali on the shifted sequence.
  have hvitali_τ : Filter.Tendsto (fun n =>
      eLpNorm ((averagedDerivField u ψ (σ_seq (n + N)) s) - g) 2 ν)
      Filter.atTop (nhds 0) :=
    MeasureTheory.tendsto_Lp_of_tendstoInMeasure (p := 2)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      hτ_meas hg_memLp hui_τ hut_τ htim_τ
  -- Lift back via shift invariance.
  exact (Filter.tendsto_add_atTop_iff_nat N).mp hvitali_τ

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

**Status: ✅ proved (axiom-free) — Bochner-Leibniz via the
`averagedDerivField` toolkit (factorization, AE-bound, AE-measurability,
MemLp 2, Vitali-driven `eLpNorm`→0). Discharge plan archived at
`plans/p2-strongL2-leibniz-discharge.md`. ~150 L body (9 steps);
9 toolkit lemmas in this file feed it. Mathlib-upstreamable. -/
theorem hasDerivWithinAt_integral_of_strongL2Deriv {Y : Type*}
    [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (u : ℝ → Lp ℝ 2 ν) (u' : Lp ℝ 2 ν) {s : ℝ} (hs : 0 ≤ s)
    (hu : HasDerivWithinAt u u' (Set.Ici 0) s)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    {M K : ℝ} (hK_nn : 0 ≤ K)
    (hψ_bound : ∀ x ∈ Set.Icc (-M) M, |deriv ψ x| ≤ K)
    (h_u_bound : ∀ᶠ σ in nhdsWithin s (Set.Ici 0),
        ∀ᵐ y ∂ν, |(u σ : Y → ℝ) y| ≤ M)
    (h_u_s_bound : ∀ᵐ y ∂ν, |(u s : Y → ℝ) y| ≤ M) :
    HasDerivWithinAt (fun σ => ∫ y, ψ ((u σ : Y → ℝ) y) ∂ν)
      (∫ y, deriv ψ ((u s : Y → ℝ) y) * (u' : Y → ℝ) y ∂ν)
      (Set.Ici 0) s := by
  classical
  -- 1. Target g := ψ' ∘ u_s; g_Lp := its Lp lift.
  set g : Y → ℝ := fun y => deriv ψ ((u s : Y → ℝ) y) with hg_def
  have hg_memLp : MemLp g 2 ν := psiDeriv_uS_memLp_two hψ hψ_bound h_u_s_bound
  set g_Lp : Lp ℝ 2 ν := hg_memLp.toLp g with hg_Lp_def
  -- 2. Padded M_σ_Lp : ℝ → Lp ℝ 2 ν (defaults to g_Lp when bound fails).
  let M_Lp : ℝ → Lp ℝ 2 ν := fun σ =>
    if h : ∀ᵐ y ∂ν, |(u σ : Y → ℝ) y| ≤ M then
      (averagedDerivField_memLp_two hψ hψ_bound h h_u_s_bound).toLp _
    else g_Lp
  -- 3. Vitali: eLpNorm (M_padded - g) → 0 along the filter.
  have hVitali := averagedDerivField_tendsto_eLpNorm hu hψ hK_nn hψ_bound
    h_u_bound h_u_s_bound
  have hM_eLpNorm_tendsto : Filter.Tendsto
      (fun σ => eLpNorm ((M_Lp σ : Y → ℝ) - g) 2 ν)
      (nhdsWithin s (Set.Ici 0)) (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hVitali
    filter_upwards [h_u_bound] with σ hσ
    simp only [M_Lp, dif_pos hσ]
    apply eLpNorm_congr_ae
    filter_upwards [(averagedDerivField_memLp_two
      hψ hψ_bound hσ h_u_s_bound).coeFn_toLp] with y hy
    simp only [Pi.sub_apply, hy, hg_def]
  -- 4. Convert eLpNorm tendsto to Lp tendsto.
  have hM_Lp_tendsto : Filter.Tendsto M_Lp (nhdsWithin s (Set.Ici 0)) (nhds g_Lp) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have : ∀ σ, dist (M_Lp σ) g_Lp = (eLpNorm ((M_Lp σ : Y → ℝ) - g) 2 ν).toReal := by
      intro σ
      rw [Lp.dist_def]
      congr 1
      apply eLpNorm_congr_ae
      filter_upwards [hg_memLp.coeFn_toLp] with y hy
      simp [hy, g_Lp]
    simp_rw [this]
    exact (ENNReal.tendsto_toReal (by simp)).comp hM_eLpNorm_tendsto
  -- 5. hu's slope form.
  have hu_slope : Filter.Tendsto (slope u s) (nhdsWithin s (Set.Ici 0 \ {s})) (nhds u') :=
    hasDerivWithinAt_iff_tendsto_slope.mp hu
  -- 6. Slope-filter is included in the nhdsWithin filter: 𝓝[Set.Ici 0 \ {s}] s ≤ 𝓝[Set.Ici 0] s.
  have hM_Lp_slopefilter : Filter.Tendsto M_Lp
      (nhdsWithin s (Set.Ici 0 \ {s})) (nhds g_Lp) :=
    hM_Lp_tendsto.mono_left (nhdsWithin_mono _ Set.diff_subset)
  -- 7. Filter.Tendsto.inner combines slope u s and M_Lp.
  have h_inner_tendsto : Filter.Tendsto
      (fun σ => @inner ℝ (Lp ℝ 2 ν) _ (slope u s σ) (M_Lp σ))
      (nhdsWithin s (Set.Ici 0 \ {s}))
      (nhds (@inner ℝ (Lp ℝ 2 ν) _ u' g_Lp)) :=
    hu_slope.inner hM_Lp_slopefilter
  -- 8. Identify the target F' with ⟪u', g_Lp⟫_ℝ via L2.inner_def + mul_comm.
  have hF'_eq : (∫ y, deriv ψ ((u s : Y → ℝ) y) * (u' : Y → ℝ) y ∂ν)
      = @inner ℝ (Lp ℝ 2 ν) _ u' g_Lp := by
    have step1 : (∫ y, deriv ψ ((u s : Y → ℝ) y) * (u' : Y → ℝ) y ∂ν)
        = ∫ y, (u' : Y → ℝ) y * g y ∂ν := by
      refine integral_congr_ae ?_
      filter_upwards with y
      show deriv ψ ((u s : Y → ℝ) y) * (u' : Y → ℝ) y
          = (u' : Y → ℝ) y * g y
      rw [hg_def]; ring
    rw [step1, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg_memLp.coeFn_toLp] with y hy
    show (u' : Y → ℝ) y * g y
        = @inner ℝ ℝ _ ((u' : Y → ℝ) y) ((g_Lp : Y → ℝ) y)
    rw [hy]
    show (u' : Y → ℝ) y * g y = g y * (u' : Y → ℝ) y
    ring
  rw [hF'_eq]
  -- 9. Apply slope characterization, identify slope F s σ with the inner product
  --    eventually-σ, conclude via h_inner_tendsto + Tendsto.congr'.
  rw [hasDerivWithinAt_iff_tendsto_slope]
  refine h_inner_tendsto.congr' ?_
  -- ψ continuous on the *compact* envelope [-(M⊔0), M⊔0]; bound there.
  have hψ_cts : Continuous ψ := hψ.continuous
  set M'' : ℝ := M ⊔ 0 with hM''
  have hM''_nn : (0 : ℝ) ≤ M'' := le_max_right _ _
  have hM_le_M'' : M ≤ M'' := le_max_left _ _
  have hIcc_ne : (Set.Icc (-M'') M'').Nonempty := ⟨0, ⟨by linarith, hM''_nn⟩⟩
  obtain ⟨x_max, _, hx_max_le⟩ :=
    isCompact_Icc.exists_isMaxOn (s := Set.Icc (-M'') M'') hIcc_ne
      (continuous_abs.comp hψ_cts).continuousOn
  set C : ℝ := |ψ x_max| with hC_def
  -- Eventually-σ: assemble (i) hσ ∈ Ici 0 \ {s}, (ii) hσ_bound : a.e. |u σ| ≤ M.
  have h_u_bd_diff : ∀ᶠ σ in nhdsWithin s (Set.Ici 0 \ {s}),
      ∀ᵐ y ∂ν, |(u σ : Y → ℝ) y| ≤ M :=
    h_u_bound.filter_mono (nhdsWithin_mono _ Set.diff_subset)
  filter_upwards [self_mem_nhdsWithin, h_u_bd_diff] with σ hσ_diff hσ_bound
  have hσ_ne : σ ≠ s := hσ_diff.2
  have hΔ_ne : σ - s ≠ 0 := sub_ne_zero.mpr hσ_ne
  -- Bound |ψ ∘ u σ| (resp. |ψ ∘ u s|) a.e. by C.
  have hψ_uσ_bd : ∀ᵐ y ∂ν, |ψ ((u σ : Y → ℝ) y)| ≤ C := by
    filter_upwards [hσ_bound] with y hy
    refine hx_max_le ?_
    exact Set.mem_Icc.mpr (abs_le.mp (le_trans hy hM_le_M''))
  have hψ_us_bd : ∀ᵐ y ∂ν, |ψ ((u s : Y → ℝ) y)| ≤ C := by
    filter_upwards [h_u_s_bound] with y hy
    refine hx_max_le ?_
    exact Set.mem_Icc.mpr (abs_le.mp (le_trans hy hM_le_M''))
  -- AEStronglyMeasurable + Integrable for both ψ ∘ u σ and ψ ∘ u s.
  have hψ_uσ_aesm : AEStronglyMeasurable (fun y => ψ ((u σ : Y → ℝ) y)) ν :=
    hψ_cts.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)
  have hψ_us_aesm : AEStronglyMeasurable (fun y => ψ ((u s : Y → ℝ) y)) ν :=
    hψ_cts.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)
  have hψ_uσ_int : Integrable (fun y => ψ ((u σ : Y → ℝ) y)) ν :=
    (MemLp.of_bound hψ_uσ_aesm C hψ_uσ_bd).integrable le_rfl
  have hψ_us_int : Integrable (fun y => ψ ((u s : Y → ℝ) y)) ν :=
    (MemLp.of_bound hψ_us_aesm C hψ_us_bd).integrable le_rfl
  -- M_Lp σ representative under hσ_bound.
  have hM_Lp_repr : (M_Lp σ : Y → ℝ) =ᵐ[ν] averagedDerivField u ψ σ s := by
    have hM_unfold : M_Lp σ
        = (averagedDerivField_memLp_two hψ hψ_bound hσ_bound h_u_s_bound).toLp
            (averagedDerivField u ψ σ s) := by
      change (if h : ∀ᵐ y ∂ν, |(u σ : Y → ℝ) y| ≤ M then
          (averagedDerivField_memLp_two hψ hψ_bound h h_u_s_bound).toLp _
        else g_Lp) = _
      rw [dif_pos hσ_bound]
    rw [hM_unfold]
    exact (averagedDerivField_memLp_two hψ hψ_bound hσ_bound h_u_s_bound).coeFn_toLp
  -- slope u s σ representative: =ᵐ (σ-s)⁻¹ * ((u σ) - (u s)).
  have hSlope_repr : (slope u s σ : Y → ℝ) =ᵐ[ν]
      fun y => (σ - s)⁻¹ * ((u σ : Y → ℝ) y - (u s : Y → ℝ) y) := by
    have hSlope_eq : slope u s σ = (σ - s)⁻¹ • (u σ - u s) := by
      rw [slope_def_module]
    rw [hSlope_eq]
    filter_upwards [Lp.coeFn_smul (σ - s)⁻¹ (u σ - u s), Lp.coeFn_sub (u σ) (u s)]
      with y h1 h2
    show ((σ - s)⁻¹ • (u σ - u s) : Lp ℝ 2 ν) y
        = (σ - s)⁻¹ * ((u σ : Y → ℝ) y - (u s : Y → ℝ) y)
    rw [h1]
    show (σ - s)⁻¹ • ((u σ - u s : Lp ℝ 2 ν) : Y → ℝ) y
        = (σ - s)⁻¹ * ((u σ : Y → ℝ) y - (u s : Y → ℝ) y)
    rw [h2]
    show (σ - s)⁻¹ • (((u σ : Y → ℝ)) y - ((u s : Y → ℝ)) y)
        = (σ - s)⁻¹ * ((u σ : Y → ℝ) y - (u s : Y → ℝ) y)
    exact smul_eq_mul _ _
  -- Now establish ⟪slope u s σ, M_Lp σ⟫_ℝ = slope F s σ.
  show @inner ℝ (Lp ℝ 2 ν) _ (slope u s σ) (M_Lp σ)
      = slope (fun σ => ∫ y, ψ ((u σ : Y → ℝ) y) ∂ν) s σ
  rw [slope_def_field, eq_div_iff hΔ_ne, ← integral_sub hψ_uσ_int hψ_us_int,
      MeasureTheory.L2.inner_def, ← integral_mul_const]
  refine integral_congr_ae ?_
  filter_upwards [hM_Lp_repr, hSlope_repr] with y hM_eq hS_eq
  -- Goal: ⟪(slope u s σ) y, (M_Lp σ) y⟫_ℝ * (σ - s) = ψ (u σ y) - ψ (u s y)
  show (@inner ℝ ℝ _ ((slope u s σ : Y → ℝ) y) ((M_Lp σ : Y → ℝ) y)) * (σ - s)
      = ψ ((u σ : Y → ℝ) y) - ψ ((u s : Y → ℝ) y)
  -- Real inner ⟪a, b⟫_ℝ = b * conj a = b * a (def-eq by RCLike.inner_apply rfl).
  show (M_Lp σ : Y → ℝ) y * (slope u s σ : Y → ℝ) y * (σ - s)
      = ψ ((u σ : Y → ℝ) y) - ψ ((u s : Y → ℝ) y)
  rw [hM_eq, hS_eq, psi_sub_eq_diff_mul_averagedDerivField u hψ σ s y]
  -- avgDF y * ((σ-s)⁻¹ * Δ) * (σ - s) = Δ * avgDF y    where Δ = u σ y - u s y
  field_simp

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

**Discovered structural requirements (2026-05-20, while attempting
the body):**

1. **L^∞ orbit bound (`h_orbit_bound`)**: `hasDerivWithinAt_integral_of_strongL2Deriv`
   needs `∀ᶠ σ in 𝓝[Ici 0] s, ∀ᵐ y ∂μ, |(P_σ f) y| ≤ M`. The abstract
   `MarkovSemigroup` has L²-contraction (operator norm ≤ 1) but no
   L^∞-contractivity. Markov-positive + conservation imply this, but
   it must be hypothesised or added as a structure field.
2. **Orbit L^q-integrability (`h_int`)**: same issue as `grossPow_pos`.
3. **Core-membership of `|u_s|^{q-1}`**: needed to apply `h_gen`'s
   form-pairing `⟪coreToL2 g, Af⟫ = -energy g f` with `g := |u_s|^{q-1}`.
4. **Measurability upgrade**: `hasDerivAt_integral_rpow_exponent` requires
   `Measurable w`; the orbit `(P_s f : X → ℝ)` is only AEStronglyMeasurable.
   Solvable by weakening the rpow lemma signature.

These are 4 structural assumptions (or design refactors) that go
beyond the current abstract `DirichletMarkovSemigroup` interface. The
discharge would either:
* Add hypotheses to the signature (4 more arguments to propagate
  through `grossLogNorm_hasDerivWithinAt`, `grossLogNorm_antitoneOn`,
  and the final hypercontractivity), or
* Strengthen `DirichletMarkovSemigroup`/`MarkovSemigroup` /`IsCore` /
  `CoreSemigroupInvariant` with the needed regularity fields.

**Status: documented `sorry` — analytic pieces (both `hasDerivAt_integral_rpow_exponent`
and `hasDerivWithinAt_integral_of_strongL2Deriv`) are now PROVED
axiom-free; the body composition needs the 4 structural pieces above
to invoke them. Effort to finish: substantial (decide which design
route, then ~200 L body + propagation). -/
theorem grossPow_hasDerivWithinAt
    (D : DirichletMarkovSemigroup X) (ρ p : ℝ) (hρ : 0 < ρ) (hp : 1 < p)
    (h_core : CoreSemigroupInvariant D)
    (h_gen : GeneratorCompat D)
    {f : X → ℝ} (hf : D.IsCore f) (hf_nonneg : ∀ x, 0 ≤ f x)
    -- Path A: strictly-positive hypothesis (Gemini-vetted 2026-05-20).
    -- Lets us avoid the regularity-at-zero issue with `u_s^{q-1}` for
    -- non-integer `q-1` — on `[ε, ∞)`, `x ↦ x^{q-1}` is C^∞.
    -- See `plans/gross-design-strictly-positive-escape.md` §4.
    (hf_pos : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ y ∂D.μ, ε ≤ f y)
    {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (grossPow D hf ρ p)
      (grossPowDeriv D hf ρ p s) (Set.Ici 0) s := by
  haveI : IsFiniteMeasure D.μ := inferInstance
  obtain ⟨ε, hε_pos, hf_ge_ε⟩ := hf_pos
  obtain ⟨Mf, hf_le_Mf⟩ := D.IsCore_memLp_top hf
  -- Lift bounds on f to bounds on (D.coreToL2 hf : X → ℝ).
  have hcoe_f : (D.coreToL2 hf : X → ℝ) =ᵐ[D.μ] f :=
    (D.IsCore_memLp hf).coeFn_toLp
  have hf_Lp_ge_ε : ∀ᵐ y ∂D.μ, ε ≤ (D.coreToL2 hf : X → ℝ) y := by
    filter_upwards [hcoe_f, hf_ge_ε] with y hcy hfy; rw [hcy]; exact hfy
  have hf_Lp_le_Mf : ∀ᵐ y ∂D.μ, |(D.coreToL2 hf : X → ℝ) y| ≤ Mf := by
    filter_upwards [hcoe_f, hf_le_Mf] with y hcy hfy; rw [hcy]; exact hfy
  -- Orbit lower/upper bounds at time s and (eventually-σ) near s.
  have hu_s_ge_ε : ∀ᵐ y ∂D.μ,
      ε ≤ ((D.P s (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y :=
    D.toMarkovSemigroup.orbit_lower_bound hs hf_Lp_ge_ε
  have hu_s_le_Mf : ∀ᵐ y ∂D.μ,
      |((D.P s (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y| ≤ Mf :=
    D.toMarkovSemigroup.Linfty_contraction hs hf_Lp_le_Mf
  have hu_σ_le_Mf : ∀ᶠ σ in nhdsWithin s (Set.Ici 0),
      ∀ᵐ y ∂D.μ,
        |((D.P σ (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y| ≤ Mf := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ_in
    exact D.toMarkovSemigroup.Linfty_contraction hσ_in hf_Lp_le_Mf
  -- Step ∂₂H: frozen orbit, varying exponent. Apply
  -- hasDerivAt_integral_rpow_exponent with w := orbit at s, a := grossExponent ρ p.
  set u_s_func : X → ℝ := ((D.P s (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ)
    with hu_s_func_def
  have hu_s_aesm : AEStronglyMeasurable u_s_func D.μ :=
    Lp.aestronglyMeasurable _
  have h_d2H : HasDerivAt
      (fun τ : ℝ => ∫ y, |u_s_func y| ^ grossExponent ρ p τ ∂D.μ)
      (2 * ρ * (grossExponent ρ p s - 1)
        * ∫ y, |u_s_func y| ^ grossExponent ρ p s * Real.log |u_s_func y| ∂D.μ) s :=
    hasDerivAt_integral_rpow_exponent D.μ hu_s_aesm hu_s_le_Mf
      (contDiff_grossExponent ρ p (n := 1)) (hasDerivAt_grossExponent ρ p s)
      (fun σ => grossExponent_pos hp ρ σ)
  -- The integral in h_d2H's derivative IS grossLogIntegral (def-eq).
  have h_d2H' : HasDerivAt
      (fun τ : ℝ => ∫ y, |u_s_func y| ^ grossExponent ρ p τ ∂D.μ)
      (2 * ρ * (grossExponent ρ p s - 1) * grossLogIntegral D hf ρ p s) s := by
    convert h_d2H using 1
  -- Step ∂₁H: varying orbit, frozen exponent. Use ψ := Real.rpow · q(s)
  -- (which is ContDiff ℝ 1 globally for q(s) ≥ 1; on the positive-orbit set,
  -- it equals |·|^{q(s)} a.e.).
  obtain ⟨Af, hAf_tendsto, hAf_pair⟩ := h_gen hf
  set q : ℝ := grossExponent ρ p s with hq_def
  have hq_pos : 0 < q := grossExponent_pos hp ρ s
  have hq_one_le : (1 : ℝ) ≤ q := (one_lt_grossExponent hp ρ s).le
  -- Orbit derivative at s.
  have hu_deriv : HasDerivWithinAt (fun σ : ℝ => D.P σ (D.coreToL2 hf))
      (D.P s Af) (Set.Ici 0) s :=
    D.toMarkovSemigroup.orbit_hasDerivWithinAt hAf_tendsto hs
  -- ψ := Real.rpow · q is ContDiff ℝ 1.
  have hψ_cd : ContDiff ℝ 1 (fun x : ℝ => x ^ q) := by
    have h := Real.contDiff_rpow_const_of_le (p := q) (n := 1)
      (by exact_mod_cast hq_one_le)
    exact h
  -- |deriv ψ x| = |q · x^{q-1}| ≤ q · max(Mf, 1)^{q-1} on [-Mf, Mf].
  -- Set the bound K := q * (max Mf 1) ^ (q - 1).
  set Mf' : ℝ := max Mf 1 with hMf'_def
  have hMf'_one : (1 : ℝ) ≤ Mf' := le_max_right _ _
  have hMf'_pos : 0 < Mf' := lt_of_lt_of_le one_pos hMf'_one
  set K : ℝ := q * Mf' ^ (q - 1) with hK_def
  have hK_nn : 0 ≤ K := by
    refine mul_nonneg hq_pos.le ?_
    exact Real.rpow_nonneg hMf'_pos.le _
  have hψ_bound : ∀ x ∈ Set.Icc (-Mf) Mf, |deriv (fun x : ℝ => x ^ q) x| ≤ K := by
    intro x hx
    -- deriv (fun x => x ^ q) = fun x => q * x^(q-1) via Real.deriv_rpow_const'.
    have hderiv : deriv (fun x : ℝ => x ^ q) x = q * x ^ (q - 1) := by
      have h := Real.deriv_rpow_const' (p := q)
      exact congrFun h x
    rw [hderiv, abs_mul, abs_of_pos hq_pos]
    refine mul_le_mul_of_nonneg_left ?_ hq_pos.le
    -- |x^(q-1)| ≤ |x|^(q-1) ≤ Mf'^(q-1).
    calc |x ^ (q - 1)| ≤ |x| ^ (q - 1) := Real.abs_rpow_le_abs_rpow x (q - 1)
      _ ≤ Mf' ^ (q - 1) := by
          refine Real.rpow_le_rpow (abs_nonneg _) ?_ (by linarith)
          calc |x| ≤ Mf := abs_le.mpr ⟨hx.1, hx.2⟩
            _ ≤ Mf' := le_max_left _ _
  -- Apply hasDerivWithinAt_integral_of_strongL2Deriv.
  have h_d1H_raw := hasDerivWithinAt_integral_of_strongL2Deriv (Y := X) D.μ
    (fun σ => D.P σ (D.coreToL2 hf)) (D.P s Af) hs hu_deriv
    (fun x : ℝ => x ^ q) hψ_cd hK_nn hψ_bound hu_σ_le_Mf hu_s_le_Mf
  -- h_d1H_raw : HasDerivWithinAt (fun σ => ∫ y, (u σ y)^q ∂ν)
  --             (∫ y, deriv (fun x => x^q) (u_s y) * (u' y)) (Ici 0) s
  -- Bridge (u σ y)^q ↔ |u σ y|^q a.e. (orbit nonneg for σ ≥ 0).
  have h_coreToL2_nn : (0 : Lp ℝ 2 D.μ) ≤ D.coreToL2 hf := by
    rw [← Lp.coeFn_nonneg]
    filter_upwards [hf_Lp_ge_ε] with y hy
    simp only [Pi.zero_apply]; linarith
  have h_orbit_nn : ∀ σ : ℝ, 0 ≤ σ → ∀ᵐ y ∂D.μ,
      0 ≤ ((D.P σ (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y :=
    fun σ hσ => (Lp.coeFn_nonneg _).mpr (D.P_positivity σ hσ _ h_coreToL2_nn)
  have h_integrand_eq : ∀ σ ∈ Set.Ici (0:ℝ),
      (∫ y, |((D.P σ (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y| ^ q ∂D.μ)
        = ∫ y, ((D.P σ (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y ^ q ∂D.μ := by
    intro σ hσ
    refine integral_congr_ae ?_
    filter_upwards [h_orbit_nn σ hσ] with y hy
    rw [abs_of_nonneg hy]
  have h_d1H : HasDerivWithinAt
      (fun σ => ∫ y, |((D.P σ (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y| ^ q ∂D.μ)
      (∫ y, deriv (fun x : ℝ => x ^ q) (u_s_func y) * (D.P s Af : X → ℝ) y ∂D.μ)
      (Set.Ici 0) s :=
    h_d1H_raw.congr (fun σ hσ => h_integrand_eq σ hσ) (h_integrand_eq s hs)
  -- ===== Chain rule: F'(s) = ∂₁H + ∂₂H (Gemini-vetted architecture) =====
  -- Abbreviations.
  set D1 : ℝ := ∫ y, deriv (fun x : ℝ => x ^ q) (u_s_func y)
      * (D.P s Af : X → ℝ) y ∂D.μ with hD1_def
  set D2 : ℝ := 2 * ρ * (grossExponent ρ p s - 1) * grossLogIntegral D hf ρ p s
    with hD2_def
  -- Two-variable function H(σ, τ) := ∫ |u_σ|^{q(τ)}; F(σ) = grossPow = H(σ, σ).
  set Hfun : ℝ → ℝ → ℝ := fun σ τ =>
    ∫ y, |((D.P σ (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y| ^ grossExponent ρ p τ ∂D.μ
    with hHfun_def
  -- The τ-derivative integrand g σ τ.
  set gfun : ℝ → ℝ → ℝ := fun σ τ =>
    2 * ρ * (grossExponent ρ p τ - 1)
      * ∫ y, |((D.P σ (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y| ^ grossExponent ρ p τ
          * Real.log |((D.P σ (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y| ∂D.μ
    with hgfun_def
  -- The goal `grossPow D hf ρ p` is `fun σ => Hfun σ σ` by def; the value
  -- grossPowDeriv equals D1 + D2 (the second equality via the energy
  -- identification, deferred). Reduce to the chain rule + energy identity.
  -- Chain rule target: HasDerivWithinAt (fun σ => Hfun σ σ) (D1 + D2) (Ici 0) s.
  have h_chain : HasDerivWithinAt (fun σ => Hfun σ σ) (D1 + D2) (Set.Ici 0) s := by
    rw [hasDerivWithinAt_iff_tendsto_slope]
    -- Split: slope (diag) = slope (Hfun · s) + (Hfun σ σ - Hfun σ s)/(σ - s).
    -- First term → D1 (h_d1H); second → D2 via MVT-in-τ + uniform Lipschitz.
    have h_first : Filter.Tendsto (fun σ => slope (fun σ' => Hfun σ' s) s σ)
        (nhdsWithin s (Set.Ici 0 \ {s})) (nhds D1) := by
      have h := hasDerivWithinAt_iff_tendsto_slope.mp h_d1H
      -- h_d1H's function is `fun σ => ∫|u_σ|^q`, and `Hfun σ' s = ∫|u_{σ'}|^{q(s)}`;
      -- `q = grossExponent ρ p s`, so they agree.
      exact h
    have h_second : Filter.Tendsto
        (fun σ => (Hfun σ σ - Hfun σ s) / (σ - s))
        (nhdsWithin s (Set.Ici 0 \ {s})) (nhds D2) := by
      sorry
    -- Combine.
    have h_sum := h_first.add h_second
    refine h_sum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ_in
    obtain ⟨_, hσ_ne⟩ := hσ_in
    rw [Set.mem_singleton_iff] at hσ_ne
    -- slope (diag) σ = slope (Hfun · s) σ + (Hfun σ σ - Hfun σ s)/(σ-s).
    show slope (fun σ' => Hfun σ' s) s σ + (Hfun σ σ - Hfun σ s) / (σ - s)
        = slope (fun σ => Hfun σ σ) s σ
    rw [slope_def_field, slope_def_field]
    have hne : σ - s ≠ 0 := sub_ne_zero.mpr hσ_ne
    field_simp
    ring
  -- Energy identification: D1 = -q · D.energy(u_s, u_s^{q-1}), hence
  -- D1 + D2 = grossPowDeriv.
  have h_energy : D1 + D2 = grossPowDeriv D hf ρ p s := by
    sorry
  rw [← h_energy]
  -- grossPow D hf ρ p = fun σ => Hfun σ σ (def-eq).
  exact h_chain

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
    (hf_ne : ¬ f =ᵐ[D.μ] 0)
    (hf_pos : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ y ∂D.μ, ε ≤ f y)
    {s : ℝ} (hs : 0 ≤ s)
    (h_int : Integrable (fun x => |((D.P s (D.coreToL2 hf) : X → ℝ) x)|
                          ^ grossExponent ρ p s) D.μ) :
    HasDerivWithinAt (grossLogNorm D hf ρ p)
      (grossLogNormDeriv D hf ρ p s) (Set.Ici 0) s := by
  set q := grossExponent ρ p s with hq_def
  have hqpos : 0 < q := grossExponent_pos hp ρ s
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hFpos : 0 < grossPow D hf ρ p s :=
    grossPow_pos D ρ p hρ hp hf hf_nonneg hf_ne hs h_int
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
    grossPow_hasDerivWithinAt D ρ p hρ hp h_core h_gen hf hf_nonneg hf_pos hs
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
    (hf_ne : ¬ f =ᵐ[D.μ] 0)
    (hf_pos : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ y ∂D.μ, ε ≤ f y)
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
    {f : X → ℝ} (hf : D.IsCore f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_ne : ¬ f =ᵐ[D.μ] 0)
    (hf_pos : ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ y ∂D.μ, ε ≤ f y)
    (h_int : ∀ s ∈ Set.Ici (0 : ℝ),
        Integrable (fun x => |((D.P s (D.coreToL2 hf) : X → ℝ) x)|
                              ^ grossExponent ρ p s) D.μ) :
    AntitoneOn (grossLogNorm D hf ρ p) (Set.Ici 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (f' := grossLogNormDeriv D hf ρ p) ?_ ?_ ?_
  · -- continuity on `[0,∞)`: each point has a within-derivative (P2),
    -- so `Λ` is continuous there.
    intro x hx
    exact (grossLogNorm_hasDerivWithinAt D ρ p hρ hp h_core h_gen hf hf_nonneg
      hf_ne hf_pos hx (h_int x hx)).continuousWithinAt
  · intro x hx
    have hx0 : 0 ≤ x := le_of_lt (by simpa using hx)
    -- `interior (Ici 0) = Ioi 0`; restrict the P2 within-derivative.
    exact (grossLogNorm_hasDerivWithinAt D ρ p hρ hp h_core h_gen hf
      hf_nonneg hf_ne hf_pos hx0 (h_int x hx0)).mono interior_subset
  · intro x hx
    exact grossLogNorm_deriv_nonpos D ρ p hρ hp h_lsi h_sv hf hf_nonneg hf_ne hf_pos
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
