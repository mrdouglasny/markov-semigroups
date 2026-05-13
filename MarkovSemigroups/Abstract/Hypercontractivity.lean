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
  space (semigroup laws restricted to `t ≥ 0`; conservation of `1`;
  positivity preservation; symmetry; `L²` contraction stated via
  `eLpNorm`).
- `DirichletMarkovSemigroup` — bundles a `MarkovSemigroup` with the
  semigroup's canonical Dirichlet form (the user supplies the form
  data plus the right-derivative-at-zero compatibility).
- `MarkovSemigroup.IsHypercontractive` — `‖P_t f‖_{L^q} ≤ ‖f‖_{L^p}`
  when `q ≤ 1 + (p − 1) e^{2ρt}`, stated via `eLpNorm` to avoid the
  Bochner junk-value trap on non-`L^p` functions.

## Main results (postulated as textbook axioms)

- `gross_lsi_implies_hypercontractive` — LSI for the form ⇒
  hypercontractivity of the bundled semigroup.
- `gross_hypercontractive_implies_lsi` — converse.
- `gross_equivalence` — LSI ⇔ hypercontractivity.

## Why bundle?

The form-vs-semigroup link `E(f, g) = -(d/dt)|_{t=0+} ⟨f, P_t g⟩` is
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
import Mathlib.MeasureTheory.Function.LpSpace.Basic

open MeasureTheory ENNReal Set

noncomputable section

/-- A *symmetric Markov semigroup* on a probability space `(X, μ)`.

This is the standard setup for Gross's LSI/HC equivalence: a strongly
continuous *symmetric* contraction semigroup on `L²(μ)` preserving
positivity and the constant function `1`.

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
  /-- The semigroup operator at time `t`. -/
  P : ℝ → (X → ℝ) → (X → ℝ)
  /-- `P_0 = id`. -/
  P_zero : ∀ f, P 0 f = f
  /-- Semigroup property (for `s, t ≥ 0`). -/
  P_semigroup : ∀ s t f, 0 ≤ s → 0 ≤ t → P (s + t) f = P s (P t f)
  /-- Conservation of the constant function `1` (for `t ≥ 0`). -/
  P_conservation : ∀ t, 0 ≤ t → P t (fun _ => 1) = fun _ => 1
  /-- Positivity preservation: `f ≥ 0 ⇒ P_t f ≥ 0` (for `t ≥ 0`). -/
  P_positivity : ∀ t, 0 ≤ t → ∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ P t f x
  /-- Symmetry of `P_t` on `L²(μ)` (for `t ≥ 0`). -/
  P_symmetric : ∀ t, 0 ≤ t → ∀ f g,
    ∫ x, f x * P t g x ∂μ = ∫ x, P t f x * g x ∂μ
  /-- `L²` contraction. Stated via `eLpNorm` (which returns `⊤` for
  non-`L²` functions) to avoid the Bochner junk-value trap. -/
  P_l2_contraction : ∀ t, 0 ≤ t → ∀ f, MemLp f 2 μ →
    eLpNorm (P t f) 2 μ ≤ eLpNorm f 2 μ

attribute [instance] MarkovSemigroup.hμ

namespace MarkovSemigroup

variable {X : Type*} [MeasurableSpace X]

/-- A symmetric Markov semigroup is *hypercontractive* with rate `ρ > 0`
if `P_t : L^p → L^q` is a contraction whenever
`q ≤ 1 + (p − 1) · e^{2ρt}`:

  `‖P_t f‖_{L^q(μ)} ≤ ‖f‖_{L^p(μ)}`.

Stated via `eLpNorm` to remain meaningful for general (possibly
non-`L^p`) functions: if `f ∉ L^p` then `eLpNorm f p μ = ⊤`, and the
inequality holds trivially. -/
def IsHypercontractive (S : MarkovSemigroup X) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ (p q : ℝ) (t : ℝ),
    1 < p → p ≤ q → 0 < t →
    q ≤ 1 + (p - 1) * Real.exp (2 * ρ * t) →
    ∀ f : X → ℝ,
      eLpNorm (S.P t f) (ENNReal.ofReal q) S.μ ≤
      eLpNorm f (ENNReal.ofReal p) S.μ

end MarkovSemigroup

/-- A *Dirichlet-Markov semigroup*: a symmetric Markov semigroup
bundled with its canonical Dirichlet form.

For a symmetric Markov semigroup the Dirichlet form is uniquely
determined by the semigroup as

  `E(f, g) = lim_{t↘0} (1/t) · ⟨f, (I − P_t) g⟩
          = -(d/dt)|_{t=0+} ⟨f, P_t g⟩`

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
  /-- Energy is nonneg on the diagonal. -/
  energy_nonneg : ∀ f, 0 ≤ energy f f
  /-- Admissible "core" functions (the algebra A₀ in BGL §1.4.2). -/
  IsCore : (X → ℝ) → Prop
  /-- Constants are core. -/
  IsCore_const : ∀ c : ℝ, IsCore (fun _ => c)
  /-- Core is closed under addition. -/
  IsCore_add : ∀ {f g}, IsCore f → IsCore g → IsCore (f + g)
  /-- Core is closed under scalar multiplication. -/
  IsCore_smul : ∀ (c : ℝ) {f}, IsCore f → IsCore (c • f)
  /-- Energy is bilinear (left). -/
  energy_add_left : ∀ f₁ f₂ g, IsCore f₁ → IsCore f₂ → IsCore g →
    energy (f₁ + f₂) g = energy f₁ g + energy f₂ g
  /-- Energy is bilinear (scalar left). -/
  energy_smul_left : ∀ (c : ℝ) f g, IsCore f → IsCore g →
    energy (c • f) g = c * energy f g
  /-- Constants have zero energy (Markov property consequence). -/
  energy_const : ∀ c : ℝ, energy (fun _ => c) (fun _ => c) = 0
  /-- **Generator–Dirichlet-form compatibility.** The energy form is
  the (negated) right-derivative-at-zero of the bilinear pairing
  `⟨f, P_t g⟩`. This is the canonical-form identification:
    `E(f, g) = -(d/dt)|_{t=0+} ∫ f · P_t g dμ`.
  The right-derivative (`Set.Ici 0`) is essential: a two-sided
  derivative would force `P_t` to extend to a group of isometries
  (Stone's theorem), collapsing the structure. -/
  energy_eq_deriv : ∀ f g, IsCore f → IsCore g →
    HasDerivWithinAt (fun t : ℝ => ∫ x, f x * P t g x ∂μ)
      (-energy f g) (Set.Ici 0) 0

namespace DirichletMarkovSemigroup

variable {X : Type*} [MeasurableSpace X]

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
of the underlying Markov semigroup. -/
def IsHypercontractive (D : DirichletMarkovSemigroup X) (ρ : ℝ) : Prop :=
  D.toMarkovSemigroup.IsHypercontractive ρ

end DirichletMarkovSemigroup

/-! ## Stroock–Varopoulos inequality (intermediate-step lemma) -/

/-- **Stroock–Varopoulos inequality.** AXIOM
(vetting-required textbook bridge).

For a `DirichletMarkovSemigroup` `D`, any nonnegative `f ∈ D.IsCore`,
any `p ≥ 2`, and assuming `f^{p/2}` and `f^{p-1}` lie in the core:

  `(4(p − 1) / p²) · E(f^{p/2}, f^{p/2}) ≤ E(f, f^{p−1})`.

In operator form (using `E(f, g) = -⟨f, Lg⟩`):
  `-⟨f^{p−1}, Lf⟩ ≥ (4(p − 1) / p²) · ⟨-L(f^{p/2}), f^{p/2}⟩`.

This is the key intermediate-step lemma in Gross's proof that LSI
implies hypercontractivity. Combined with LSI applied to `f^{p/2}`
(and the chain rule for `(d/dt) ‖P_t f‖_p^p`), it closes the
differential inequality `(d/dt) ‖P_t f‖_{q(t)} ≤ 0` along the path
`q(t) = 1 + (p − 1) · e^{2ρt}`.

## On the hypotheses

* For `p ≥ 2`, both `x ↦ x^{p/2}` and `x ↦ x^{p−1}` are `C¹` on
  `[0, ∞)`, so `f ≥ 0` (no uniform `ε`-bound needed) suffices to
  make the powers smooth. Using `f ≥ 0` rather than `f ≥ ε > 0`
  avoids vacuous-hypothesis pitfalls on infinite-measure spaces
  where `L²(μ)` excludes uniformly-positive functions.
* `IsCore` closure under the power maps `t ↦ t^q` is not built into
  `DirichletMarkovSemigroup` (concrete instances typically have the
  core closed under smooth compositions; we don't enforce that
  abstractly). So we add `D.IsCore (f^{p/2})` and `D.IsCore (f^{p−1})`
  as explicit hypotheses of the axiom.
* The inequality holds for **all** symmetric Markov semigroups, not
  just diffusions. Diffusions give equality at `p = 2`; the bound
  as stated is general.

## Discharge plan (sketch)

Standard textbook proof avoids the generator entirely. Build the
inequality from the pointwise algebraic fact
  `(a − b)(a^{p−1} − b^{p−1}) ≥ (4(p − 1)/p²) · (a^{p/2} − b^{p/2})²`
for `a, b ≥ 0` (elementary calculus, real-variable convexity), then
integrate against the symmetric Markov kernel
`k_t(x, dy) dμ(x)` representing `⟨g, h − P_t h⟩` for any pair
`(g, h)`, and finally divide by `t` and take `t ↘ 0` using
`energy_eq_deriv`.

Moderate-to-high Lean effort: the integral-kernel representation of
`⟨g, h − P_t h⟩` may need to be assumed (or proved separately if
the structure carries an explicit Markov kernel; currently
`DirichletMarkovSemigroup` carries `P_t` as a bare operator).

## References

* Stroock, *Logarithmic Sobolev inequalities for Gibbs states*, in
  *Dirichlet Forms (Varenna 1992)*, Lecture Notes in Math. 1563.
* Varopoulos, "Hardy-Littlewood theory for semigroups," J. Funct.
  Anal. 63 (1985).
* Bakry-Gentil-Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, §1.7 / Proposition 1.7.1.

## Vetting status

**Standard** (gemini-3.1-pro-preview, two-pass vetting 2026-05-13):
* First pass: "Needs Revision" — original draft required
  `f ≥ ε > 0`, flagged as potentially vacuous on infinite-measure
  spaces (no `L²` function is uniformly bounded below). Revision:
  for `p ≥ 2` the powers `x ↦ x^{p/2}` and `x ↦ x^{p−1}` are `C¹`
  on `[0, ∞)` (since `p/2, p−1 ≥ 1`), so `f ≥ 0` suffices.
* Second pass: "Standard" — revised version confirmed correct.
  Lean's `0 ^ q = 0` for `q ≥ 1` handles `f(x) = 0` cleanly.
  Edge cases: `p = 2` gives equality `E(f, f) ≤ E(f, f)`; `f ≡ 0`
  gives `0 ≤ 0`. Constant `4(p − 1) / p²` and direction `≤`
  confirmed. Inequality holds at general symmetric-Markov level
  (no diffusion property needed). -/
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
hypercontractivity.

The proof uses the semigroup interpolation method: differentiate
`‖P_t f‖_{L^{q(t)}}` along `q(t) = 1 + (p − 1) e^{2ρt}` and show the
derivative is `≤ 0` via the LSI applied to `|f|^{q/2}`. The integral
key step uses the bilinear form `E(f, g) = -(d/dt)|_{t=0+} ⟨f, P_t g⟩`
via the Stroock–Varopoulos inequality. -/
axiom gross_lsi_implies_hypercontractive {X : Type*} [MeasurableSpace X]
    (D : DirichletMarkovSemigroup X) (ρ : ℝ)
    (h_lsi : D.SatisfiesLogSobolev ρ) : D.IsHypercontractive ρ

/-- **Postulated (Gross 1975, Theorem 2).** Hypercontractivity implies
LSI.

The proof differentiates the hypercontractive bound at `t = 0` with
`p = 2`, `q = 2 + ε`, and takes `ε → 0`. -/
axiom gross_hypercontractive_implies_lsi {X : Type*} [MeasurableSpace X]
    (D : DirichletMarkovSemigroup X) (ρ : ℝ)
    (h_hyp : D.IsHypercontractive ρ) : D.SatisfiesLogSobolev ρ

namespace DirichletMarkovSemigroup

variable {X : Type*} [MeasurableSpace X]

/-- Gross's theorem (forward direction): LSI ⇒ hypercontractivity.

This is Gross (1975), Theorem 1, packaged for the bundled structure. -/
theorem hypercontractive_of_logSobolev (D : DirichletMarkovSemigroup X)
    (ρ : ℝ) (h_lsi : D.SatisfiesLogSobolev ρ) :
    D.IsHypercontractive ρ :=
  gross_lsi_implies_hypercontractive D ρ h_lsi

/-- Gross's theorem (reverse direction): hypercontractivity ⇒ LSI.

Gross (1975), Theorem 2. -/
theorem logSobolev_of_hypercontractive (D : DirichletMarkovSemigroup X)
    (ρ : ℝ) (h_hyp : D.IsHypercontractive ρ) :
    D.SatisfiesLogSobolev ρ :=
  gross_hypercontractive_implies_lsi D ρ h_hyp

/-- The Gross equivalence: LSI ↔ hypercontractivity for a
`DirichletMarkovSemigroup`. -/
theorem gross_equivalence (D : DirichletMarkovSemigroup X) (ρ : ℝ) :
    D.SatisfiesLogSobolev ρ ↔ D.IsHypercontractive ρ :=
  ⟨D.hypercontractive_of_logSobolev ρ,
   D.logSobolev_of_hypercontractive ρ⟩

/-! ## Direct consequence: the semigroup improves integrability -/

/-- Direct application of hypercontractivity to any function `f`:

  `‖P_t f‖_{L^q(μ)} ≤ ‖f‖_{L^p(μ)}`

whenever `q ≤ 1 + (p − 1) e^{2ρt}`. -/
theorem semigroup_lp_improvement (D : DirichletMarkovSemigroup X)
    (ρ : ℝ) (h_hyp : D.IsHypercontractive ρ)
    (f : X → ℝ)
    (p q : ℝ) (hp : 1 < p) (hpq : p ≤ q)
    (t : ℝ) (ht : 0 < t)
    (h_bound : q ≤ 1 + (p - 1) * Real.exp (2 * ρ * t)) :
    eLpNorm (D.P t f) (ENNReal.ofReal q) D.μ ≤
    eLpNorm f (ENNReal.ofReal p) D.μ :=
  h_hyp.2 p q t hp hpq ht h_bound f

end DirichletMarkovSemigroup

end
