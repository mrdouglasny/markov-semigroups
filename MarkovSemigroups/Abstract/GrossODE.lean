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

/-- **P2 core — the differentiation-under-the-integral.**
`grossPow` has right derivative `grossPowDeriv` on `[0,∞)`. This is
the genuine analytic bottleneck (`plans/gross-discharge.md` P2,
~700–1300 L): differentiate `s ↦ ∫ |P_s f|^{q(s)}` jointly in the
exponent path and the semigroup, using

* `h_core` ⇒ `P_s f ∈ core` so the integrand is regular;
* `h_gen` (`GeneratorCompat`) for the strong-`L²` right derivative
  `∂_s (P_s f) = A(P_s f)` and the form pairing
  `∫ u^{q-1} A u = −E(u, u^{q-1})`;
* dominated convergence (core `L^∞` bounds) to pass the right
  difference quotient inside the integral;
* the pointwise `∂_s |·|^{q(s)} = |·|^{q} log|·| · q'` for the
  exponent-path term.

**Status: documented `sorry` — the bottleneck.** -/
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
