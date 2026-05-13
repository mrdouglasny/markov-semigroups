/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Atomic textbook axioms for the OU entropy decay bound

This file packages **two atomic textbook bridges** for the Gaussian
Ornstein-Uhlenbeck semigroup on `ℝ`:

* `ouSemigroup_fisher_info_decay` — Bakry-Émery gradient decay for the
  Fisher information (BGL Prop 5.5.2, Jensen-on-`x²/y` argument).
* `hasDerivAt_entropy_ouSemigroup` — de Bruijn identity: the entropy
  `∫ g · log g dγ` differentiated under the OU heat flow equals minus
  the Fisher information (BGL §5.5).

Together these two facts (plus FTC and a one-line algebraic identity)
discharge the previous broad axiom `ouSemigroup_entropy_sq_decay_bound`
(BGL Theorem 5.5.2). The discharge lives in
`Instances/WorkInProgress/EuclideanEntropyDecay.lean`.

Both axioms require a positive lower bound `g ≥ ε > 0` on the function;
this is the standard regularization handling `log 0` in the textbook
proof. The application to `f²` proceeds via `g := f² + ε` plus a limit
`ε → 0`.

## Why split into two axioms?

The original axiom bundled "rate identity" + "gradient decay" + "FTC"
into a single statement. Splitting yields:
1. Each piece is a standalone textbook fact, vettable independently.
2. The Fisher info decay (A1) closely parallels `ouSemigroup_gradient_decay`
   which we proved — same Jensen + γ-invariance structure, just with
   `(g')²/g` instead of `(g')²`.
3. The de Bruijn identity (A2) is parametric-integral differentiation
   structurally identical to `hasDerivAt_l2sq_ouSemigroup_pos` which
   we proved — but applied to the `s · log s` integrand instead of
   `s²`.
4. Both axioms are reusable for future `BakryEmerySpace` instances.

## References

* Bakry-Gentil-Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, §5.5 (de Bruijn identity, Fisher information decay,
  entropy decay under Bakry-Émery curvature).
* Bakry-Émery (1985) "Diffusions hypercontractives", §I.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MarkovSemigroups.Instances.WorkInProgress.Euclidean

open MeasureTheory Filter Set Real ProbabilityTheory Topology

open scoped ContDiff

noncomputable section

namespace Gaussian1D

/-- The Fisher information of `g : ℝ → ℝ` against the standard Gaussian:
`I(g) = ∫ (g'(y))² / g(y) dγ(y)`.

For our purposes `g` is bounded below by some `ε > 0`, so the division
is well-defined everywhere. -/
def fisherInfo (g : ℝ → ℝ) : ℝ :=
  ∫ y, (deriv g y) ^ 2 / g y ∂γ

/-- The Boltzmann-style entropy `H(g) = ∫ g · log g dγ` (no `(∫g) log(∫g)`
subtraction at this granularity — the centered version is in
`DirichletSpace.entropy`). For `g ≥ ε > 0`, this is a smooth functional. -/
def boltzmannEntropy (g : ℝ → ℝ) : ℝ :=
  ∫ y, g y * Real.log (g y) ∂γ

/-! ## A1: Fisher information gradient decay (BGL Prop 5.5.2) -/

/-- **Bakry-Émery gradient decay for the Fisher information.** AXIOM
(vetting-required textbook bridge).

For any `C¹` `g : ℝ → ℝ` with `g, g'` bounded and `g ≥ ε > 0` pointwise,
the Fisher information `I(P_t g)` decays exponentially:

  `I(P_t g) = ∫ ((P_t g)'(y))² / (P_t g)(y) dγ(y)
              ≤ exp(-2t) · ∫ (g'(y))² / g(y) dγ(y) = exp(-2t) · I(g)`.

## Proof in textbooks

Two steps:
1. The Mehler derivative formula gives `(P_t g)'(x) = e^{-t} P_t(g')(x)`
   (already proved as `hasDerivAt_ouSemigroup_C1`).
2. Apply Jensen's inequality to the convex function `φ(x, y) = x² / y`
   on `{y > 0}`:
   `((P_t g)'(x))² / (P_t g)(x) = (e^{-t} P_t(g'))² / P_t(g)
       = e^{-2t} · (P_t(g'))² / (P_t g)
       ≤ e^{-2t} · P_t((g')²/g)`
   by Jensen on the Mehler probability kernel.
3. Integrate against γ and use γ-invariance of P_t (Fubini +
   `ou_kernel_map`):
   `∫ ((P_t g)')² / P_t g dγ ≤ e^{-2t} · ∫ P_t((g')²/g) dγ
       = e^{-2t} · ∫ (g')²/g dγ`.

The Jensen step is the Bakry-Émery curvature condition `Γ₂ ≥ Γ` in
disguise (for OU on ℝ with `ρ = 1`, this curvature bound is exact).

## Discharge plan

Per Gemini 3.1-pro vetting (verdict: **Standard**, 2026-05-12): the
cleanest discharge avoids the 2D-Jensen-on-`x²/y` argument. Instead,
apply Cauchy-Schwarz on the Mehler probability kernel
`μ_x(dy) := P_t(x, dy)`:
  `(P_t g'(x))² = (∫ (g'/√g) · √g dμ_x)²
       ≤ (∫ (g')²/g dμ_x) · (∫ g dμ_x)`
giving `(P_t g'(x))² / P_t g(x) ≤ P_t((g')²/g)(x)`. Then `P_t g'(x) =
e^t · (P_t g)'(x)`... wait — by `hasDerivAt_ouSemigroup_C1`,
`(P_t g)'(x) = e^{-t} · P_t g'(x)`. So
`((P_t g)'(x))² / (P_t g)(x) = e^{-2t} (P_t g')² / P_t g ≤ e^{-2t}
P_t((g')²/g)`. Finally integrate against γ + γ-invariance.

Expected effort: ~150-250 lines (substantially less than the 2D-Jensen
route — most of the work is the Cauchy-Schwarz application + γ-invariance
manipulation).

## References

* Bakry-Gentil-Ledoux, Proposition 5.5.2 and §5.5.
* Bakry-Émery (1985), "Diffusions hypercontractives," Prop. 1.

## Vetting

**Standard** (gemini-3.1-pro-preview, 2026-05-12). Hypotheses tight;
`ε ≤ g ⇒ P_t g ≥ ε` for free since `P_t` averages against a probability
kernel; exponent `exp(-2t)` correct for OU(1) Bakry-Émery curvature
`ρ = 1`. No counterexamples. -/
axiom ouSemigroup_fisher_info_decay
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    {ε M : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hg'_bd : ∀ x, |deriv g x| ≤ M)
    (t : ℝ) (ht : 0 ≤ t) :
    fisherInfo (ouSemigroup t g) ≤ Real.exp (-2 * t) * fisherInfo g

/-! ## A2: De Bruijn identity (entropy derivative = -Fisher info) -/

/-- **De Bruijn identity for the OU semigroup.** AXIOM
(vetting-required textbook bridge).

For any `C¹` `g : ℝ → ℝ` with `g, g'` bounded and `g ≥ ε > 0` pointwise,
the Boltzmann entropy `H(P_s g) = ∫ P_s g · log(P_s g) dγ` is
differentiable in `s` at any `t > 0` with derivative

  `(d/dt) H(P_t g) = -I(P_t g)`.

## Proof in textbooks

Differentiate under the integral sign:
  `(d/dt) ∫ P_t g · log(P_t g) dγ
     = ∫ ((d/dt) P_t g) · (1 + log P_t g) dγ`
     `= ∫ L(P_t g) · (1 + log P_t g) dγ`  (heat equation
                                            `hasDerivAt_t_ouSemigroup`)
     `= ∫ L(P_t g) · log(P_t g) dγ`  (since `∫ L(h) dγ = 0` for any
                                       `h` integrable, by γ-invariance)
     `= -∫ Γ(P_t g, log(P_t g)) dγ`  (integration by parts,
                                       `gaussian_dirichlet_form_identity`-style)
     `= -∫ ((P_t g)')² / P_t g dγ`  (since `Γ(f, log g) = f' · g'/g` and
                                       here `f = g = P_t g`).

The parametric differentiation requires the integrand
`(s, y) ↦ P_s g(y) · log(P_s g(y))` to satisfy a uniform dominator —
since `g ≥ ε > 0` and `|g| ≤ M`, `P_s g` also stays in `[ε, M]`, and
`s · log s` is continuous and bounded on `[ε, M]`.

## Discharge plan

Per Gemini 3.1-pro vetting (verdict: **Standard**, 2026-05-12). Two
sub-steps:

1. **Bilinear Dirichlet form identity** (auxiliary, ~50-100 lines):
   `∫ f · L h dγ = -∫ f' · h' dγ` for suitable test functions. Provable
   via 1D IBP using the identity `(h'(y) · e^{-y²/2})' = (Lh)(y) ·
   e^{-y²/2}`. This generalizes our existing
   `gaussian_dirichlet_form_identity` (which is the diagonal case
   `f = h = g`).
2. **Parametric differentiation** (~150-250 lines): differentiate
   `s ↦ ∫ P_s g · log(P_s g) dγ` under the integral via the heat
   equation `(d/ds) P_s g = L(P_s g)` and the chain rule. Use the
   bilinear Dirichlet form identity to get
   `∫ L(P_t g) · (1 + log P_t g) dγ = -∫ ((P_t g)')² / P_t g dγ`
   (taking `f := P_t g`, `h := 1 + log P_t g`, so `h' = (P_t g)'/P_t g`).
   The `(d/ds) = (d/dt)`-style step uses Mathlib's
   `hasDerivAt_integral_of_dominated_loc_of_deriv_le`; dominator is
   `|L(P_t g)|·(M·log M + 1)` which is γ-integrable (linear growth
   times Gaussian).

The C¹ restriction on `g` (not `C^∞`) is intentional: for `t > 0`,
`P_t g` is automatically `C^∞` (by `ouSemigroup_contDiff_bounded`,
discharged in `EuclideanHermite.lean`), so the differentiation works
cleanly. At `t = 0` the right-derivative is established by FTC + DCT
limit (the auxiliary `hasDerivWithinAt_entropy_ouSemigroup_zero`).

## References

* Bakry-Gentil-Ledoux, §5.5 (de Bruijn identity).
* Stam (1959), "Some inequalities satisfied by the quantities of
  information of Fisher and Shannon."

## Vetting

**Standard** (gemini-3.1-pro-preview, 2026-05-12). For `t > 0`, the
parametric differentiation goes through cleanly because `P_t g` is
`C^∞` and the integrand `(LP_tg)(1 + log P_tg)` has at-most-linear
growth × Gaussian decay → γ-integrable. The boundary version at
`t = 0` (which has only `C¹` regularity) is correct via the FTC+DCT
route: `lim_{t↘0} I(P_t g) = I(g)` by DCT, so the right-derivative
matches. Hypotheses tight; both `g ≤ M` and `|g'| ≤ M` are needed
for clean dominator bounds. -/
axiom hasDerivAt_entropy_ouSemigroup
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    {ε M : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hg'_bd : ∀ x, |deriv g x| ≤ M)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => boltzmannEntropy (ouSemigroup s g))
      (-fisherInfo (ouSemigroup t g)) t

/-- **Boundary case of de Bruijn at `t = 0+`.** AXIOM.

The de Bruijn identity extends to a right-derivative at `t = 0`:
`HasDerivWithinAt (s ↦ H(P_s g)) (-I(g)) (Ici 0) 0`.

Required for the FTC application that integrates from 0 to t. -/
axiom hasDerivWithinAt_entropy_ouSemigroup_zero
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    {ε M : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hg'_bd : ∀ x, |deriv g x| ≤ M) :
    HasDerivWithinAt (fun s => boltzmannEntropy (ouSemigroup s g))
      (-fisherInfo g) (Set.Ici 0) 0

end Gaussian1D

end
