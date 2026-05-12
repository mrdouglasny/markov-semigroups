/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Schwartz-class convolution preserves `C^∞`

This file states (as a textbook axiom) the smoothing property of convolution
against a Schwartz-class kernel: if `K` is `C^∞` with all iterated derivatives
integrable, and `f` is bounded measurable, then the convolution `f ⋆ K` is
`C^∞`. This is the standard "smoothing-by-Schwartz" theorem; Mathlib has the
compact-support version (`HasCompactSupport.contDiff_convolution_right`) but
not this Schwartz-class generalization at the time of writing.

## Why this is needed

The Mehler kernel `K_t(x, z) = (b√(2π))⁻¹ · exp(−(z − e^{−t}x)²/(2b²))` is
`C^∞` in `x` with Gaussian decay in `z`. Convolving a bounded measurable `f`
against this kernel gives a function that is `C^∞` in `x` — this is the
content of `ouSemigroup_contDiff` in `Euclidean.lean`. The axiom below is the
general, Mathlib-style formulation; `ouSemigroup_contDiff` becomes a one-line
corollary.

## References

- Reed–Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Theorem V.4 (Schwartz space is closed under convolution and is `C^∞`).
- Folland, *Real Analysis*, §8.2 (Convolution and approximation).
- Mathlib analogs that motivate this statement:
  `Mathlib.Analysis.Calculus.ContDiff.Convolution` (`HasCompactSupport`
  versions).
-/

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open MeasureTheory Real

noncomputable section

/-- **Smooth integrable-derivative kernel convolution preserves `C^∞`.** AXIOM
(vetting-required textbook bridge).

For a kernel `K : ℝ → ℝ` that is `C^∞` and whose iterated derivatives are
all integrable against Lebesgue measure, and a bounded measurable function
`f : ℝ → ℝ`, the convolution `x ↦ ∫ K(x − y) · f(y) dy` is `C^∞` as a
function of `x`.

The integrand is written with `x` inside the smooth factor `K` (not the
merely measurable factor `f`), so differentiation under the integral sign
applies directly without a change-of-variables step. Both forms
(`K y * f (x − y)` and `K (x − y) * f y`) compute the same integral by
translation invariance of Lebesgue measure, but only the form below
admits a direct proof via Leibniz rule, since `f` is only measurable.

The proof in textbooks proceeds by induction on the differentiation order:
at each step, differentiate under the integral sign using Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The local dominator at
order `n` on `|x| ≤ R` is `|K^{(n)}(-y)| + 2R · |K^{(n+1)}(·)|`-type
bound (FTC + Fubini), which is integrable since both `D^n K` and
`D^{n+1} K` are in `L¹`.

Mathlib has `HasCompactSupport.contDiff_convolution_right` for the
compact-support case; this axiom extends to integrable-derivative kernels.

## Vetting status

**Likely correct, revision applied** (vetted 2026-05-12 by Gemini
`gemini-3.1-pro-preview`; initial `gemini-2.5-pro` vetting returned
"Standard").

Gemini 3.1-pro identified that the original form `K y * f (x − y)`
required a change-of-variables step before differentiation under the
integral could be applied, since `f` is only measurable. The integrand
has been swapped to `K (x − y) * f y` per the 3.1-pro recommendation.
Hypotheses are confirmed tight: every `D^n K ∈ L¹` plus `f ∈ L^∞` is
exactly the Sobolev `W^{∞,1}` × `L^∞` condition needed (Lieb–Loss
Theorem 2.16, applied with `p=∞, q=1`).

## Discharge plan

By induction on the differentiation order, using:
* `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (Mathlib parametric
  derivative). Differentiating `K(x − y) · f(y)` in `x` gives
  `K'(x − y) · f(y)`, bounded locally by `(|K'(-y)| + 2R·|K''(·)|) · M`
  which is `L¹` by hypothesis.
* The identity `(K ⋆ f)^{(n+1)} = ((D K) ⋆ f)^{(n)}` (derivative falls on
  the smooth factor K).
* Continuity of `L¹` translation to show each derivative is continuous.
* `ContDiff.of_succ` / iterated-derivative induction in Mathlib.

Estimated effort: 200–400 lines, comparable to a Mathlib-quality contribution.

## References

- Lieb & Loss, *Analysis* (2nd ed.), Theorem 2.16 (Derivatives of
  convolutions): canonical reference for this exact statement.
- Folland, *Real Analysis* (2nd ed.), Chapter 8, Section 2 (Convolution):
  Proposition 8.10(b) (`f ∈ L¹, g ∈ L^∞ ⇒ f ⋆ g` uniformly continuous);
  Exercise 8.4 (`f ∈ L^p`, `g ∈ W^{k,p'}` ⇒ `f ⋆ g ∈ C^k`).
- Hörmander, *The Analysis of Linear Partial Differential Operators I*. -/
axiom contDiff_top_convolution_schwartzKernel
    {K : ℝ → ℝ} (hK_smooth : ContDiff ℝ ⊤ K)
    (hK_deriv_int : ∀ n : ℕ, Integrable (iteratedDeriv n K) volume)
    {f : ℝ → ℝ} (hf_meas : Measurable f) {M : ℝ}
    (hf_bd : ∀ x, |f x| ≤ M) :
    ContDiff ℝ ⊤ (fun x => ∫ y, K (x - y) * f y)

end
