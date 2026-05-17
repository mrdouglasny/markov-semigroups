/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strong-`L²` difference-quotient limit for the Gaussian OU semigroup

G2 (a) of the Gross-discharge plan (`plans/gross-discharge.md`) — the
analytic core. For core `f`, the right difference quotient of the
`Lp`-carrier OU semigroup converges in `L²(γFin n)`-norm to the named
generator `ouGeneratorFin f = Δf − x·∇f`.

**This file is the Codex work item.** It contains exactly one
`sorry` (`ouSemigroupFinLp_diffQuot_tendsto`). It is deliberately
isolated so it can be filled in parallel with the γ-IBP / assembly
work in `EuclideanGeneratorCompat`.
-/

import MarkovSemigroups.Instances.WorkInProgress.EuclideanGeneratorLp

open MeasureTheory Filter
open scoped BigOperators Topology InnerProductSpace ContDiff

noncomputable section

namespace GaussianFin

variable {n : ℕ}

/-- **`Fin n`-generic Stein/Gaussian-IBP wrapper** (Codex, 2026-05-16).
`EuclideanFin.stein_partialDeriv_ouShiftFin` is stated only for
`Fin (n+1)`; this lifts it to generic `Fin n` by case-splitting
(`n = 0`: `i : Fin 0` is vacuous via `Fin.elim0`; `n = m+1`: the
existing lemma). Unblocks the `Fin n` endpoint theorem below. -/
private theorem stein_partialDeriv_ouShiftFin_all {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (t : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    ∫ y, y i * partialDeriv i f (ouShiftFin t x y) ∂γFin n =
      Real.sqrt (1 - Real.exp (-2 * t)) *
        ouSemigroupFin t (secondPartial i f) x := by
  cases n with
  | zero => exact (Fin.elim0 i)
  | succ m =>
      simpa using
        (stein_partialDeriv_ouShiftFin (n := m) (f := f) hf t i x)

/-- **Ornstein–Uhlenbeck pointwise heat equation at `t = 0⁺`** (the
right-endpoint of the Mehler-semigroup time derivative).

For `f : (Fin n → ℝ) → ℝ` that is `C^∞` with uniformly bounded value,
first and second coordinate derivatives, the explicit Mehler integral
`t ↦ ∫ f(e^{-t}x + √(1-e^{-2t})·y) d(⊗ⁿ N(0,1))(y)` has right
derivative at `0` equal to the OU generator `Lf(x) = Δf(x) − x·∇f(x)`.

**General (no project definitions).** Stated purely in Mathlib terms
— `fderiv`, `Pi.single`, `Real.exp`/`Real.sqrt`,
`MeasureTheory.Measure.pi`, `ProbabilityTheory.gaussianReal`,
`HasDerivWithinAt`, `Set.Ici` — so it is a reusable, vetting-amenable
textbook statement rather than a project-specific stopgap. The
project-specific `hasDerivWithinAt_t_ouSemigroupFin_zero` is derived
from it by unfolding the (thin) project definitions.

Reference: Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov
Diffusion Operators* (2014), §2.7 (the Ornstein–Uhlenbeck/heat
semigroup and its generator); Mehler's formula. **Vetted Standard /
Likely correct** (Gemini `gemini-3-pro-preview`, 2026-05-16; recorded
in `AXIOM_AUDIT.md`): well-formed; matches BGL §2.7 with
self-consistent variance-1 Mehler constants (no rescaling); non-vacuous;
**pure-second-partial bounds sufficient** — via Itô/Dynkin
`Pₜf − f = ∫₀ᵗ Pₛ(Lf) ds` the martingale term vanishes in
expectation, so only `|∇f|`,`|Δf|` boundedness is needed (no mixed-
partial, third-derivative, or growth hypotheses); right-derivative
endpoint form correct. Discharge route: parametric differentiation
under the integral with the Pi-valued chain rule through the Mehler
shift + the scaling identity `∂ᵢ²(Pₜf) = e^{-2t} Pₜ(∂ᵢ²f)` (see the
two-interface obstacle note on the project lemma below). -/
axiom gaussianOU_heatEquation_within_zero {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf_smooth : ContDiff ℝ ∞ f) (M : ℝ)
    (hf_bd : ∀ x : Fin n → ℝ,
      ‖f x‖ ≤ M ∧
      (∀ i : Fin n, ‖fderiv ℝ f x (Pi.single i 1)‖ ≤ M) ∧
      (∀ i : Fin n,
        ‖fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x
            (Pi.single i 1)‖ ≤ M))
    (x : Fin n → ℝ) :
    HasDerivWithinAt
      (fun t : ℝ =>
        ∫ y,
          f (fun i => Real.exp (-t) * x i
              + Real.sqrt (1 - Real.exp (-2 * t)) * y i)
          ∂(MeasureTheory.Measure.pi
              (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)))
      ((∑ i : Fin n,
          fderiv ℝ (fun z => fderiv ℝ f z (Pi.single i 1)) x
            (Pi.single i 1))
        - ∑ i : Fin n, x i * fderiv ℝ f x (Pi.single i 1))
      (Set.Ici 0) 0

/-- **The precise blocker (Codex 2026-05-16): the nD pointwise OU
heat equation at `t = 0⁺`.** The branch controls *spatial*
derivatives of `ouSemigroupFin t f` and has the scalar/L²-continuity
endgame, but exposes **no reusable multivariate pointwise
time-derivative** for `τ ↦ ouSemigroupFin τ f x`. This lemma is
exactly that missing prerequisite (right-derivative-at-0 form, which
Codex confirmed suffices): `P_0 f = f`, so the right `t`-derivative of
`τ ↦ (P_τ f) x` at `0` is `(L f) x = ouGeneratorFin f x`.

Proof route: tensor/Fubini lift of the proved 1D
`Gaussian1D.hasDerivAt_t_ouSemigroup'` (G1) through
`ouSemigroupFin_section_eq_ouSemigroup` / `ouSemigroupFin_insertNth_eq`
+ per-coordinate product rule + the `t→0⁺` endpoint
(`hasDerivWithinAt_Ici_of_tendsto_deriv`, as used for the 1D /
quadratic discharges). This is the genuine analytic crux; isolated as
its own target so it can be filled (Codex) independently of the DCT
upgrade below.

**Remaining obstacle (Codex, 2026-05-16; the `Fin n` Stein wrapper
above is done).** Two specific Lean interfaces fight the parametric
heat-equation proof: (1) the `HasDerivAt`-under-the-integral for
`τ ↦ ouSemigroupFin τ f x` needs a *Pi-valued chain rule through
`ouShiftFin`*, with the derivative integrand `F'` presented to
simultaneously satisfy `hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
finite-sum measurability, and the later integral algebra; (2) then the
Mehler-scaling identity
`secondPartial i (ouSemigroupFin t f) x
  = exp (-2*t) * ouSemigroupFin t (secondPartial i f) x`
must be bridged through `section_secondDeriv` /
`section_secondDeriv_ouSemigroupFin_eq`. -/
theorem hasDerivWithinAt_t_ouSemigroupFin_zero {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) (x : Fin n → ℝ) :
    HasDerivWithinAt (fun t : ℝ => ouSemigroupFin t f x)
      (ouGeneratorFin f x) (Set.Ici 0) 0 := by
  obtain ⟨hsm, M, hM⟩ := hf
  simpa only [ouSemigroupFin, ouShiftFin, γFin, Gaussian1D.γ,
    ouGeneratorFin_apply, secondPartial, partialDeriv] using
    gaussianOU_heatEquation_within_zero (n := n) f hsm M hM x

/-- **G2 (a) — strong-`L²` difference-quotient limit.** For core `f`,
`t⁻¹ • (P_t [f] − [f]) → [ouGeneratorFin f]` in `Lp ℝ 2 (γFin n)` as
`t → 0⁺` (right limit, matching `GeneratorCompat`'s `𝓝[>] 0`).

Strategy (Gross-discharge plan, Gemini-vetted): from the now-explicit
prerequisite `hasDerivWithinAt_t_ouSemigroupFin_zero`, the pointwise
right limit `(P_t f(x) − f(x))/t → ouGeneratorFin f x` is immediate;
the difference quotient is dominated by a fixed `L²(γFin n)` function
(core `IsCoreFin` bounds + Mehler contraction
`ouSemigroupFin_preserves_*`), so dominated convergence upgrades the
pointwise limit to the strong `L²` limit. Same DCT pattern as the
existing `ouSemigroupFin_l2_sq_hasDerivWithinAt` /
`gaussian1D_pairing_hasDerivWithinAt_zero` discharges. -/
theorem ouSemigroupFinLp_diffQuot_tendsto {f : (Fin n → ℝ) → ℝ}
    (hf : IsCoreFin f) :
    Tendsto
      (fun t : ℝ => t⁻¹ •
        ((stdGaussianFin_dirichletMarkovSemigroup n).P t
            ((stdGaussianFin_dirichletMarkovSemigroup n).coreToL2 hf)
          - (stdGaussianFin_dirichletMarkovSemigroup n).coreToL2 hf))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (ouGeneratorFinLp hf)) := by
  sorry

end GaussianFin

end
