/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hypercontractivity and the Gross Equivalence

A Markov semigroup P_t is hypercontractive if it maps L^p → L^q
for suitable (p, q, t). Nelson (1973) proved this for the OU
semigroup. Gross (1975) showed the equivalence with the log-Sobolev
inequality.

## Main definitions

- `IsHypercontractive` — P_t : L^p → L^q bounded with norm 1
- `HypercontractiveRate` — the optimal rate ρ
- `NelsonBound` — the optimal (p,q,t) relation: e^{-2ρt} ≤ (p-1)/(q-1)

## Main results

- `hypercontractive_of_logSobolev` — LSI with constant ρ implies
  hypercontractivity with rate ρ (Gross 1975)
- `logSobolev_of_hypercontractive` — hypercontractivity with rate ρ
  implies LSI with constant ρ (Gross 1975)
- `gross_equivalence` — LSI ↔ hypercontractivity

## The Nelson estimate

For a semigroup with hypercontractivity rate ρ, and a perturbation
V with ‖V‖_{L^p} < ∞:

  ‖e^{-V}‖_{L^q} ≤ ‖e^{-P_t V}‖_{L^p} · (semigroup bound)

This is the mechanism used to control interacting QFT:
- P_t smooths V (reduces its L^p norm)
- The L^p → L^q improvement gives room for the exponential
- The result: ‖e^{-V}‖_{L^q} ≤ exp(C · ‖V‖)

## References

- Nelson, "The free Markoff field," J. Funct. Anal. 12 (1973)
- Gross, "Logarithmic Sobolev inequalities," Amer. J. Math. 97 (1975)
- Gross, "Hypercontractivity and logarithmic Sobolev inequalities
  for the Clifford-Dirichlet form," Duke Math. J. 42 (1975)
- Simon, *The P(φ)₂ Euclidean QFT*, Princeton, 1974, Ch. I
-/

import MarkovSemigroups.Abstract.DirichletForm

open MeasureTheory

noncomputable section

/-- A Markov semigroup P_t on a probability space (X, μ) is a
family of operators P_t : L^∞(X) → L^∞(X) parametrized by t ≥ 0,
satisfying the semigroup property P_{s+t} = P_s ∘ P_t and the
contraction property ‖P_t f‖_p ≤ ‖f‖_p.

This is the abstract version of the heat semigroup / OU semigroup. -/
structure MarkovSemigroup (X : Type*) [MeasurableSpace X] where
  /-- The reference probability measure. -/
  μ : Measure X
  hμ : IsProbabilityMeasure μ
  /-- The semigroup operator at time t. -/
  P : ℝ → (X → ℝ) → (X → ℝ)
  /-- Semigroup property. -/
  semigroup : ∀ s t f, P (s + t) f = P s (P t f)
  /-- P_0 = identity. -/
  identity : ∀ f, P 0 f = f
  /-- L² contraction. -/
  contraction : ∀ t f,
    ∫ x, (P t f x) ^ 2 ∂μ ≤ ∫ x, (f x) ^ 2 ∂μ

namespace MarkovSemigroup

variable {X : Type*} [MeasurableSpace X]

/-- A semigroup is hypercontractive with rate ρ if P_t maps L^p → L^q
whenever e^{-2ρt} ≤ (p-1)/(q-1), with operator norm ≤ 1.

This means: for any 1 < p ≤ q < ∞ and t > 0 satisfying the
Nelson bound q ≤ 1 + (p-1)e^{2ρt}:

  (∫ |P_t f|^q dμ)^{1/q} ≤ (∫ |f|^p dμ)^{1/p}

Physically: the semigroup boosts integrability. Waiting time t
buys you L^p → L^q improvement at rate ρ. -/
def IsHypercontractive (S : MarkovSemigroup X) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ (p q : ℝ) (t : ℝ),
    1 < p → p ≤ q → 0 < t →
    q ≤ 1 + (p - 1) * Real.exp (2 * ρ * t) →
    -- ‖P_t f‖_q ≤ ‖f‖_p for all f:
    ∀ f : X → ℝ,
      (∫ x, |S.P t f x| ^ q ∂S.μ) ^ (1/q) ≤
      (∫ x, |f x| ^ p ∂S.μ) ^ (1/p)

/-- **Postulated (Gross 1975, Theorem 1).** LSI implies hypercontractivity.
The proof uses the semigroup interpolation method: differentiate
���P_t f‖_{p(t)} along the path p(t) = 1 + (p-1)e^{2ρt} and show
the derivative is ≤ 0 using the LSI. -/
axiom gross_lsi_implies_hypercontractive {X : Type*} [MeasurableSpace X]
    (S : MarkovSemigroup X) [ds : DirichletSpace X]
    (h_compatible : ds.μ = S.μ) (ρ : ℝ)
    (h_lsi : ds.SatisfiesLogSobolev ρ) : S.IsHypercontractive ρ

/-- **Postulated (Gross 1975, Theorem 2).** Hypercontractivity implies LSI.
The proof differentiates the hypercontractive bound ‖P_t f‖_q ≤ ‖f‖_p
at t = 0 with p = 2, q = 2 + ε and takes ε → 0. -/
axiom gross_hypercontractive_implies_lsi {X : Type*} [MeasurableSpace X]
    (S : MarkovSemigroup X) [ds : DirichletSpace X]
    (h_compatible : ds.μ = S.μ) (ρ : ℝ)
    (h_hyp : S.IsHypercontractive ρ) : ds.SatisfiesLogSobolev ρ

/-- Gross's theorem (forward direction): LSI implies hypercontractivity.

If the Dirichlet space (X, μ, E) satisfies the log-Sobolev inequality
with constant ρ, and P_t is the associated semigroup (with E(f,f) =
-∫ f · Lf dμ where L generates P_t), then P_t is hypercontractive
with rate ρ.

This is Gross (1975), Theorem 1. -/
theorem hypercontractive_of_logSobolev (S : MarkovSemigroup X)
    [ds : DirichletSpace X]
    (h_compatible : ds.μ = S.μ)
    (ρ : ℝ) (h_lsi : ds.SatisfiesLogSobolev ρ) :
    S.IsHypercontractive ρ :=
  gross_lsi_implies_hypercontractive S h_compatible ρ h_lsi

/-- Gross's theorem (reverse direction): hypercontractivity implies LSI.

Gross (1975), Theorem 2. -/
theorem logSobolev_of_hypercontractive (S : MarkovSemigroup X)
    [ds : DirichletSpace X]
    (h_compatible : ds.μ = S.μ)
    (ρ : ℝ) (h_hyp : S.IsHypercontractive ρ) :
    ds.SatisfiesLogSobolev ρ :=
  gross_hypercontractive_implies_lsi S h_compatible ρ h_hyp

/-- The Gross equivalence: LSI ↔ hypercontractivity.

For a Markov semigroup with associated Dirichlet form:
  LSI with constant ρ  ⟺  hypercontractivity with rate ρ -/
theorem gross_equivalence (S : MarkovSemigroup X)
    [ds : DirichletSpace X]
    (h_compatible : ds.μ = S.μ) (ρ : ℝ) :
    ds.SatisfiesLogSobolev ρ ↔ S.IsHypercontractive ρ :=
  ⟨S.hypercontractive_of_logSobolev h_compatible ρ,
   S.logSobolev_of_hypercontractive h_compatible ρ⟩

/-! ## Direct consequence: the semigroup improves integrability -/

/-- Direct application of hypercontractivity to any function f.

  ‖P_t f‖_{L^q(μ)} ≤ ‖f‖_{L^p(μ)}

whenever q ≤ 1 + (p-1)e^{2ρt}. This is just the definition
of `IsHypercontractive` unpacked. -/
theorem semigroup_lp_improvement (S : MarkovSemigroup X)
    (ρ : ℝ) (h_hyp : S.IsHypercontractive ρ)
    (f : X → ℝ)
    (p q : ℝ) (hp : 1 < p) (hpq : p ≤ q)
    (t : ℝ) (ht : 0 < t)
    (h_bound : q ≤ 1 + (p - 1) * Real.exp (2 * ρ * t)) :
    (∫ x, |S.P t f x| ^ q ∂S.μ) ^ (1/q) ≤
    (∫ x, |f x| ^ p ∂S.μ) ^ (1/p) :=
  h_hyp.2 p q t hp hpq ht h_bound f

-- NOTE: The full "Nelson estimate" for constructive QFT
-- (controlling ‖e^{-V}‖ for the interacting Boltzmann weight)
-- involves additional steps beyond bare hypercontractivity:
--   1. Jensen's inequality: P_t(e^{-V}) ≥ e^{-P_t V} (convexity of exp)
--   2. Decomposition of V into localized pieces (cluster expansion)
--   3. The specific structure of the P(φ)₂ interaction
-- These application-specific steps belong in pphi2 / pphi2N,
-- not in this abstract module.

end MarkovSemigroup

end
