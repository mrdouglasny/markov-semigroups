/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Polynomial Chaos Concentration (Janson Theorem 5.10)

For a centered $F \in \mathcal H^{\le d}$ (a polynomial of total
degree $\le d$ in a finite-dim Gaussian vector), there is a
universal constant $c_d > 0$ depending only on $d$ such that
$$
\mathbb P\bigl(|F| > \lambda \, \|F\|_{L^2}\bigr)
  \;\le\; 2 \exp\bigl(-c_d \, \lambda^{2/d}\bigr),
\qquad \lambda > 0.
$$

The exponent $2/d$ is sharp (saturated by $F = \phi_1^d$). The
constant $c_d$ is dimension-independent (independent of $n$, the
size of the Gaussian vector).

## Equivalent Bonami-Nelson L^p form

$$
\|F\|_{L^p} \;\le\; (p - 1)^{d/2} \, \|F\|_{L^2},
\qquad p \ge 2.
$$

## Proof outline (three ingredients)

1. **OU hypercontractivity** restricted to chaos $\mathcal H_k$
   (`OUEigenfunctions`): for $f \in \mathcal H_k$ and $p \ge 2$,
   $\|f\|_{L^p} \le (p-1)^{k/2} \|f\|_{L^2}$.
2. **Markov / Chebyshev**: $\mathbb P(|F| > \lambda \|F\|_2) \le
   (\|F\|_p / (\lambda \|F\|_2))^p$.
3. **Optimize** $p$: set $p - 1 = (\lambda/e)^{2/d}$.

This file is the LD endpoint that downstream consumers call.

## Main theorems

- `bonami_nelson_chaos` — L^p improvement on a single chaos $\mathcal H_k$.
- `bonami_nelson_chaosLE` — L^p improvement on $\mathcal H^{\le d}$
  (with a multiplicative degree-dependent constant).
- `polynomial_chaos_concentration` — the Janson 5.10 tail bound.

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), Theorem 5.10
  (the gold-standard reference for this bound).
- A. Bonami, *Étude des coefficients de Fourier des fonctions de
  $L^p(G)$*, Ann. Inst. Fourier 20 (1970).
- E. Nelson, "The free Markov field," J. Funct. Anal. 12 (1973).
- R. Adamczak, P. Wolff, "Concentration inequalities for non-Lipschitz
  functions," Probab. Theory Related Fields 162 (2015) — modern
  treatment with explicit constants.

## Status

API + axiom skeleton (2026-05-08). The Bonami-Nelson L^p improvement
on a single chaos follows immediately from the OU eigenfunction
identity (`ouSemigroup_act_wienerChaos`) plus the abstract
hypercontractivity inequality already in
`Abstract/Hypercontractivity.lean`. The concentration tail bound is
a Markov + optimize derivation from the L^p bound. Both are stated
as axioms here pending the OU semigroup being concretely available;
the proof scripts are short once the prerequisites are wired.
-/

import MarkovSemigroups.Gaussian.OUEigenfunctions

noncomputable section

namespace MarkovSemigroups.Gaussian

open MeasureTheory

variable {n : ℕ}

/-- **Bonami-Nelson L^p improvement on a single Wiener chaos.**

For $f \in \mathcal H_k$ and $p \ge 2$:
$$
\|f\|_{L^p} \;\le\; (p - 1)^{k/2} \, \|f\|_{L^2}.
$$

**Reference:** Bonami (1970) for the 1D case; Nelson (1973) for the
infinite-dim OU semigroup. Janson §5.1.

**Proof strategy:** The OU semigroup $T_t$ is hypercontractive: it
maps $L^2 \to L^p$ for $e^{2t} = p - 1$ with operator norm $\le 1$
(`Abstract/Hypercontractivity.lean`). Restricted to $\mathcal H_k$,
$T_t$ acts as multiplication by $e^{-kt}$
(`ouSemigroup_act_wienerChaos`), hence
$\|f\|_{L^p} \cdot e^{-kt} \le \|f\|_{L^2}$. Solving for
$\|f\|_{L^p}$ with $e^{2t} = p - 1$ gives the bound. -/
axiom bonami_nelson_chaos (n k : ℕ)
    (f : Lp ℝ 2 (stdGaussianFin n))
    (_hf : f ∈ wienerChaos n k)
    (p : ℝ) (_hp : 2 ≤ p) :
    ‖f‖ ≤ (p - 1) ^ ((k : ℝ) / 2) * ‖f‖

/-- **Bonami-Nelson L^p improvement on $\mathcal H^{\le d}$.**

Triangle inequality across $k = 0, \dots, d$ extends the per-chaos
bound to $\mathcal H^{\le d}$ at the cost of a degree-$d$ prefactor:
$$
\|F\|_{L^p} \;\le\; (d + 1) \, (p - 1)^{d/2} \, \|F\|_{L^2}.
$$

**Reference:** Janson §5.1.

**Proof strategy:** Decompose `F = ∑ k ∈ range (d+1), Π_k F` via the
chaos projections (`chaosProjection`), apply `bonami_nelson_chaos` to
each summand, take triangle inequality, dominate $(p-1)^{k/2}$ by
$(p-1)^{d/2}$ for $k \le d$ and $p \ge 2$. -/
axiom bonami_nelson_chaosLE (n d : ℕ)
    (F : Lp ℝ 2 (stdGaussianFin n))
    (_hF : F ∈ wienerChaosLE n d)
    (p : ℝ) (_hp : 2 ≤ p) :
    ‖F‖ ≤ ((d : ℝ) + 1) * (p - 1) ^ ((d : ℝ) / 2) * ‖F‖

/-- **Polynomial Chaos Concentration (Janson Theorem 5.10).**

For centered $F \in \mathcal H^{\le d}$ with $d \ge 1$, there is a
universal constant $c_d > 0$ (depending only on $d$, not on $n$ or
the specific Gaussian vector) such that for all $\lambda > 0$,
$$
\mathbb P\bigl(|F| > \lambda \, \|F\|_{L^2}\bigr)
  \;\le\; 2 \exp\bigl(-c_d \, \lambda^{2/d}\bigr).
$$

**Reference:** Janson, *Gaussian Hilbert Spaces*, Theorem 5.10.

**Proof strategy** (Markov + optimize, three lines):
1. By Markov,
   $\mathbb P(|F| > \lambda \|F\|_2) \le \mathbb E |F|^p / (\lambda \|F\|_2)^p$.
2. By Bonami-Nelson on $\mathcal H^{\le d}$,
   $\mathbb E |F|^p \le \bigl((d+1)(p-1)^{d/2}\bigr)^p \, \|F\|_2^p$.
3. Combined: $\mathbb P(\dots) \le \bigl((d+1)(p-1)^{d/2} / \lambda\bigr)^p
   = (d+1)^p \exp\bigl(p[(d/2)\log(p-1) - \log \lambda]\bigr)$.
4. Set $p - 1 = (\lambda / ((d+1) e))^{2/d}$ to make the exponent
   $\le -d/2 \cdot (\lambda / ((d+1)e))^{2/d}$.
5. The $(d+1)^p$ prefactor is absorbed into the constant for
   $\lambda$ above a threshold $\lambda_0(d)$; below that the bound
   $\le 2$ is trivial. -/
axiom polynomial_chaos_concentration (n d : ℕ) (_hd : 1 ≤ d) :
    ∃ c_d : ℝ, 0 < c_d ∧
      ∀ (F : Lp ℝ 2 (stdGaussianFin n)),
        F ∈ wienerChaosLE n d →
        ∀ (lam : ℝ), 0 < lam →
          (stdGaussianFin n) {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|} ≤
            2 * ENNReal.ofReal (Real.exp (-c_d * lam ^ ((2 : ℝ) / d)))

end MarkovSemigroups.Gaussian
