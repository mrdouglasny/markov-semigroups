/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hermite Polynomials Are OU Eigenfunctions

The Ornstein-Uhlenbeck generator on $L^2(\gamma_n)$ (with $\gamma_n$
the standard multivariate Gaussian on $\mathbb R^n$) is
$$
L f(x) \;=\; \Delta f(x) - x \cdot \nabla f(x).
$$

The key spectral fact: $L H_\alpha = -|\alpha| H_\alpha$ for every
multi-index $\alpha$, so the $k$-th Wiener chaos is the eigenspace
of $L$ with eigenvalue $-k$. The OU semigroup $T_t$ acts on
$\mathcal H_k$ by $e^{-kt}$.

The proof is direct algebra:
1. The 1D recurrence gives $L_1 H_k = -k \, H_k$ where
   $L_1 = \partial_x^2 - x \partial_x$.
2. The multi-dim $L$ is a sum of single-coordinate operators
   $L_i = \partial_{x_i}^2 - x_i \partial_{x_i}$.
3. $H_\alpha = \prod_i H_{\alpha_i}(x_i)$, and each $L_i$ acts only
   on its own coordinate, contributing $-\alpha_i$. Sum gives
   $-|\alpha|$.

This bypasses any infinite-dimensional spectral theory: the
eigenfunction relation is a polynomial identity.

## Main definitions

- `ouGenerator n` — the operator $L = \Delta - x \cdot \nabla$ on
  smooth functions $\mathbb R^n \to \mathbb R$.

## Main theorems

- `ouGenerator_hermiteMulti_1d` — `L₁ H_k = -k · H_k` (1D base case).
- `ouGenerator_hermiteMulti` — `L H_α = -|α| · H_α` (multi-index).
- `ouSemigroup_act_wienerChaos` — `T_t f = exp(-k t) · f` for
  `f ∈ wienerChaos γ k`. This is the semigroup-level reformulation.

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), §2.4
  (the OU semigroup) and Theorem 4.4 (eigenvalues of `L`).
- D. Bakry, I. Gentil, M. Ledoux, *Analysis and Geometry of Markov
  Diffusion Operators*, Springer (2014), §2.7.

## Status

API + axiom skeleton (2026-05-08). The 1D and multivariate
eigenfunction identities are stated as axioms with explicit
proof-strategy docstrings citing the polynomial recurrence; the
semigroup-level reformulation depends on the
`Diffusion/OrnsteinUhlenbeck.lean` skeleton being filled in.
-/

import MarkovSemigroups.Gaussian.WienerChaos

noncomputable section

namespace MarkovSemigroups.Gaussian

/-- The 1D Ornstein-Uhlenbeck generator
$L_1 f(x) = f''(x) - x \, f'(x)$ acting on smooth real functions. -/
noncomputable def ouGenerator1D (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv (deriv f) x - x * deriv f x

/-- The $n$-dim Ornstein-Uhlenbeck generator
$L f(x) = \Delta f(x) - x \cdot \nabla f(x)$. -/
noncomputable def ouGenerator (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x =>
    (∑ i, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single i 1)) -
    (∑ i, x i * fderiv ℝ f x (Pi.single i 1))

/-- **1D Hermite polynomials are OU eigenfunctions:**
`L₁ H_k = -k · H_k`.

**Proof strategy:** Direct calculation from the probabilist's Hermite
recurrence
- $H_{k+1}(x) = x \, H_k(x) - k \, H_{k-1}(x)$
- $H_k'(x) = k \, H_{k-1}(x)$

so $H_k''(x) - x H_k'(x) = k(k-1) H_{k-2}(x) - x \cdot k H_{k-1}(x)$,
and the recurrence collapses this to $-k H_k(x)$. Both identities
are in Mathlib's `Polynomial.hermite` API
(`hermite_succ`, `derivative_hermite`).

**Reference:** Janson, *Gaussian Hilbert Spaces*, Theorem 4.4. -/
axiom ouGenerator1D_hermiteEval (k : ℕ) (x : ℝ) :
    ouGenerator1D (hermiteEval k) x = -(k : ℝ) * hermiteEval k x

/-- **Multivariate Hermite polynomials are OU eigenfunctions:**
`L H_α = -|α| · H_α`.

**Proof strategy:** $L = \sum_i L_i$ where $L_i$ acts only on the
$i$-th coordinate. Since $H_\alpha(x) = \prod_j H_{\alpha_j}(x_j)$,
$L_i H_\alpha$ multiplies through to $-\alpha_i \cdot H_\alpha$. Sum
over $i$ gives $-|\alpha| \cdot H_\alpha$. The 1D base case is
`ouGenerator1D_hermiteEval` above. -/
axiom ouGenerator_hermiteMultiEval {n : ℕ} (α : Fin n → ℕ)
    (x : Fin n → ℝ) :
    ouGenerator n (hermiteMultiEval α) x =
      -(MultiIndex.totalDegree α : ℝ) * hermiteMultiEval α x

/-- **The OU semigroup acts on $\mathcal H_k$ by $e^{-kt}$.**

The OU semigroup $T_t$ on $L^2(\gamma_n)$ commutes with the spectral
decomposition into Wiener chaos: each chaos $\mathcal H_k$ is
$T_t$-invariant, and $T_t$ restricts to multiplication by $e^{-kt}$
on it.

This is the semigroup-level reformulation of the eigenfunction
identity above. The connection: $T_t = e^{tL}$, so on the eigenspace
of $L$ with eigenvalue $-k$, $T_t$ is multiplication by $e^{-kt}$.

**Reference:** Janson, *Gaussian Hilbert Spaces*, Theorem 4.4 +
the OU semigroup's L²-spectral-resolution. Bakry-Gentil-Ledoux §2.7.

**Status note:** depends on the OU semigroup definition in
`Diffusion/OrnsteinUhlenbeck.lean` being filled in. Currently that
file is a docstring skeleton; this axiom is the natural target once
the OU semigroup is concretely available. -/
axiom ouSemigroup_act_wienerChaos {n : ℕ} (k : ℕ) (t : ℝ) (_ht : 0 ≤ t)
    (f : MeasureTheory.Lp ℝ 2 (stdGaussianFin n))
    (_hf : f ∈ wienerChaos n k) :
    True
    -- TARGET (after OU is concrete):
    -- OUSemigroup.act t f = Real.exp (-k * t) • f

end MarkovSemigroups.Gaussian
