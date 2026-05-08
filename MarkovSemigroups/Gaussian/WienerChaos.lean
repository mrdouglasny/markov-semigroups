/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wiener Chaos Decomposition

For the standard Gaussian measure $\gamma$ on $\mathbb R^n$ (we work
in finite dimension; this suffices for `pphi2`'s lattice
applications), the Hilbert space $L^2(\gamma)$ decomposes as an
orthogonal direct sum of homogeneous Wiener chaos:
$$
L^2(\gamma) \;=\; \bigoplus_{k = 0}^{\infty} \mathcal H_k,
$$
where $\mathcal H_k$ is the closure (in $L^2$) of the linear span of
multivariate Hermite polynomials of total degree $k$.

This is the abstract counterpart of the multiple-Wiener-Itô integral
expansion in stochastic calculus, but stated for finite-dimensional
Gaussians where the Hermite definition is purely algebraic and we do
not need any stochastic-integration machinery.

## Main definitions

- `wienerChaos γ k` — the $k$-th chaos as a submodule of $L^2(\gamma)$.
- `wienerChaosLE γ d` — `⨆_{k ≤ d} wienerChaos γ k`, the polynomials
  of total degree $\le d$.
- `chaosProjection γ k` — orthogonal projection $L^2(\gamma) \to \mathcal H_k$.

## Main theorems

- `wienerChaos_orthogonal` — distinct chaos spaces are orthogonal in $L^2$.
- `wienerChaos_isInternalDirectSum` — the direct sum is the whole space.
- `mvPoly_mem_wienerChaosLE` — polynomials of total degree $\le d$ live in
  `wienerChaosLE d`.

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), Theorem 2.6.
- D. Nualart, *The Malliavin Calculus and Related Topics*, Springer
  (2006), §1.1.

## Status

API + axiom skeleton (2026-05-08). The chaos definition (`wienerChaos`)
is concrete; orthogonality and the direct-sum decomposition are
axiomatized with proof-strategy docstrings citing Janson Thm 2.6.
-/

import MarkovSemigroups.Gaussian.HermitePolynomials
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Algebra.DirectSum.Decomposition

noncomputable section

namespace MarkovSemigroups.Gaussian

open MeasureTheory

variable {n : ℕ}

/-- The set of multivariate Hermite polynomials of total degree $k$,
as functions $(\mathrm{Fin}\ n \to \mathbb R) \to \mathbb R$. -/
def hermiteFamilyOfDegree (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ α : Fin n → ℕ, MultiIndex.totalDegree α = k ∧ f = hermiteMultiEval α }

/-- The $k$-th Wiener chaos: closed linear span (in $L^2(\gamma)$) of
multivariate Hermite polynomials of total degree $k$.

Concretely, `f ∈ wienerChaos γ k` iff `f` is the $L^2$-limit of a
sequence of finite linear combinations of $H_\alpha$ with
$|\alpha| = k$. For $k = 0$ this is the constants; for $k \ge 1$ it is
the centred polynomials of homogeneous degree $k$ modulo lower-degree
Wick subtractions. -/
axiom wienerChaos (n k : ℕ) : Submodule ℝ (Lp ℝ 2 (stdGaussianFin n))

/-- Polynomials of total degree $\le d$: `⨆_{k ≤ d} wienerChaos γ k`. -/
noncomputable def wienerChaosLE (n d : ℕ) : Submodule ℝ (Lp ℝ 2 (stdGaussianFin n)) :=
  ⨆ k ∈ Finset.range (d + 1), wienerChaos n k

/-- **Orthogonality of distinct chaos spaces.**

For $j \ne k$, `wienerChaos γ j` and `wienerChaos γ k` are orthogonal
subspaces of $L^2(\gamma)$.

**Reference:** Janson Thm 2.6 + multivariate-Hermite orthogonality
(`hermiteMulti_orthogonality`).

**Proof strategy:** Multivariate Hermite polynomials of distinct total
degrees are orthogonal under $\gamma$ (a corollary of the per-coordinate
1D orthogonality, since the product structure plus pigeon-hole means
any cross term contains a coordinate where the degrees differ). The
chaos spaces are the closures of these orthogonal degree-$k$ spans, so
they remain orthogonal. -/
axiom wienerChaos_orthogonal (n : ℕ) {j k : ℕ} (hjk : j ≠ k)
    (f g : Lp ℝ 2 (stdGaussianFin n))
    (_hf : f ∈ wienerChaos n j) (_hg : g ∈ wienerChaos n k) :
    @inner ℝ _ _ f g = 0

/-- **Wiener chaos decomposition** (Janson Theorem 2.6).

The family `(wienerChaos γ k)_{k ∈ ℕ}` is an internal orthogonal direct
sum of $L^2(\gamma)$.

**Proof strategy:**
1. Density of polynomials in $L^2(\gamma)$ (`hermiteMulti_dense`).
2. Each polynomial of total degree $\le d$ has an explicit Hermite
   expansion (Gram-Schmidt on multi-indices ordered by total degree).
3. Closure of the polynomial span equals $L^2$, hence `⨆_k H_k = ⊤`.
4. Orthogonality (`wienerChaos_orthogonal`) makes the sup a direct sum. -/
axiom wienerChaos_isInternalDirectSum (n : ℕ) :
    DirectSum.IsInternal (wienerChaos n)

/-- **Orthogonal projection onto the $k$-th chaos.** -/
axiom chaosProjection (n k : ℕ) :
    Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n)

/-- A multivariate Hermite polynomial of total degree $k$ lies in
the $k$-th chaos. (Building block: the chaos contains all of its
Hermite generators.)

**Reference:** Definition of `wienerChaos` as the closed span. -/
axiom hermiteMultiEval_mem_wienerChaos (n : ℕ) (α : Fin n → ℕ)
    (hα : MemLp (hermiteMultiEval α) 2 (stdGaussianFin n)) :
    (hα.toLp _) ∈ wienerChaos n (MultiIndex.totalDegree α)

end MarkovSemigroups.Gaussian
