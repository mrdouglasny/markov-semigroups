# Polynomial Chaos Concentration in markov-semigroups: Roadmap

*Drafted 2026-05-08. Companion to
[`pphi2/docs/polynomial-chaos-concentration.md`](https://github.com/mrdouglasny/pphi2/blob/main/docs/polynomial-chaos-concentration.md)
which states the goal and gives the full proof sketch + references. This
file is the markov-semigroups-side implementation roadmap: concrete file
layout, theorem statements, and dependencies.*

## Goal

Land the abstract theorem (Janson, *Gaussian Hilbert Spaces*, Thm 5.10):

> For $F \in \mathcal H^{\le d}$ (a polynomial of total degree $\le d$ in
> a centered Gaussian process) with $\mathbb E F = 0$, there is a
> universal $c_d > 0$ such that
> $\mathbb P(|F| > \lambda \|F\|_{L^2}) \le 2 \exp(-c_d \, \lambda^{2/d})$.

Equivalent Bonami-Nelson L^p form:
$\|F\|_{L^p} \le (p-1)^{d/2} \|F\|_{L^2}$ for $p \ge 2$.

The downstream consumer is `pphi2`'s Cluster A (4 axioms reducing to the
Glimm-Jaffe Ch. 8 dynamical-cutoff Nelson estimate).

## Strategy: finite-dim Hermite, no stochastic calculus

Per Gemini's pass-2 advisory: the lattice approximation in pphi2 keeps
everything finite-dimensional, so we **avoid Wiener-Ito multiple
integrals** and define $\mathcal H_k$ algebraically via multivariate
Hermite polynomials. Specifically:

1. Define multivariate (probabilist's) Hermite polynomials
   $H_\alpha(x) = \prod_i H_{\alpha_i}(x_i)$ for multi-indices
   $\alpha \in \mathbb N^n$.
2. Identify $\mathcal H_k$ with the span of $\{H_\alpha : |\alpha| = k\}$
   under any orthonormal basis of the Gaussian Hilbert space.
3. Prove the OU eigenfunction property $L H_\alpha = -|\alpha| H_\alpha$
   by direct algebraic computation on the generator $L = \Delta - x \cdot \nabla$.
4. Derive Bonami-Nelson on $\mathcal H_k$ from the OU eigenfunction
   property + the abstract hypercontractivity bound already in
   `Abstract/Hypercontractivity.lean`.

This bypasses spectral-theorem machinery for unbounded operators on
$L^2(\gamma_C)$.

## File layout

A new directory `MarkovSemigroups/Gaussian/` parallel to
`Diffusion/`, holding four files. Each file's main theorems are listed
with their core dependencies on Mathlib + existing markov-semigroups.

### `Gaussian/HermitePolynomials.lean` — multivariate Hermite

Builds on Mathlib's `Polynomial.hermite : ℕ → Polynomial ℤ` (1D).

```lean
/-- Multivariate Hermite polynomial for a finite multi-index. -/
noncomputable def hermiteMulti {n : ℕ} (α : Fin n → ℕ) : MvPolynomial (Fin n) ℝ

/-- Evaluating a multivariate Hermite at a Gaussian-distributed point. -/
noncomputable def hermiteMultiEval {n : ℕ} (α : Fin n → ℕ) (x : Fin n → ℝ) : ℝ

/-- Total degree of a multi-index. -/
def MultiIndex.totalDegree {n : ℕ} (α : Fin n → ℕ) : ℕ := ∑ i, α i

/-- **Orthogonality of multivariate Hermite under the standard Gaussian.**
    `∫ H_α(x) H_β(x) dγ(x) = δ_{αβ} · ∏_i α_i!` -/
theorem hermiteMulti_orthogonality {n : ℕ} (α β : Fin n → ℕ) :
    ∫ x : Fin n → ℝ, hermiteMultiEval α x * hermiteMultiEval β x ∂stdGaussianℝⁿ n =
      if α = β then ∏ i, (α i).factorial else 0
```

Approximate length: 200-300 lines. Heavy on Mathlib's `MvPolynomial` and
`Polynomial.hermite` infrastructure; the orthogonality reduces to the 1D
case via Fubini on independent components.

### `Gaussian/WienerChaos.lean` — chaos decomposition

```lean
/-- The k-th Wiener chaos: closure of degree-k Hermite polynomials in L². -/
noncomputable def wienerChaos {n : ℕ} (γ : Measure (Fin n → ℝ)) (k : ℕ) :
    Submodule ℝ (Lp ℝ 2 γ)

/-- Chaos decomposition: `L²(γ) = ⊕_k H_k`. -/
theorem wienerChaos_isInternalDirectSum {n : ℕ} (γ : Measure (Fin n → ℝ))
    [IsStandardGaussian γ] :
    DirectSum.IsInternal (wienerChaos γ : ℕ → Submodule ℝ (Lp ℝ 2 γ))

/-- Polynomials of total degree ≤ d span `⊕_{k ≤ d} H_k`. -/
theorem mem_wienerChaosLE {n : ℕ} (γ : Measure (Fin n → ℝ)) (d : ℕ)
    (P : MvPolynomial (Fin n) ℝ) (hP : P.totalDegree ≤ d) :
    (P.eval) ∈ ⨆ k ∈ Finset.range (d + 1), wienerChaos γ k
```

Approximate length: 200-300 lines. The completeness of Hermite polynomials
in $L^2(\gamma)$ follows from density of polynomials (Mathlib has this
for the standard Gaussian on ℝ; multivariate uses Fubini).

### `Gaussian/OUEigenfunctions.lean` — H_k as eigenspace of L

```lean
/-- The OU generator `L = Δ - x · ∇` acting on smooth functions. -/
noncomputable def ouGenerator {n : ℕ} : (((Fin n → ℝ) → ℝ) → (Fin n → ℝ) → ℝ)

/-- **Hermite polynomials are eigenfunctions of the OU generator.**
    For multi-index α with |α| = k: `L H_α = -k · H_α`. -/
theorem ouGenerator_hermiteMulti {n : ℕ} (α : Fin n → ℕ) :
    ouGenerator (hermiteMultiEval α) = fun x =>
      (- (MultiIndex.totalDegree α : ℝ)) * hermiteMultiEval α x

/-- The OU semigroup acts on `H_k` by multiplication by `e^{-kt}`. -/
theorem ouSemigroup_wienerChaos {n : ℕ} (γ : Measure (Fin n → ℝ))
    [IsStandardGaussian γ] (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 γ) (hf : f ∈ wienerChaos γ k) :
    OUSemigroup.act t f = Real.exp (-k * t) • f
```

Approximate length: 150-250 lines. The eigenfunction calculation is a
direct expansion: $L H_\alpha = \sum_i (\partial_{x_i}^2 - x_i \partial_{x_i}) H_\alpha$,
each summand contributes $-\alpha_i H_\alpha$ via the 1D recurrence.

### `Gaussian/PolynomialChaosConcentration.lean` — the Janson 5.10 theorem

```lean
/-- **Bonami-Nelson L^p bound on chaos.** For `f ∈ H_k`, `p ≥ 2`:
    `‖f‖_{L^p} ≤ (p - 1)^{k/2} · ‖f‖_{L²}`. -/
theorem bonami_nelson_chaos {n : ℕ} (γ : Measure (Fin n → ℝ))
    [IsStandardGaussian γ] (k : ℕ) (f : Lp ℝ 2 γ) (hf : f ∈ wienerChaos γ k)
    (p : ℝ) (hp : 2 ≤ p) :
    ‖f‖_{L^p γ} ≤ (p - 1) ^ (k / 2 : ℝ) * ‖f‖_{L^2 γ}

/-- **L^p bound on `H^{≤d}`.** Triangle inequality across `k = 0, …, d`. -/
theorem bonami_nelson_chaosLE {n : ℕ} (γ : Measure (Fin n → ℝ))
    [IsStandardGaussian γ] (d : ℕ) (f : Lp ℝ 2 γ)
    (hf : f ∈ ⨆ k ∈ Finset.range (d + 1), wienerChaos γ k)
    (p : ℝ) (hp : 2 ≤ p) :
    ‖f‖_{L^p γ} ≤ (d + 1) * (p - 1) ^ (d / 2 : ℝ) * ‖f‖_{L^2 γ}

/-- **Polynomial chaos concentration (Janson Thm 5.10).**
    For centered `F ∈ H^{≤d}`, λ > 0:
    `P(|F| > λ ‖F‖_{L²}) ≤ 2 exp(- c_d · λ^{2/d})` for some universal c_d > 0. -/
theorem polynomial_chaos_concentration {n : ℕ} (γ : Measure (Fin n → ℝ))
    [IsStandardGaussian γ] (d : ℕ) (hd : 0 < d) :
    ∃ c_d : ℝ, 0 < c_d ∧ ∀ (F : Lp ℝ 2 γ),
      F ∈ ⨆ k ∈ Finset.range (d + 1), wienerChaos γ k →
      ∫ x, F x ∂γ = 0 →
      ∀ (lam : ℝ), 0 < lam →
        γ {x | lam * ‖F‖_{L^2 γ} < |F x|} ≤
          2 * ENNReal.ofReal (Real.exp (- c_d * lam ^ ((2 : ℝ) / d)))
```

Approximate length: 100-200 lines. The proof is the three-line Markov +
optimize argument from §3 of the pphi2 doc.

## Dependencies

External (Mathlib):
- `Mathlib.RingTheory.Polynomial.Hermite.Basic` — 1D Hermite.
- `Mathlib.RingTheory.Polynomial.Hermite.Gaussian` — Rodrigues formula.
- `Mathlib.Algebra.MvPolynomial.*` — multivariate polynomials.
- `Mathlib.MeasureTheory.Function.LpSpace` — $L^p$ spaces.
- `Mathlib.Probability.Distributions.Gaussian` — standard Gaussian
  measure (1D and tensor-product).

Internal (markov-semigroups):
- `Abstract/Hypercontractivity.lean` — `IsHypercontractive` definition,
  Gross's equivalence (LSI ↔ HC), abstract `semigroup_lp_improvement`.
- `Diffusion/OrnsteinUhlenbeck.lean` — currently a 45-line skeleton with
  Mehler's formula in the docstring. Will need to be filled in with the
  actual `OUSemigroup C` definition + the contraction theorem before
  `Gaussian/OUEigenfunctions.lean` can use it.

## Order of work

1. **Fill in `Diffusion/OrnsteinUhlenbeck.lean`** (currently a docstring
   skeleton). Define `OUSemigroup C` for finite-dim covariance, prove
   Mehler's formula and L²-contraction. ~3-5 days.
2. **`Gaussian/HermitePolynomials.lean`** — multivariate Hermite +
   orthogonality. ~3-5 days.
3. **`Gaussian/WienerChaos.lean`** — chaos decomposition. ~3-5 days.
4. **`Gaussian/OUEigenfunctions.lean`** — eigenfunction property +
   semigroup action by $e^{-kt}$. ~2-3 days. The bottleneck is the
   eigenfunction calculation, which is direct algebra but requires care
   with the multi-index combinatorics.
5. **`Gaussian/PolynomialChaosConcentration.lean`** — Bonami-Nelson +
   Janson 5.10. ~3-5 days.

Total in markov-semigroups: ~3 weeks.

After this, the `pphi2/NelsonEstimate/` rewiring (replacing the
`True`-stub theorems in `RoughErrorBound.lean`, then doing the dynamical
cutoff in `NelsonEstimate.lean`) is a separate effort estimated at 2-3
weeks per the pphi2 roadmap — so the total Cluster A timeline is 5-6
weeks, comfortably inside Gemini's 6-8 week estimate.

## Risks and exit ramps

- If multivariate Hermite orthogonality (step 2) takes longer than 5 days
  due to MvPolynomial / Fubini friction, consider stating it as an axiom
  with literature citation (Janson §5.1) and unblock downstream work.
- If the OU eigenfunction calculation (step 4) hits unexpected
  integration-by-parts issues, the 1D OU + tensor product gives a
  cleaner factored proof; switching to that approach mid-stream is
  cheap.
- The Mehler-formula proof in step 1 is the most measure-theory-heavy
  step. If it stalls, the Markov-semigroup contraction can be proved
  abstractly via the existing `Abstract/Hypercontractivity` framework
  without going through Mehler.

## What this unlocks beyond pphi2 Cluster A

- **pphi2N** (O(N) sigma model): the same polynomial-chaos concentration
  applies to vector-valued Wick polynomials.
- **Phase 4** of pphi2 (`pphi2_nontriviality`,
  `continuumLimit_nonGaussian`): the genuine non-Gaussian discharges
  need the same dynamical-cutoff machinery.
- **Janson Theorem 5.10 in Mathlib**: a substantial probability-library
  contribution in its own right, currently not available upstream.
- **Stein's method / Malliavin calculus** future work: the Wiener chaos
  decomposition is the prerequisite for both.
