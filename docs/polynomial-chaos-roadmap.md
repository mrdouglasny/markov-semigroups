# Polynomial Chaos Concentration in markov-semigroups: Roadmap

*Drafted 2026-05-08, updated 2026-05-09. Companion to
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

## Status (2026-05-09)

**Effectively done in three weeks of wall-clock**, but the OU semigroup
action on chaos pieces still rests on 3 placeholder axioms (the underlying
Mehler-kernel infrastructure is stubbed). All four target files exist
and are sorry-free:

| File | Lines | Status |
|---|---|---|
| `Gaussian/HermitePolynomials.lean` | ~460 | **Proved**: `hermiteMulti_orthogonality`, `hermiteMulti_l2_pos`, `hermiteMulti_dense`. The density theorem rests on one external axiom in gaussian-field (`polynomial_dense_L2_of_subGaussian`, Janson Thm 2.6). |
| `Gaussian/WienerChaos.lean` | ~530 | **Proved**: `wienerChaos n k` def, `wienerChaos_orthogonal`, `chaosProjection_sum_eq_of_mem_wienerChaosLE`, full chaos arithmetic, and `wienerChaos_isHilbertSum` (the Hilbert-sum decomposition `L²(γ) = ⊕̂ₖ Hₖ`, derived from `hermiteMulti_dense` via `IsHilbertSum.mkInternal`). The legacy `wienerChaos_isInternalDirectSum` axiom statement was *strictly stronger* than the true theorem (would require finite chaos expansions) and has been replaced. |
| `Gaussian/OUEigenfunctions.lean` | ~540 | **Proved**: `ouGenerator_hermiteMultiEval` (1D + multivariate eigenfunction property `L H_α = -|α| H_α`). Three placeholder axioms remain for the OU semigroup operator (`ouSemigroupAct`) and its action on chaos pieces (`ouSemigroupAct_eq_smul_of_mem_wienerChaos`, `ouSemigroupAct_eLpNorm_hypercontractive`) — these will be discharged once `Diffusion/OrnsteinUhlenbeck.lean` is filled in. |
| `Gaussian/PolynomialChaosConcentration.lean` | ~630 | **Proved**: `bonami_nelson_chaos`, `bonami_nelson_chaosLE`, `polynomial_chaos_concentration`. Axiom footprint per `#print axioms`: the three OU placeholder axioms above (Lean built-ins aside). |

Net: the polynomial-chaos concentration theorem is in place and ready
for downstream consumption. The remaining axiom debt is (a) the
gaussian-field analytic axiom `polynomial_dense_L2_of_subGaussian`
(used by `hermiteMulti_dense` and `wienerChaos_isHilbertSum`), and
(b) the three OU-semigroup placeholder axioms in
`Gaussian/OUEigenfunctions.lean` (consumed by the Bonami-Nelson and
polynomial-chaos-concentration theorems).

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

## File layout (as built)

`MarkovSemigroups/Gaussian/`, parallel to `Diffusion/`.

### `Gaussian/HermitePolynomials.lean` — multivariate Hermite

```lean
/-- Evaluation of the 1D probabilist's Hermite polynomial at a real point. -/
noncomputable def hermiteEval (k : ℕ) (x : ℝ) : ℝ

/-- Multivariate Hermite evaluated at `x : Fin n → ℝ`: H_α(x) = ∏ᵢ H_{αᵢ}(xᵢ). -/
noncomputable def hermiteMultiEval {n : ℕ} (α : Fin n → ℕ) (x : Fin n → ℝ) : ℝ

/-- Total degree of a multi-index. -/
def MultiIndex.totalDegree {n : ℕ} (α : Fin n → ℕ) : ℕ := ∑ i, α i

/-- Standard product Gaussian on `Fin n → ℝ`. -/
noncomputable def stdGaussianFin (n : ℕ) : Measure (Fin n → ℝ)

/-- **Orthogonality of multivariate Hermite under the standard Gaussian.** -/
theorem hermiteMulti_orthogonality {n : ℕ} (α β : Fin n → ℕ) :
    ∫ x : Fin n → ℝ, hermiteMultiEval α x * hermiteMultiEval β x ∂(stdGaussianFin n) =
      if α = β then ((∏ i, (α i).factorial : ℕ) : ℝ) else 0

/-- **Density of multivariate Hermite polynomials in L²(γ).** -/
theorem hermiteMulti_dense {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 (stdGaussianFin n)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℝ),
      (∫ x, |f x - ∑ α ∈ s, c α * hermiteMultiEval α x| ^ 2 ∂(stdGaussianFin n)) < ε
```

The orthogonality reduces to the 1D case via Fubini on the pi-measure
plus the gaussian-field identity `wickMonomial_inner_gaussianReal_one`.
The density is the algebraic combination of `polynomial_dense_L2_of_subGaussian`
(textbook axiom, gaussian-field) and a `Submodule.span`-based change of basis
between multivariate monomials and multivariate Hermite (proved here, ~300
lines of `MvPolynomial.induction_on` + Hermite three-term recurrence).

### `Gaussian/WienerChaos.lean` — chaos decomposition

```lean
/-- The k-th Wiener chaos: closure of degree-k Hermite polynomials in L². -/
def wienerChaos (n k : ℕ) : Submodule ℝ (Lp ℝ 2 (stdGaussianFin n))

/-- Polynomials of total degree ≤ d. -/
noncomputable def wienerChaosLE (n d : ℕ) : Submodule ℝ (Lp ℝ 2 (stdGaussianFin n))

/-- Orthogonal projection L² → H_k. -/
noncomputable def chaosProjection (n k : ℕ) :
    Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n)

/-- Distinct chaos spaces are orthogonal. -/
theorem wienerChaos_orthogonal (n : ℕ) {j k : ℕ} (hjk : j ≠ k) ...

/-- Hilbert-sum decomposition L²(γ) = ⊕̂ₖ Hₖ (proved from `hermiteMulti_dense`). -/
theorem wienerChaos_isHilbertSum (n : ℕ) :
    IsHilbertSum ℝ (fun k => wienerChaos n k) (fun k => (wienerChaos n k).subtypeₗᵢ)

/-- Sum decomposition F = ∑_{k ≤ d} P_k F for F ∈ wienerChaosLE. -/
theorem chaosProjection_sum_eq_of_mem_wienerChaosLE (n d : ℕ)
    (F : Lp ℝ 2 (stdGaussianFin n)) (hF : F ∈ wienerChaosLE n d) :
    F = ∑ k ∈ Finset.range (d + 1), chaosProjection n k F
```

### `Gaussian/OUEigenfunctions.lean` — H_k as eigenspace of L

```lean
/-- The OU generator L = Δ - x · ∇. -/
noncomputable def ouGenerator (n : ℕ) (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ

/-- **Hermite polynomials are OU eigenfunctions.** L H_α = -|α| H_α. -/
theorem ouGenerator_hermiteMultiEval {n : ℕ} (α : Fin n → ℕ) :
    ouGenerator n (hermiteMultiEval α) =
      fun x => -(MultiIndex.totalDegree α : ℝ) * hermiteMultiEval α x

/-- **The OU semigroup operator** (placeholder; awaits Mehler-kernel infrastructure). -/
axiom ouSemigroupAct (n : ℕ) (t : ℝ) :
    Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n)

/-- **OU acts on H_k by e^{-kt}** (placeholder; will be a theorem from Mehler). -/
axiom ouSemigroupAct_eq_smul_of_mem_wienerChaos {n : ℕ} (k : ℕ)
    (t : ℝ) (_ht : 0 ≤ t) (f : Lp ℝ 2 (stdGaussianFin n))
    (_hf : f ∈ wienerChaos n k) :
    ouSemigroupAct n t f = Real.exp (-(k : ℝ) * t) • f

/-- **Nelson hypercontractive bound** ‖T_t f‖_{L^p} ≤ ‖f‖_{L^2} for e^{2t} ≥ p-1. -/
axiom ouSemigroupAct_eLpNorm_hypercontractive ...
```

The eigenfunction theorem `ouGenerator_hermiteMultiEval` is proved (1D
algebraic recurrence + Finset-product calculus on the multivariate
gradient/Laplacian). The three remaining axioms are placeholder for the
full Mehler/OU machinery; their discharge is the principal remaining
work item (see "Remaining work" below).

### `Gaussian/PolynomialChaosConcentration.lean` — Janson 5.10

```lean
/-- **Bonami-Nelson L^p bound on chaos.** ‖f‖_{L^p} ≤ (p-1)^{k/2} · ‖f‖_{L²}. -/
theorem bonami_nelson_chaos (n k : ℕ) ... : ...

/-- **L^p bound on H^{≤d}.** -/
theorem bonami_nelson_chaosLE (n d : ℕ) ... : ...

/-- **Polynomial chaos concentration (Janson Thm 5.10).** -/
theorem polynomial_chaos_concentration (n d : ℕ) (hd : 1 ≤ d) :
    ∃ c_d : ℝ, 0 < c_d ∧ ∀ (F : Lp ℝ 2 (stdGaussianFin n)),
      F ∈ wienerChaosLE n d → ⟪F, 1⟫ = 0 → ∀ lam : ℝ, 0 < lam →
        (stdGaussianFin n) {x | lam * ‖F‖₂ < |F x|} ≤
          2 * ENNReal.ofReal (Real.exp (-c_d * lam ^ ((2 : ℝ) / d)))
```

`#print axioms polynomial_chaos_concentration` shows: the three OU
placeholder axioms above (plus Lean built-ins). Once those are
discharged, the chain back to `polynomial_dense_L2_of_subGaussian` is
the only remaining textbook axiom in the polynomial-chaos pipeline.

## Dependencies

External (Mathlib):
- `Mathlib.RingTheory.Polynomial.Hermite.{Basic,Gaussian}` — 1D Hermite + Rodrigues.
- `Mathlib.Algebra.MvPolynomial.*` — multivariate polynomials.
- `Mathlib.MeasureTheory.Function.{LpSpace,L2Space}` — L^p / L².
- `Mathlib.Probability.Distributions.Gaussian.{Real,Multivariate,Fernique}`
  — standard Gaussian + Fernique's theorem (used for the sub-Gaussian
  instance in gaussian-field).
- `Mathlib.Analysis.InnerProductSpace.{l2Space,Projection.FiniteDimensional}`
  — Hilbert-sum decompositions, orthogonal projections.

External (gaussian-field):
- `GeneralResults/PolynomialDensityGaussian.lean` (added 2026-05-09):
  `IsSubGaussianMeasure`, `polynomial_dense_L2_of_subGaussian` axiom,
  `isSubGaussianMeasure_pi_gaussianReal` proved from Mathlib's
  `IsGaussian.exists_integrable_exp_sq` (Fernique).
- `SchwartzNuclear/HermiteWick.lean`: 1D Wick orthogonality
  `wickMonomial_inner_gaussianReal_one` (used in `hermiteMulti_orthogonality`).
- `GaussianField/WickMultivariate.lean`: multivariate Wick / Hermite
  bridge (used in earlier proof iterations; now mostly subsumed).

Internal (markov-semigroups):
- `Abstract/Hypercontractivity.lean` — `IsHypercontractive`, Gross's
  equivalence (LSI ↔ HC), abstract `semigroup_lp_improvement`. Used
  by `bonami_nelson_chaos`.
- `Diffusion/OrnsteinUhlenbeck.lean` — **still a 45-line skeleton.** The
  three placeholder axioms in `Gaussian/OUEigenfunctions.lean` will be
  discharged here once the Mehler-kernel definition + L²-contraction
  + hypercontractivity proof are filled in. This is multi-week work
  (Mehler-kernel measure-theory is the heaviest chunk).

## Remaining work

Two discrete items:

1. **Fill in `Diffusion/OrnsteinUhlenbeck.lean`** with the OU semigroup,
   Mehler-kernel formula `(T_t f)(x) = ∫ f(e^{-t}x + √(1-e^{-2t}) y) dγ(y)`,
   L²-contraction, and hypercontractivity. **Multi-week** — this is the
   heaviest measure-theory item in the project. Discharges
   `ouSemigroupAct` and `ouSemigroupAct_eq_smul_of_mem_wienerChaos`.

2. **Bonami-Nelson hypercontractivity proof** (`ouSemigroupAct_eLpNorm_hypercontractive`),
   either as a corollary of (1) + Gross's theorem (the abstract
   `Abstract/Hypercontractivity.gross_lsi_implies_hypercontractive` axiom
   already in the project), or directly via Nelson's two-point + tensorization
   argument. **3-5 days** once (1) is in place.

The polynomial-chaos pipeline currently rests on (a) one external
axiom (`polynomial_dense_L2_of_subGaussian` in gaussian-field) and (b)
three OU-side axioms whose discharge is gated on (1)/(2). After (1)+(2)
the whole pipeline rests on the single gaussian-field analytic axiom.

## What this unlocked beyond pphi2 Cluster A

- **pphi2N** (O(N) sigma model): the same polynomial-chaos concentration
  applies to vector-valued Wick polynomials.
- **Phase 4** of pphi2 (`pphi2_nontriviality`,
  `continuumLimit_nonGaussian`): uses the same dynamical-cutoff machinery.
- **Janson Theorem 5.10 in Mathlib**: a substantial probability-library
  contribution in its own right, currently not available upstream.
- **Stein's method / Malliavin calculus** future work: the Wiener chaos
  decomposition is a prerequisite for both.
