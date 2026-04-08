# Plan: Filling Brascamp-Lieb Sorry's

Status: 3 sorry's remaining after `ffb9f1f`

## Priority Ordering

1. **Sorry 3 (Integrability)** — needed for the RHS integral to exist
2. **Sorry 2 (Smoothness)** — needed for IBP in the main proof
3. **Sorry 1 (Core theorem)** — combines everything

---

## Sorry 3: Integrability (Low-Medium difficulty)

**Goal:** `Integrable (fun x => (fderiv ℝ f x) (g x)) m.μ`
where `g x = (Hess V x)⁻¹ (∇f x)`.

### Strategy
Use `Integrable.mono` with the pointwise bound already proven in
`pointwise_hessian_bound`:

```
(∇f(x))(g(x)) ≤ (1/ρ) ‖∇f(x)‖²
```

Since `(1/ρ) ‖∇f‖²` is integrable by hypothesis (`hf_grad_int`),
and the integrand is nonneg (from Hessian positive definiteness),
we get integrability.

### Key Mathlib lemmas
- `Integrable.mono` — domination by integrable function
- `Integrable.const_mul` — for `(1/ρ) * ‖∇f‖²`
- `AEStronglyMeasurable` — need measurability of the integrand
  (follows from `ContDiff` of f and g)

### Intermediate lemmas needed
- Measurability of `fun x => (fderiv ℝ f x) (g x)` — should follow
  from continuity (C¹ functions are continuous, composition of
  continuous functions is measurable)
- Nonneg bound: `0 ≤ (fderiv ℝ f x) (g x)` from the Hessian positive
  definiteness (already essentially proven in `pointwise_hessian_bound`)

### Blocker
The `AEStronglyMeasurable` side goal. Need to show that the composition
of `fderiv ℝ f` and `g` is measurable. Should follow from continuity
of C¹ functions but may require finding the right Mathlib path.

---

## Sorry 2: Smoothness of Hessian inverse (Medium difficulty)

**Goal:** `ContDiff ℝ 1 g` where `g x = (Hess V x)⁻¹ (∇f x)`.

### Strategy
Decompose as composition of smooth maps:
1. `x ↦ Hess V(x)` — C⁰ if V is C² (C^k if V is C^{k+2})
2. `A ↦ A⁻¹` — smooth on invertible operators
3. `x ↦ ∇f(x)` — C⁰ if f is C¹ (C^k if f is C^{k+1})
4. `(A, v) ↦ A v` — bilinear, hence smooth

Apply chain rule: `ContDiff.comp`.

### Key Mathlib lemmas
- `contDiffOn_inv` or `ContDiff.inverse` — smoothness of operator
  inversion on the open set of invertible operators
- `ContDiff.comp` — chain rule for `ContDiff`
- `ContDiff.prod` — build pairs
- `ContinuousLinearMap.contDiff_eval` or `ContDiff.clm_apply` — for
  the application map `(A, v) ↦ A v`
- `LinearMap.toContinuousLinearMap` — finite-dim equivalence

### Intermediate lemmas needed
- Show `Hess V(x)` is always in the domain of `contDiffOn_inv`
  (i.e., always invertible) — follows from positive definiteness
  via `hessian_injective` + `hessian_surjective` (already proven)
- May need to strengthen V to C³ and f to C² for g to be C¹

### Blocker
Need to check if Mathlib v4.29.0 has `contDiffOn_inv` for
`ContinuousLinearMap`. If not available, may need to go through
matrices and Cramer's rule. Also the type-juggling between
`E →L[ℝ] (E →L[ℝ] ℝ)` and invertible operators on E could be tricky.

---

## Sorry 1: Core Brascamp-Lieb (High difficulty)

**Goal:**
```
m.variance f ≤ ∫ x, (fderiv ℝ f x) (g x) ∂m.μ
```

### Strategy (BGL Prop 4.9.1, via Bochner identity)

**Step 1.** Center: let f̄ = f - μ(f), so Var = ∫ f̄² dμ.

**Step 2.** Weighted IBP for μ = e^{-V} dx:
```
∫ ⟨∇u, ∇v⟩ dμ = ∫ u · (-Lv) dμ
```
where L = Δ - ⟨∇V, ∇·⟩ is the Witten Laplacian.

**Step 3.** Bochner identity for L:
```
∫ (Lφ)² dμ = ∫ ‖Hess φ‖² dμ + ∫ ⟨Hess V · ∇φ, ∇φ⟩ dμ
```

**Step 4.** Cauchy-Schwarz with weight (Hess V)^{1/2}:
```
∫ ⟨∇f, ∇φ⟩ dμ ≤ (∫ ⟨(Hess V)⁻¹ ∇f, ∇f⟩ dμ)^{1/2} · (∫ ⟨Hess V · ∇φ, ∇φ⟩ dμ)^{1/2}
```

**Step 5.** Combine: from Bochner, ∫ ⟨Hess V · ∇φ, ∇φ⟩ dμ ≤ ∫ (Lφ)² dμ.
So ∫ f̄ · (-Lφ) dμ ≤ I(f)^{1/2} · (∫ (Lφ)² dμ)^{1/2}.

**Step 6.** Variational argument: take sup over h = -Lφ with ∫h²dμ = 1
gives (Var f)^{1/2} ≤ I(f)^{1/2}, hence Var f ≤ I(f).

### Key Mathlib lemmas
- `MeasureTheory.integral_divergence` — divergence theorem
- `MeasureTheory.integral_inner_le_sqrt_integral_norm_sq` — integral
  Cauchy-Schwarz
- `Mathlib.Analysis.Calculus.Hessian` — Hessian definition
- `Mathlib.Analysis.InnerProductSpace.Gradient` — gradient/nabla

### Intermediate lemmas needed (in order)

1. **Weighted IBP** (`weighted_ibp`):
   ```
   ∫ ⟨∇u, ∇v⟩ dμ = -∫ u · (Δv - ⟨∇V, ∇v⟩) dμ
   ```
   This is the most important helper. Proof: expand using
   ∫ ⟨∇u, ∇v⟩ e^{-V} dx, apply standard divergence theorem,
   compute the boundary term (vanishes for Schwartz-class functions).

2. **Bochner identity** (`bochner_weighted`):
   ```
   ∫ (Lφ)² dμ = ∫ ‖Hess φ‖² dμ + ∫ ⟨Hess V · ∇φ, ∇φ⟩ dμ
   ```
   Proof: long calculation using weighted IBP multiple times.
   This is the main technical challenge.

3. **Integral Cauchy-Schwarz** with weighted inner product.

### Alternative approach
Instead of the Bochner identity route, consider:
- **Direct spectral approach**: In finite dimensions, L has a discrete
  spectrum. Expand f in eigenfunctions of L, compute Var directly.
  This avoids Bochner but requires spectral theory for L.
- **Semigroup interpolation**: Use the OU semigroup e^{tL}.
  Already partially set up via `BakryEmerySpace`.

### Blockers
1. Weighted IBP is not in Mathlib — must be built from scratch
   using the divergence theorem + density computation.
2. Bochner identity is a long, error-prone calculation.
3. The variational/density argument (Step 6) requires showing that
   the range of -L is dense in L²₀(μ), which needs spectral theory.

### Possible simplification
For the finite-dimensional case, one could avoid the variational
argument entirely by directly solving -Lφ = f̄ (which exists because
L has a spectral gap from strict convexity). This requires:
- Lax-Milgram or spectral theorem for self-adjoint operators on
  finite-dimensional Hilbert spaces (available in Mathlib)
- Show L has trivial kernel on mean-zero functions

---

## Summary

| Sorry | Difficulty | Estimated effort | Dependencies |
|-------|-----------|-----------------|-------------|
| 3 (Integrability) | Low-Medium | 1-2 days | measurability of C¹ compositions |
| 2 (Smoothness) | Medium | 2-4 days | `contDiffOn_inv`, type juggling |
| 1 (Core theorem) | High | 1-3 weeks | weighted IBP, Bochner identity |

Total: ~2-4 weeks of focused work.
