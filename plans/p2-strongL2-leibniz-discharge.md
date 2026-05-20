# Discharge plan: `hasDerivWithinAt_integral_of_strongL2Deriv`

The P2 Leibniz kernel — the single remaining genuinely-new analytic
content in the Route A discharge of `gross_lsi_implies_hypercontractive`.
Lives in `MarkovSemigroups/Abstract/GrossODE.lean`; stated with no
project definitions so it is Mathlib-upstream-ready once proved.

**Status (2026-05-19):** statement *patched* with a corrective
hypothesis (see "Lemma-as-originally-stated was false" below);
Gemini-deep-think-vetted proof plan. Body is `sorry`. To be discharged.

## Patched statement

```lean
theorem hasDerivWithinAt_integral_of_strongL2Deriv {Y : Type*}
    [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (u : ℝ → Lp ℝ 2 ν) (u' : Lp ℝ 2 ν) {s : ℝ} (hs : 0 ≤ s)
    (hu : HasDerivWithinAt u u' (Set.Ici 0) s)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (h_u_bound : ∃ M : ℝ,
        ∀ᶠ σ in 𝓝[Set.Ici 0] s, ∀ᵐ y ∂ν, |(u σ : Y → ℝ) y| ≤ M) :
    HasDerivWithinAt (fun σ => ∫ y, ψ ((u σ : Y → ℝ) y) ∂ν)
      (∫ y, deriv ψ ((u s : Y → ℝ) y) * (u' : Y → ℝ) y ∂ν)
      (Set.Ici 0) s
```

`h_u_bound` says the orbit `u_σ` is uniformly `L^∞`-bounded as `σ`
approaches `s` from within `Set.Ici 0`.

## Lemma-as-originally-stated was false (and why the patch is minimal)

The original hypothesis was `∀ y, |ψ'(u_s y)| ≤ Cψ` — bounding `ψ'`
only at `σ = s`. **Counterexample** (Gemini-deep-think 2026-05-19):
let `ν = Lebesgue [0,1]`, `v(y) = |y|^{-1/3}` (∈ `L²([0,1])`),
`u σ y = y + σ · v(y)` (smooth curve in `L²`), `ψ(x) = x⁴`. Then
`ψ'(u_0 y) = 4y³` is bounded on `[0,1]` (the old hypothesis is
satisfied with `Cψ = 4`), but for any `σ > 0` the expansion of
`ψ(u_σ y)` contains `σ⁴ · |y|^{-4/3}`, which is **not Lebesgue-
integrable**, so `F(σ) = ∫ ψ(u_σ) dν = +∞` and no derivative exists.

The intuition: the MVT/FTC segment
`u_s(y) + t · (u_σ(y) − u_s(y))`, `t ∈ [0,1]`, passes through values
on the `(y,σ)`-strip near `u_s`, not just on the curve `u_σ`. A
pointwise bound on `ψ'(u_σ y)` (even uniform in `σ`) does *not*
control `ψ'` on the intermediate segment unless the segment is a
straight line (which the `(y,σ)` strip generally is not). The clean
fix is to trap the *entire* segment in a fixed convex interval where
`ψ'` is bounded by continuity — i.e., bound `u_σ` itself uniformly in
`σ` near `s`. Then both endpoints and the interior of the MVT segment
live in `[−M, M]`, and the continuous `ψ'|_{[-M,M]}` is bounded.

This is **the minimal** Mathlib-upstream-ready strengthening that
makes the lemma both true and provable along the L²-difference-
quotient route.

## Why this is true in the Gross use-case

`grossPow_hasDerivWithinAt` invokes the kernel with
`u = (P_·) f : ℝ → Lp ℝ 2 ν` where `f` is in the abstract
`D.IsCore`. Two facts give `h_u_bound`:

1. The `IsCore` predicate carries a uniform sup-norm bound on `f`
   (typical formulation: `∃ M, ‖f‖_∞ ≤ M`; if `IsCore` doesn't
   already carry this, `CoreSemigroupInvariant` gives it via the
   `L^∞`-boundedness of `Pₜf` on the core).
2. `DirichletMarkovSemigroup.semigroup_contraction` gives
   `‖P_σ f‖_∞ ≤ ‖f‖_∞` for all `σ ≥ 0` (Markov-semigroup contraction
   on `L^∞`).

So `‖u_σ‖_∞ ≤ M` for all `σ ≥ 0`, which implies the eventually-in-σ
a.e.-in-y bound `h_u_bound` (with the same `M`). The consumer
supplies it as a few-line lemma; no new axioms.

## Proof route (Gemini deep-think 2026-05-19, vetted)

Let `F(σ) := ∫_y ψ(u_σ y) dν`. Goal:
`HasDerivWithinAt F (∫ ψ'(u_s)·u') (Set.Ici 0) s`.

### Step 1 — pointwise FTC for ψ

Since `ψ ∈ C¹`, for every `(σ, y)`:
```
ψ(u_σ y) − ψ(u_s y) = M_σ(y) · (u_σ(y) − u_s(y))
```
where `M_σ(y) := ∫_0^1 ψ'(u_s(y) + t · (u_σ(y) − u_s(y))) dt`. This
is purely 1D pointwise FTC — **no product-measure Fubini needed**
(this is a key formalization shortcut: the difference factors before
the y-integral, so no `Fubini.integral_prod` boilerplate).

### Step 2 — express the difference quotient as an L² inner product

Define `Δσ := (u_σ − u_s) / (σ − s) ∈ Lp ℝ 2 ν` (with the
`σ = s` value taken as `u'`; `hu` ensures `Δσ → u'` in `L²` as
`σ → s⁺`).

Then:
```
(F(σ) − F(s)) / (σ − s) = ∫_y M_σ(y) · Δσ(y) dν(y) = ⟪M_σ, Δσ⟫_{L²(ν)}
```

(Real inner product on `L²(ν)`; `M_σ` and `Δσ` are both in `L²` —
see Step 3 for `M_σ`.) **Second key formalization shortcut:** this is
*literally* the L² inner product. No manual `Term A / Term B` split
+ Cauchy–Schwarz is needed — instead use Mathlib's continuity of the
inner product:
`Filter.Tendsto.inner : f →ᶠ a → g →ᶠ b → ⟪f, g⟫ →ᶠ ⟪a, b⟫`.

### Step 3 — `M_σ → ψ'(u_s)` in `L²(ν)`

This is the heart. The roadmap that avoids ε-δ in metric-space hell:

3a. By `hu` and the standing `h_u_bound`, both `u_σ → u_s` in `L²`
    and `‖u_σ‖_∞ ≤ M` eventually-in-σ. From the bound: for any
    `t ∈ [0,1]`, `|u_s(y) + t·(u_σ(y) − u_s(y))| ≤ M` a.e., so by
    continuity of `ψ'`, `|ψ'(...)| ≤ K := ‖ψ'‖_{∞,[-M,M]} < ∞`.
    Hence `‖M_σ‖_∞ ≤ K` and `‖M_σ − ψ'(u_s)‖_∞ ≤ 2K`. The
    finite-measure dominator `(2K)² · 1` is `L¹(ν)`.

3b. `L² ⇒ in measure`: `u_σ → u_s` in measure
    (`MeasureTheory.tendstoInMeasure_of_tendsto_Lp`).

3c. Subsequence a.e.: for any sequence `σₙ → s` in `𝓝[≥] s`, extract
    a subsequence on which `u_{σₙ_k} → u_s` a.e.
    (`MeasureTheory.tendstoInMeasure_iff_exists_subseq_tendsto_ae` or
    a direct argument).

3d. Pointwise DCT on `t`: along that subsequence, for a.e. `y`,
    `M_{σₙ_k}(y) → ψ'(u_s(y))` (interior `t`-integral closes by
    pointwise DCT — the integrand `ψ'(u_s(y) + t · (u_{σₙ_k}(y) −
    u_s(y)))` converges to `ψ'(u_s(y))` pointwise in `t` for a.e.
    `y`, dominated by `K`).

3e. Upgrade subsequence a.e. → in-measure → `L²`: with the `4K²`
    L² dominator from 3a,
    `MeasureTheory.tendsto_Lp_of_tendstoInMeasure` gives
    `M_σ → ψ'(u_s)` in `L²` (full filter, not just subsequence).

### Step 4 — close

By Step 3 (`M_σ → ψ'(u_s)` in `L²`) and `hu` (`Δσ → u'` in `L²`),
`Filter.Tendsto.inner` gives
`⟪M_σ, Δσ⟫ → ⟪ψ'(u_s), u'⟫ = ∫ ψ'(u_s)·u' dν`.
Combined with Step 2, that's `HasDerivWithinAt F (∫ ψ'(u_s)·u') (Set.Ici 0) s`.

## Key Mathlib lemmas

- `MeasureTheory.tendstoInMeasure_of_tendsto_Lp`
- `MeasureTheory.tendstoInMeasure_iff_exists_subseq_tendsto_ae`
- `MeasureTheory.tendsto_Lp_of_tendstoInMeasure` (the converse: in-measure + L^p-dominated ⇒ Lp)
- `Filter.Tendsto.inner` (continuity of real `L²` inner product)
- `Continuous.intervalIntegral` / pointwise DCT for the `t`-integral defining `M_σ`
- `MeasureTheory.MemLp.toLp`, `Lp.coeFn_*` for representative bookkeeping
- `ContDiff.continuous_deriv` (`ψ ∈ C¹ ⇒ ψ' continuous`); `IsCompact.bddAbove_image` for `‖ψ'|_{[-M,M]}‖_∞`

## Formalization effort

**~300–400 lines.** The bulk is bookkeeping for the `MemLp 2 ν`
status of `M_σ` (joint `(t,y)` measurability is mechanical from
continuity of `ψ'`) and the in-measure-subsequence machinery. The
two structural shortcuts (no Fubini, no manual Term-A/Term-B split)
cut roughly 100 + 100 lines off a naïve direct proof.

## Ruled-out alternatives

- **Direct Mathlib pointwise Leibniz** (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`):
  doesn't apply, because `u : ℝ → Lp` is only strong-`L²`-differentiable
  in `σ`, not pointwise-a.e.-differentiable. The strong-`L²` derivative
  is the abstraction that lets the kernel exist at all.
- **Nemitsky / superposition-operator Fréchet differentiability of
  `Φ(v) := ∫ ψ ∘ v dν` on `L²`**: doesn't exist — `Φ` maps `L² → ℝ`
  only when `ψ` is at most quadratic. For general `C¹` `ψ`, the
  Fréchet-derivative-of-Φ + chain-rule route is a dead end.

## Vetting record

- **Gemini deep-think 2026-05-19** (gemini-3.1-pro): confirmed the
  original statement is false (counterexample above), confirmed the
  `h_u_bound` patch is the minimal fix (NOT a uniform-on-curve bound
  on `ψ'(u_σ)`, which is too weak because of the MVT segment issue),
  confirmed the L²-inner-product-continuity + in-measure-subsequence
  proof shape, ruled out the Nemitsky route, estimated 300–400 LOC.
- **In-file docstring's earlier sketch** ("discharge from pointwise
  Mathlib Leibniz + L²→L¹ Cauchy–Schwarz") was inaccurate about the
  route — the actual route is inner-product continuity, not pointwise
  Leibniz.

## Consumer-side patch needed

`grossPow_hasDerivWithinAt` (Abstract/GrossODE.lean, around line 302):
must now supply `h_u_bound` when invoking the kernel. Supplied from
`D.IsCore f` + `D.semigroup_contraction` (Markov-semigroup `L^∞`-
contractivity) — a few lines, no new abstract content.

## References

BGL §5.2 (Leibniz/Duhamel for semigroup orbits); Glimm-Jaffe Ch.6;
Stein–Shakarchi Vol III §1.3 (parametric integrals).
