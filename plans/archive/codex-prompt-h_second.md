> **📦 ARCHIVED 2026-05-21 — work complete (GrossODE.lean is sorry-free). Retained for provenance; see [`../history.md`](../history.md).**

# Codex prompt — fill `h_second` (MVT-in-τ) in grossPow_hasDerivWithinAt

**Repo:** `markov-semigroups` (Lean 4 + Mathlib).
**File:** `MarkovSemigroups/Abstract/GrossODE.lean`.
**Build:** `lake build MarkovSemigroups.Abstract.GrossODE` (must stay green; no new axioms, no new sorries except the one you're replacing).
**Branch:** `gross-grossPow-hasDerivWithinAt-body`.

## STATUS UPDATE (2026-05-21): all helper lemmas now exist — this is pure assembly

Every scalar/measure-theoretic ingredient for the MVT path is now proved
axiom-free in this same file (above `grossPow_hasDerivWithinAt`). The
remaining task is *only* to wire them into `h_second`. The helpers:

```lean
-- MVT with an unordered-interval witness:
exists_hasDerivAt_eq_slope_uIcc {f f' : ℝ → ℝ} {a b : ℝ}
  (hab : a ≠ b) (hfc : Continuous f) (hff' : ∀ x, HasDerivAt f (f' x) x) :
  ∃ c ∈ Set.uIcc a b, (f b - f a) / (b - a) = f' c

-- ∫|f| = (eLpNorm f 1).toReal:
integral_abs_eq_eLpNorm_one_toReal (hf : Integrable (fun y => |f y|) ν) :
  ∫ y, |f y| ∂ν = (eLpNorm f 1 ν).toReal

-- probability space: eLpNorm·2 → 0  ⇒  ∫|·| → 0:
tendsto_integral_abs_of_tendsto_eLpNorm_two_zero (ν) [IsProbabilityMeasure ν]
  (F : ι → Y → ℝ) (hF_meas) (hF_int) (hF_two) :
  Tendsto (fun i => ∫ y, |F i y| ∂ν) l (𝓝 0)

-- (v^r·log v)' = v^{r-1}(r·log v + 1):
hasDerivAt_rpow_mul_log {r v : ℝ} (hv : 0 < v) :
  HasDerivAt (fun w => w ^ r * Real.log w) (v ^ (r - 1) * (r * Real.log v + 1)) v

-- UNIFORM Lipschitz of v ↦ v^r·log v on [a,b] (0<a), uniform over r ∈ [r₀,r₁]:
exists_lipschitz_rpow_mul_log {a b r₀ r₁ : ℝ} (ha : 0 < a) :
  ∃ L : ℝ, 0 ≤ L ∧ ∀ r ∈ Set.Icc r₀ r₁, ∀ v ∈ Set.Icc a b, ∀ w ∈ Set.Icc a b,
    |w ^ r * Real.log w - v ^ r * Real.log v| ≤ L * |w - v|

-- CONTINUITY of the frozen-orbit log-integral at any τ₀:
continuousAt_integral_rpow_mul_log (ν) [IsFiniteMeasure ν] {w : Y → ℝ}
  (hw : AEStronglyMeasurable w ν) {ε M : ℝ} (hε : 0 < ε)
  (hwε : ∀ᵐ y ∂ν, ε ≤ |w y|) (hwM : ∀ᵐ y ∂ν, |w y| ≤ M)
  {a : ℝ → ℝ} (ha : Continuous a) (ha_pos : ∀ τ, 0 < a τ) (τ₀ : ℝ) :
  ContinuousAt (fun τ => ∫ y, |w y| ^ a τ * Real.log |w y| ∂ν) τ₀
```

Plus the orbit a.e. lower bound `ε ≤ u_σ` is available via
`MarkovSemigroup.orbit_lower_bound` (for σ ≥ 0), and the orbit `→ u_s`
in L² via the within-derivative `hu_deriv.continuousWithinAt` (already
in scope), which feeds `tendsto_integral_abs_of_tendsto_eLpNorm_two_zero`.

So: build the MVT-witness `τ_σ` (via `exists_hasDerivAt_eq_slope_uIcc`,
with the per-τ derivative `HasDerivAt (Hfun σ ·) (gfun σ τ) τ` coming from
`hasDerivAt_integral_rpow_exponent` at frozen orbit `u_σ`), squeeze
`τ_σ → s`, then bound `|gfun σ τ_σ − D2|` by the two brackets using
`exists_lipschitz_rpow_mul_log` (first) and `continuousAt_integral_rpow_mul_log`
(second). No new analysis needed.

## Task

Inside the theorem `grossPow_hasDerivWithinAt`, in the `have h_chain` block,
there is one `sorry` for the sub-goal `h_second`:

```lean
    have h_second : Filter.Tendsto
        (fun σ => (Hfun σ σ - Hfun σ s) / (σ - s))
        (nhdsWithin s (Set.Ici 0 \ {s})) (nhds D2) := by
      sorry
```

Replace this `sorry` with a complete proof. Do not change anything else
in the file (the surrounding scaffold is proven and must stay intact).

## In-scope definitions and hypotheses (all available at the sorry)

```lean
-- ρ p : ℝ, hρ : 0 < ρ, hp : 1 < p, hs : 0 ≤ s
-- D : DirichletMarkovSemigroup X
-- hf : D.IsCore f, with f ≥ ε > 0 a.e. and |f| ≤ Mf a.e.
ε   : ℝ;  hε_pos : 0 < ε
Mf  : ℝ
Mf' : ℝ := max Mf 1;  hMf'_one : 1 ≤ Mf';  hMf'_pos : 0 < Mf'
q   : ℝ := grossExponent ρ p s;  hq_pos : 0 < q;  hq_one_le : 1 ≤ q
Af  : Lp ℝ 2 D.μ                       -- the generator image of hf (from h_gen)
u_s_func : X → ℝ := ((D.P s (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ)

-- Orbit a.e. bounds:
hu_s_ge_ε : ∀ᵐ y ∂D.μ, ε ≤ ((D.P s (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y
hu_s_le_Mf : ∀ᵐ y ∂D.μ, |((D.P s (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y| ≤ Mf
hu_σ_le_Mf : ∀ᶠ σ in nhdsWithin s (Set.Ici 0),
    ∀ᵐ y ∂D.μ, |((D.P σ (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y| ≤ Mf

-- Two-variable function and its τ-derivative integrand:
Hfun : ℝ → ℝ → ℝ := fun σ τ =>
    ∫ y, |((D.P σ (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y| ^ grossExponent ρ p τ ∂D.μ
gfun : ℝ → ℝ → ℝ := fun σ τ =>
    2 * ρ * (grossExponent ρ p τ - 1)
      * ∫ y, |((D.P σ (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y| ^ grossExponent ρ p τ
          * Real.log |((D.P σ (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ) y| ∂D.μ
D2 : ℝ := 2 * ρ * (grossExponent ρ p s - 1) * grossLogIntegral D hf ρ p s
-- NOTE: D2 = gfun s s  (because grossLogIntegral D hf ρ p s
--       = ∫ |u_s|^{q(s)} · log|u_s|, and gfun s s has that integral times 2ρ(q(s)-1)).
```

Useful already-proven lemmas in this file / project:
- `hasDerivAt_integral_rpow_exponent (ν) (hw : AEStronglyMeasurable w ν) (hM : ∀ᵐ y ∂ν, |w y| ≤ M) (ha_cd : ContDiff ℝ 1 a) (ha : HasDerivAt a a' s) (ha_pos : ∀ σ, 0 < a σ) : HasDerivAt (fun σ => ∫ y, |w y|^{a σ} ∂ν) (a' * ∫ y, |w y|^{a s} * Real.log |w y| ∂ν) s`
- `contDiff_grossExponent ρ p (n := 1) : ContDiff ℝ 1 (grossExponent ρ p)`
- `hasDerivAt_grossExponent ρ p τ : HasDerivAt (grossExponent ρ p) (2*ρ*(grossExponent ρ p τ - 1)) τ`
- `grossExponent_pos hp ρ τ : 0 < grossExponent ρ p τ`
- `MarkovSemigroup.orbit_lower_bound`, `MarkovSemigroup.Linfty_contraction` (orbit a.e. bounds for σ ≥ 0).
- `MarkovSemigroup.strong_cont_at S g hs : Tendsto (fun σ => S.P σ g) (𝓝[Ici 0] s) (𝓝 (S.P s g))` (orbit → in L²).

## The mathematical plan (Gemini-vetted, gemini-3.1-pro-preview 2026-05-20)

**Step 4 — MVT in τ.** For σ in a right-neighbourhood of `s` with σ ≠ s,
the frozen-orbit function `Hfun σ ·` has the τ-derivative `gfun σ τ` at
every τ (by `hasDerivAt_integral_rpow_exponent` with `w := orbit at σ`,
`a := grossExponent ρ p`, point τ; the orbit bound for that σ comes from
`hu_σ_le_Mf`). Apply `exists_hasDerivAt_eq_slope` (Mathlib MVT) on the
interval between `s` and `σ` (case-split `lt_or_gt_of_ne` for orientation),
giving `τ_σ` strictly between `s` and `σ` with
`(Hfun σ σ - Hfun σ s)/(σ - s) = gfun σ τ_σ`.

**Squeeze.** `τ_σ` between `s` and `σ` ⇒ `|τ_σ - s| ≤ |σ - s| → 0`, so
`τ_σ → s` (as σ → s).

**Step 5 — `gfun σ τ_σ → D2 = gfun s s`.** Split:
`|gfun σ τ_σ − gfun s s| ≤ |gfun σ τ_σ − gfun s τ_σ| + |gfun s τ_σ − gfun s s|`.

* **Second bracket → 0**: `τ ↦ gfun s τ` is continuous at `s` (DCT —
  the integrand `|u_s|^{q(τ)}·log|u_s|` is dominated using `ε ≤ |u_s| ≤ Mf`,
  so `log|u_s| ∈ [log ε, log Mf]` is bounded), and `τ_σ → s`.

* **First bracket → 0 (the key step, uses the bounds)**: the integrand
  `(τ, v) ↦ v^{q(τ)}·log v` has **uniformly bounded ∂_v** on `v ∈ [ε, Mf]`
  for `τ` near `s` (because `ε ≤ v ≤ Mf` keeps both `v^{q(τ)-1}` and `log v`
  bounded). So it is Lipschitz in `v` with a uniform constant `L`
  (`Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le`). Hence pointwise
  `|f(τ_σ, u_σ y) − f(τ_σ, u_s y)| ≤ L·|u_σ y − u_s y|`, and `integral_mono`
  gives `|gfun σ τ_σ − gfun s τ_σ| ≤ |2ρ(q(τ_σ)-1)|·L·∫ |u_σ − u_s|`. Then
  `u_σ → u_s` in L² (from `strong_cont_at`, or from the orbit's
  within-derivative continuity), and **L² → L¹** on the probability
  measure `D.μ` (Cauchy–Schwarz with the constant-1 function:
  `∫|g| ≤ ‖g‖_{L²}·‖1‖_{L²} = ‖g‖_{L²}` since μ is a probability measure)
  ⇒ `∫|u_σ − u_s| → 0`.

Combine via `tendsto_of_tendsto_of_tendsto_of_le_of_le` / squeeze.

## Known pitfalls

- The orbit `(D.P σ (D.coreToL2 hf) : X → ℝ)` is an `Lp` coercion — only
  `AEStronglyMeasurable`, only a.e.-bounded. All estimates are a.e.
- For the MVT you need the orbit bound `|u_σ y| ≤ Mf` for the *specific* σ;
  it is available eventually-σ via `hu_σ_le_Mf` — work on the filter
  `nhdsWithin s (Set.Ici 0 \ {s})` and `filter_upwards [hu_σ_le_Mf, ...]`.
- The `[ε, Mf]` strict-positive bounds are essential to tame `log` —
  do not try to bound `log|u_σ|` without them.
- Keep `q τ = grossExponent ρ p τ > 1` in mind (so `q τ - 1 > 0`,
  rpow well-behaved).

## Deliverable

A single replacement for the `sorry` (a `by`-block proving `h_second`).
Keep everything else byte-for-byte identical. Verify with
`lake build MarkovSemigroups.Abstract.GrossODE`. Confirm no new axioms
via `#print axioms GrossODE.grossPow_hasDerivWithinAt` (should remain
`[propext, Classical.choice, Quot.sound]` modulo the other body sorry
`h_energy`, which is being filled separately).
