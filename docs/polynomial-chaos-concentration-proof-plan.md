# Proof plan: `polynomial_chaos_concentration` (Janson 5.10)

**Status:** Ready for formalization. Vetted by Gemini deep-think
(2026-05-08). Estimated effort: 120–180 lines of Lean tactic-style
proof.

## Target

Convert `polynomial_chaos_concentration` from axiom to theorem in
`MarkovSemigroups/Gaussian/PolynomialChaosConcentration.lean`:

```lean
theorem polynomial_chaos_concentration (n d : ℕ) (hd : 1 ≤ d) :
    ∃ c_d : ℝ, 0 < c_d ∧
      ∀ (F : Lp ℝ 2 (stdGaussianFin n)),
        F ∈ wienerChaosLE n d →
        ∀ (lam : ℝ), 0 < lam →
          (stdGaussianFin n)
              {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|} ≤
            2 * ENNReal.ofReal (Real.exp (-c_d * lam ^ ((2 : ℝ) / d)))
```

## Available lemmas

* `bonami_nelson_chaosLE` (theorem, file:9a5658d):
  ```
  eLpNorm F (ENNReal.ofReal p) μ ≤
    ENNReal.ofReal (((d : ℝ) + 1) * (p - 1) ^ ((d : ℝ) / 2)) *
      eLpNorm F 2 μ
  ```
* `MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm` (Mathlib):
  ```
  μ { x | ε ≤ ‖f x‖ₑ } ≤ ε⁻¹ ^ p.toReal * eLpNorm f p μ ^ p.toReal
  ```
* `Real.log_two_gt_d9 : 0.6931471803 < Real.log 2`
* `Lp.norm_def`, `Lp.coeFn_*`, `Lp.aestronglyMeasurable`
* `Real.exp_pos`, `Real.exp_log`, `Real.rpow_*`
* `ENNReal.ofReal_*`, `ENNReal.toReal_*`
* `prob_le_one`

## Constants

```lean
let L0 : ℝ := Real.exp 1 * ((d : ℝ) + 1)
let c_d : ℝ := (1 / 2) * (1 / L0) ^ ((2 : ℝ) / d)
```

(Lean 4 reserves `λ` as the lambda introducer; do **not** name a local
`λ₀`. Use `L0` or similar.)

## Outer structure

```lean
refine ⟨c_d, hc_d_pos, ?_⟩
intro F hF lam hlam
by_cases hF_norm_zero : ‖F‖ = 0
· -- Case A: F = 0 in Lp.
  ...
push_neg at hF_norm_zero
have hF_norm_pos : 0 < ‖F‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hF_norm_zero)
by_cases hlam_large : L0 ≤ lam
· -- Case C: large λ — Markov + Bonami-Nelson + algebraic identification.
  ...
push_neg at hlam_large
-- Case B: small λ — trivial bound.
...
```

## Case A: `‖F‖ = 0` (≈ 15–20 lines)

`Lp.norm_eq_zero_iff` gives `F =ᵐ[μ] 0`. Then
`{x | 0 < |(F : … ) x|} ⊆ {x | F x ≠ 0}` is null. Apply `measure_mono`
+ `measure_zero_iff_ae_eq_zero` (or equivalent) to get LHS = 0.

```lean
have hF_eq_zero : (F : (Fin n → ℝ) → ℝ) =ᵐ[stdGaussianFin n] 0 :=
  (Lp.norm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hF_norm_zero
have h_set_null : (stdGaussianFin n)
    {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|} = 0 := by
  rw [hF_norm_zero, mul_zero]
  -- {x | 0 < |F x|} = {x | F x ≠ 0}; this is null.
  apply measure_mono_null _ (ae_iff.mp hF_eq_zero)
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  exact (abs_pos.mp hx)
rw [h_set_null]
exact bot_le
```

## Case B: `0 < λ < L0` (small λ, ≈ 30–40 lines)

1. `μ {…} ≤ 1` by `prob_le_one`.
2. Show `1 ≤ 2 · ENNReal.ofReal (exp(-c_d λ^(2/d)))`.
3. Reduces to `1 ≤ 2 · exp(-c_d λ^(2/d))` in ℝ then ofReal-monotone.
4. Equivalent to `c_d λ^(2/d) ≤ log 2`.
5. `c_d λ^(2/d) = (1/2) (λ/L0)^(2/d)` via `Real.mul_rpow`.
6. `λ < L0` ⇒ `λ/L0 < 1` ⇒ `(λ/L0)^(2/d) < 1` (`Real.rpow_lt_one`).
7. So `c_d λ^(2/d) < 1/2 < log 2` (`Real.log_two_gt_d9`).

This case is purely algebraic in ℝ; should be straightforward.

## Case C: `L0 ≤ λ` (large λ, ≈ 65–100 lines, the bulk)

### Setup

```lean
set t : ℝ := (lam / L0) ^ ((2 : ℝ) / d) with ht_def
set p : ℝ := 1 + t with hp_def
have ht_one_le : 1 ≤ t := …  -- (lam/L0)^(2/d) ≥ 1^(2/d) = 1
have hp_two_le : 2 ≤ p := by linarith
```

### Algebraic key

```lean
have h_pminus1_pow : (p - 1) ^ ((d : ℝ) / 2) = lam / L0 := by
  -- (p - 1)^(d/2) = t^(d/2) = ((lam/L0)^(2/d))^(d/2)
  --              = (lam/L0)^((2/d) * (d/2))   -- Real.rpow_mul
  --              = (lam/L0)^1                  -- field_simp
  --              = lam/L0
```

This identification is the crux — it makes the Markov + Bonami-Nelson
bound collapse to `exp(-p)` exactly.

### Markov + Bonami-Nelson (the technical bulk)

**Critical advice from Gemini vetting:** Move to ℝ as soon as possible.
The `ENNReal` arithmetic with `ofReal`-coercions, division, and rpow
becomes intractable; doing the algebra in ℝ is far cleaner. The
recommended structure:

```lean
-- Apply Markov in ENNReal.
have h_markov : (stdGaussianFin n) {x | lam * ‖F‖ < |F x|} ≤
    (ENNReal.ofReal (lam * ‖F‖))⁻¹ ^ p *
      eLpNorm (F : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n) ^ p := by
  -- Inclusion {< } ⊆ {≤} bridges to meas_ge_le_mul_pow_eLpNorm_enorm.
  refine (measure_mono ?_).trans ?_
  · intro x hx; simp [Set.mem_setOf_eq] at hx ⊢
    -- ‖F x‖ₑ = ENNReal.ofReal |F x|; lam * ‖F‖ < |F x| ⇒ ofReal lhs ≤ ofReal rhs
    sorry
  · convert MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm
      (stdGaussianFin n) (p := ENNReal.ofReal p) ?_ ?_
      (Lp.aestronglyMeasurable F) ?_ ?_
    all_goals sorry  -- side-conditions: ofReal p ≠ 0, ≠ ∞, ε ≠ 0, ε ≠ ∞ ⇒ μ{‖f‖ = ⊤} = 0

-- Apply Bonami-Nelson and combine.
have h_bn := bonami_nelson_chaosLE n d F hF p hp_two_le
have h_combined : … ≤ ENNReal.ofReal (((d+1) * (p-1)^(d/2))^p / lam^p) := by
  …  -- algebraic combine using h_markov, h_bn

-- Move to ℝ via ENNReal.toReal_le_toReal once both sides are finite.
have h_rhs_finite : … < ⊤ := …
have h_real : (μ {…}).toReal ≤ (((d+1) * (p-1)^(d/2))^p / lam^p) := …

-- Substitute h_pminus1_pow: (p-1)^(d/2) = lam/L0.
-- ⇒ (d+1)(lam/L0)/lam = (d+1)/L0 = (d+1)/(e(d+1)) = 1/e.
-- ⇒ ((d+1)(p-1)^(d/2))^p / lam^p = (1/e)^p = exp(-p).
have h_simp : ((↑d + 1) * (p - 1)^((d : ℝ)/2))^p / lam^p = Real.exp (-p) := …

-- Final: exp(-p) = exp(-(1+t)) ≤ 2·exp(-t/2) = 2·exp(-c_d λ^(2/d)).
have h_target : Real.exp (-p) ≤ 2 * Real.exp (-c_d * lam^(2/d)) := by
  -- Need c_d · lam^(2/d) = t/2, then exp(-1-t) ≤ 2·exp(-t/2)
  -- ⟺ exp(-1) ≤ 2·exp(t/2 - t + t) = 2·exp(t/2).  Wait, just compute:
  -- exp(-1-t) / exp(-t/2) = exp(-1 - t/2). For t ≥ 1: exp(-1 - 1/2) = exp(-3/2) ≤ 1/2 ≤ 1/2
  -- So exp(-1-t) ≤ (1/2) · exp(-t/2) ≤ 2 · exp(-t/2). ✓
  …
```

### Why move to ℝ early

In ENNReal, the cancellation `(ENNReal.ofReal (lam * ‖F‖))⁻¹^p ·
(ENNReal.ofReal ((d+1)(p-1)^(d/2)) · ENNReal.ofReal ‖F‖)^p` involves
multiplications of `ofReal`s, raising to real powers, and division —
each step requires nonzero/non-top side-conditions and the
`ENNReal.ofReal_*` lemmas don't compose smoothly. In ℝ, the same
expression simplifies via `ring`/`field_simp` once `‖F‖ > 0` and
`lam > 0` are established.

Concretely:

```lean
-- In ENNReal: hard.
(ENNReal.ofReal (lam * ‖F‖))⁻¹ ^ p *
  (ENNReal.ofReal ((d+1)(p-1)^(d/2)) * ENNReal.ofReal ‖F‖) ^ p

-- Move to ℝ using ENNReal.toReal_*:
((lam * ‖F‖)⁻¹) ^ p * (((d+1)(p-1)^(d/2)) * ‖F‖) ^ p
  = (lam * ‖F‖)^(-p) * ((d+1)(p-1)^(d/2))^p * ‖F‖^p
  = (lam^(-p)) * (‖F‖^(-p)) * ((d+1)(p-1)^(d/2))^p * ‖F‖^p
  = (lam^(-p)) * ((d+1)(p-1)^(d/2))^p
  = ((d+1)(p-1)^(d/2))^p / lam^p
```

Then convert back via `ENNReal.ofReal_le_ofReal` at the end.

### Final exp comparison

```
exp(-p) = exp(-(1+t))
       = exp(-1) · exp(-t)
       ≤ 2 · exp(-t/2)             -- because exp(-1-t/2) ≤ 1/2 ≤ 2 for t ≥ 1
                                      i.e., exp(-1) · exp(-t/2) ≤ 1/2,
                                      since exp(-1) ≈ 0.368 ≤ 0.5 already.
       = 2 · exp(-c_d · lam^(2/d))  -- because c_d · lam^(2/d) = t/2.
```

Verify `c_d · lam^(2/d) = t/2`:
- `c_d = (1/2) (1/L0)^(2/d)`.
- `c_d · lam^(2/d) = (1/2) (1/L0)^(2/d) · lam^(2/d) = (1/2) (lam/L0)^(2/d) = (1/2) · t = t/2`. ✓

## Critical Mathlib lemmas to verify exact names

* `Lp.norm_eq_zero_iff` — converts `‖F‖ = 0` ⇔ `F =ᵐ 0`.
* `Lp.norm_def` — `‖F‖ = (eLpNorm F p μ).toReal`. **Trap**: at recent
  Mathlib v4.29.0, the `Lp` norm API has heavily refactored around
  `eLpNorm`/`snorm`. The connection from the topological `‖F‖` (norm
  on the `Lp` type) to `eLpNorm F 2 μ` (measure-theoretic extended
  norm) may need to be routed through `snorm` lemmas — verify with a
  small `#check Lp.norm_def` test before committing to the exact form.
* `Lp.aestronglyMeasurable` — for the Markov hypothesis.
* `MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm` — Markov.
* `ENNReal.ofReal_rpow_of_pos` — `ENNReal.ofReal (a^p) = (ENNReal.ofReal a)^p` for `0 < a`.
* `ENNReal.toReal_rpow` — `(x^p).toReal = x.toReal ^ p` for finite x.
* `ENNReal.toReal_inv_of_ne_top` — for `(ε⁻¹).toReal = ε.toReal⁻¹`.
* `Real.mul_rpow` (for `0 ≤ a, 0 ≤ b`).
* `Real.rpow_mul` (for `0 ≤ x` — the exponents associate).
* `Real.rpow_lt_one` (for `0 ≤ a < 1`).
* `Real.log_two_gt_d9`.
* `Real.enorm_eq_ofReal_abs` (or Mathlib v4.29.0 equivalent
  `ofReal_abs_eq_enorm`): for `y : ℝ`, `‖y‖ₑ = ENNReal.ofReal |y|`.
  Needed for the inclusion `{lam·‖F‖ < |F x|} ⊆ {ENNReal.ofReal (lam·‖F‖) ≤ ‖F x‖ₑ}`.
* `prob_le_one` or `MeasureTheory.measure_le_one` (need
  `IsProbabilityMeasure (stdGaussianFin n)` instance).

**Probability measure instance**: `stdGaussianFin n` is
`Measure.pi (fun _ => gaussianReal 0 1)`, so the instance
`IsProbabilityMeasure (stdGaussianFin n)` should synthesize
automatically from `MeasureTheory.Measure.pi.instIsProbabilityMeasure`
+ the per-coordinate `gaussianReal 0 1` probability instance. If
synthesis fails, force it with
`inferInstanceAs (IsProbabilityMeasure (Measure.pi …))` or add a
short top-level instance declaration.

## Implementation tips

1. **Build the case A handler first** — it's the simplest and exercises
   the `Lp.norm_eq_zero_iff` interface.

2. **Then case B** — pure ℝ algebra; no Markov/ENNReal interaction
   needed.

3. **Save case C for last** — it's the bulk. Within it, nail
   `h_pminus1_pow` and `h_simp` (the algebraic identifications) as
   standalone `have`s in ℝ before threading them through the
   Markov-side ENNReal manipulations.

4. **For the Markov-to-ℝ bridge**: introduce intermediate `have`s for
   each finiteness side-condition. Don't try to do it in one tactic
   block. The pattern:
   - `h_eLpNorm_p_lt_top`: `eLpNorm F p μ < ⊤` (from Bonami-Nelson +
     `eLpNorm F 2 μ < ⊤` since F : Lp).
   - `h_eLpNorm_p_ne_top`: `eLpNorm F p μ ≠ ⊤`.
   - `h_ofReal_lam_nF_ne_zero`: `ENNReal.ofReal (lam · ‖F‖) ≠ 0`.
   - `h_ofReal_lam_nF_ne_top`: trivial since `ofReal _ ≠ ⊤`.

5. **The `‖F x‖ₑ = ENNReal.ofReal |F x|` step** for the inclusion
   `{lam·‖F‖ < |F x|} ⊆ {ENNReal.ofReal (lam·‖F‖) ≤ ‖F x‖ₑ}` requires
   `Real.enorm_eq_ofReal_abs` or similar. For `F x : ℝ`,
   `‖F x‖ₑ = ENNReal.ofReal |F x|`.

## Estimated effort

* Case A: 15–20 lines.
* Case B: 30–40 lines.
* Case C: 65–100 lines.
* Total: **120–180 lines**.

Likely 1–2 focused work sessions of ≈ 2–4 hours each, given the
ENNReal/ℝ bookkeeping.

## Vetting verdict (Gemini deep-think, 2026-05-08)

> "The plan is solid. The case split on λ is the correct approach. The
> definitions of c_d, L0, p, and t are standard and correct. The key
> steps of applying Bonami-Nelson and Markov's inequality are
> identified properly. The algebraic simplifications are correct. You
> have a winning strategy here. The previous difficulties likely arose
> from the implementation details of ENNReal/Real arithmetic, which we
> can refine."

Key strategic recommendation:

> "As soon as you apply Markov's inequality, prove the RHS is finite
> and immediately convert the inequality to ℝ using
> `ENNReal.toReal_le_toReal`. Do all subsequent algebraic cancellation
> and simplification in ℝ, then convert the final bound back to
> ENNReal. This will sidestep the vast majority of ENNReal-related
> pain."
