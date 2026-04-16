# AI-Assisted Lean Proving: Demo and Case Studies

A demonstration of how a mathematician interacts with AI tools
(Claude, Codex, Gemini) to formalize proofs in Lean 4, drawn from
a real project: lattice gauge theory mass gap and Markov semigroup
functional inequalities.

**Projects:** [markov-semigroups](https://github.com/mrdouglasny/markov-semigroups),
[lgt](https://github.com/mrdouglasny/lgt) (lattice gauge theory),
[hille-yosida](https://github.com/mrdouglasny/hille-yosida) (C₀-semigroups)

**Author:** Michael R. Douglas, with AI assistance from Claude (Anthropic),
Codex (OpenAI), and Gemini (Google)

---

## Live Demo: Fill a Sorry

### Target: `semigroup_selfAdjoint` in `Instances/Euclidean.lean`

**The sorry:**
```lean
semigroup_selfAdjoint := fun f g t ht hf hg => by
    -- Self-adjointness: the Mehler kernel K(t,x,y) is symmetric
    sorry
```

**The goal:** ∫ (P_t f)·g dγ = ∫ f·(P_t g) dγ, where P_t is the
Ornstein-Uhlenbeck semigroup on ℝ with standard Gaussian measure.

### Step 1: Read the existing pattern (30 sec)

The `semigroup_mean` proof (just above) shows the technique:
- Define φ(x,y) = e^{-t}x + √(1-e^{-2t})y
- Use `ou_kernel_map`: (γ⊗γ).map φ = γ (Gaussian convolution)
- Use `HasLaw.integral_comp` + `integral_prod` (Fubini)

### Step 2: Mathematical insight (1 min)

Self-adjointness needs a symmetry argument beyond what `semigroup_mean`
used. The key: the orthogonal reflection

    T(x,y) = (ax+by, bx-ay)     where a²+b²=1

preserves γ⊗γ (rotation/reflection invariance of 2D Gaussian) and
swaps the roles of f and g:
- T sends φ to fst: φ(T(x,y)) = a(ax+by)+b(bx-ay) = (a²+b²)x = x
- T sends fst to φ: (T(x,y)).1 = ax+by = φ(x,y)

So ∫ f(φ(p))·g(p.1) d(γ⊗γ) = ∫ f(p.1)·g(φ(p)) d(γ⊗γ) by
change of variables under T.

### Step 3: First attempt — write the proof (2 min)

```lean
show ∫ x, ouSemigroup t f x * g x ∂γ = ∫ x, f x * ouSemigroup t g x ∂γ
simp only [ouSemigroup]
set a := exp (-t); set b := sqrt (1 - exp (-2 * t))
set φ : ℝ × ℝ → ℝ := fun p => a * p.1 + b * p.2
-- Fubini: convert to product integrals
-- Reflection: T(x,y) = (ax+by, bx-ay)
-- Change of variables: ∫ h d(γ⊗γ) = ∫ h∘T d(γ⊗γ)
```

Build → 8 errors.

### Step 4: Iterate on errors (3 min)

Main issues encountered:
- **`mul_of_bound` doesn't exist** → replaced with `Integrable.mono'`
  and explicit norm bounds from `IsCore.bounded`
- **`integral_prod` rewrite direction** → Fubini applies forward
  (product → iterated), not backward. Used `rw [← integral_prod]`
  after setting up the right form
- **`nlinarith` can't handle a²+b²=1** → explicit `ring` step:
  factor as `(a^2+b^2)*p.1`, then `rw [hab, one_mul]`
- **`integral_map` needs `AEStronglyMeasurable`** → constructed
  explicitly via `rw [hT_preserves]`

### Step 5: Build succeeds (30 sec)

One sorry remains: `(γ.prod γ).map T = γ.prod γ` (orthogonal
invariance of 2D Gaussian). This is provable with the same
`gaussianReal_add + independence` technique as `ou_kernel_map`,
using coefficients (b, -a) instead of (a, b).

**Total: ~7 minutes, 1 provable sorry.**

---

## Case Study A: Search for Previous Results

### Example 1: Finding `exp_nat_mul`

**Context:** Proving c^k ≤ exp(-m·k) in `DobrushinVerification.lean`.
Need to rewrite c^k as exp(k · log c).

**Attempt:** `Real.exp_natMul` — not found.

**Search:**
```bash
grep -rn "theorem exp_nat_mul" .lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean
```
Found at line 229:
```
theorem exp_nat_mul (x : ℝ) (n : ℕ) : exp (n * x) = exp x ^ n
```

**The mismatch:** Signature has `n * x` but our goal has `log c * k`
(i.e., `x * n` — backwards).

**The fix:**
```lean
rw [show -(- Real.log c) * ↑k = ↑k * Real.log c by ring,
    Real.exp_nat_mul, Real.exp_log hc_pos]
```

A `ring` rewrite to swap multiplication order before applying the lemma.

### Example 2: Finding `trace_mul_cycle`

**Context:** Proving Tr(g·A·g⁻¹) = Tr(A) for gauge invariance.

**Attempt:** `simp [map_mul, map_inv, Matrix.trace_mul_cycle]` — fails
because `map_inv` doesn't fire (matrix ring isn't a `DivisionMonoid`).

**Search:**
```bash
grep -n "trace_mul_cycle" .lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Trace.lean
```
Found: `Tr(A * B * C) = Tr(B * C * A)` — cyclically permutes.

**The multi-step fix:**
```lean
simp only [gaugeTrace, map_mul]           -- unfold, distribute rep
rw [Matrix.trace_mul_cycle]               -- Tr(g·h·g⁻¹) → Tr(g⁻¹·g·h)
rw [← map_mul, inv_mul_cancel, map_one]   -- g⁻¹·g = 1
rw [Matrix.one_mul]                        -- 1·h = h
```

### The pattern

```
Need lemma → grep Mathlib → read signature → notice mismatch → bridge with rewrite
```

The AI searches thousands of files instantly and generates bridging
rewrites. The human knows WHAT to search for (trace cyclicity,
exponential power).

---

## Case Study B: Postulating Intermediate Results

### The problem: circular dependency

Goal: prove Poincaré inequality `Var(f) ≤ (1/ρ) E(f,f)` (axiom #4).

The standard proof needs the semigroup energy identity, which needs
the L² operator bridge to hille-yosida — a large infrastructure gap.

**Shortcut attempt:** Use variance decay (axiom #6) at t=1:
```
Var(f) = [∫f² - ∫(P₁f)²] + Var(P₁f)
       ≤ bound + e^{-2ρ} · Var(f)
```
But variance decay itself needs Poincaré + Grönwall → **circular!**

### The proposal

**AI postulates:** Add a new class field `semigroup_l2_decay_bound`:
```
∫f² - ∫(P_t f)² ≤ (1 - e^{-2ρt})/ρ · E(f,f)
```

**Judgment — is it more elementary than Poincaré?**
- It follows from d/dt ∫(P_t f)² = -2E(P_t f) integrated with gradient_decay
- That's generator theory — no spectral gap needed
- YES, more elementary ✓

**Judgment — does it break the cycle?**
- Poincaré from L²_decay + ergodicity (no variance_decay needed!)
- Variance_decay from Poincaré + derivative + Grönwall
- No circularity ✓

### The result

```
BEFORE: 7 axioms (including Poincaré and variance_decay)
AFTER:  5 axioms (both proved from class fields)
```

The same pattern was then applied to log-Sobolev (add entropy class
fields → prove LSI) and Brascamp-Lieb (promote resolvent to structure
fields → prove resolvent-IBP axiom), reducing 7 → 2 axioms total.

### The pattern

```
1. Goal: prove axiom P
2. Attempt: needs axiom V → but V needs P → circular
3. Postulate: class field L (more elementary than both)
4. Judge: L doesn't need P or V? ✓
5. Judge: L + other fields → P? ✓
6. Judge: P + other fields → V? ✓ (no cycle)
7. Implement: add L, prove P and V
8. Build: `lake build` confirms 0 sorry's
```

---

## Case Study C: Structuring a New Project

### Starting point

"Can we formulate the d≥3 Yang-Mills mass gap using Dobrushin uniqueness?"

The d=2 mass gap uses Doeblin's condition (independent Markov chains
after gauge fixing). For d≥3, gauge fixing leaves interacting links —
need Dobrushin uniqueness instead.

### Phase 1: Bottom-up estimates

```
DobrushinVerification.lean  ← influence bound ≤ 2nβ, column sum < 1
MassGap3D.lean              ← theorem statement (initially just positivity)
```

Proved: `influenceBound_le_linear`, `dobrushin_sufficient`,
exponential decay `c^k ≤ exp(-mk)`. All zero sorry's.

But the theorem conclusion was vacuous:
```lean
∃ C₁ C₂, 0 < C₁ ∧ 0 < C₂ ∧ ∀ d, C₁ * exp(-C₂ * d) > 0
```

### External review (Codex)

> **P0:** The theorem is vacuous — it never mentions observables,
> expectations, or connected correlators.
>
> **P1:** The measure layer is incomplete — no canonical YM measure,
> no proof that Z > 0.

### Phase 2: Top-down measure construction

```
YMMeasure.lean        ← productHaar, partitionFn (Z > 0), ymExpect, connected2pt
GaugeInvariance.lean  ← S(g·U) = S(U), plaqObs gauge-invariant (zero sorry's!)
SingleSiteKernel.lean ← singleSiteZ, density, ∫p=1
Integrability.lean    ← continuous on compact → integrable (closed all integrability sorry's)
```

### Phase 3: Connection

```
GaugeFixing.lean ← Faddeev-Popov identity, correlation bounds
Locality.lean    ← DependsOn, plaquette support, product independence
```

**Key discovery:** Mathlib already has `DependsOn` for product types
(in `Mathlib.Logic.Function.DependsOn`). Our `GaugeConnection G d N
= LatticeLink d N → G` is exactly a product type. This enabled the
product independence theorem — proved entirely from Mathlib:

```
iIndepFun_pi → iIndep → indep_iSup_of_disjoint
→ comap_le_of_dependsOn → IndepFun → integral_mul
```

### Final state

The theorem conclusion is now real:
```lean
|connected2pt G n d N β plaq (plaqObs p) (plaqObs q)| ≤
    4 * n² * exp(-m * dist(p,q))
```

10 files, 0 axioms, 2 sorry's (both in the gauge-fixing Fubini step).

### The pattern

```
1. Question → Plan components
2. Build estimates bottom-up (sorry-free)
3. External review identifies gaps
4. Build measure top-down (respond to review)
5. Connect estimate to measure
6. Discover Mathlib already has key concept (DependsOn)
7. Assemble proof from Mathlib's independence API
8. Localize remaining gaps to specific sorry's
```

---

## Tools and Their Roles

| Tool | Role | Example |
|------|------|---------|
| **Claude** | Primary prover: writes Lean, iterates on errors, searches Mathlib | All three case studies |
| **Codex** | Reviewer: identifies vacuous theorems, missing connections | d≥3 architecture review |
| **Gemini** | Domain expert: checks axiom validity, suggests proof strategies | Verified Brascamp-Lieb axioms |
| **Lean/lake** | Ground truth: accepts or rejects every proof | `lake build` at every step |
| **Mathlib** | Library: 100k+ lemmas to search and compose | `exp_nat_mul`, `trace_mul_cycle`, `DependsOn`, `iIndepFun_pi` |

The human provides: mathematical direction, judgment on intermediate
results, validation of reviews, and the decision of when to stop.
The AI provides: Mathlib search, proof writing, error iteration,
architecture proposals, and dependency analysis.
