> **📦 ARCHIVED 2026-05-21 — work complete (GrossODE.lean is sorry-free). Retained for provenance; see [`../history.md`](../history.md).**

# Codex prompt — fill `h_energy` (energy identification) in grossPow_hasDerivWithinAt

**Repo:** `markov-semigroups` (Lean 4 + Mathlib).
**File:** `MarkovSemigroups/Abstract/GrossODE.lean`.
**Build:** `lake build MarkovSemigroups.Abstract.GrossODE` (must stay green; no new axioms, no new sorries except the one you're replacing).
**Branch:** `gross-grossPow-hasDerivWithinAt-body`.

## Task

Inside the theorem `grossPow_hasDerivWithinAt`, near the end, there is a
`sorry` for the sub-goal `h_energy`:

```lean
  have h_energy : D1 + D2 = grossPowDeriv D hf ρ p s := by
    sorry
```

Replace this `sorry` with a complete proof. Do not change anything else.

## In-scope definitions and hypotheses (all available at the sorry)

```lean
-- ρ p : ℝ, hρ : 0 < ρ, hp : 1 < p, hs : 0 ≤ s
-- D : DirichletMarkovSemigroup X
-- h_core : CoreSemigroupInvariant D
-- h_gen  : GeneratorCompat D
-- hf : D.IsCore f, with f ≥ ε > 0 a.e. and |f| ≤ Mf a.e.
ε   : ℝ;  hε_pos : 0 < ε
q   : ℝ := grossExponent ρ p s;  hq_pos : 0 < q;  hq_one_le : 1 ≤ q
Af  : Lp ℝ 2 D.μ
hAf_tendsto : Filter.Tendsto (fun t : ℝ => t⁻¹ • (D.P t (D.coreToL2 hf) - D.coreToL2 hf))
                (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds Af)
hAf_pair : ∀ {g : X → ℝ} (hg : D.IsCore g),
              ⟪D.coreToL2 hg, Af⟫_ℝ = - D.energy g f
u_s_func : X → ℝ := ((D.P s (D.coreToL2 hf) : Lp ℝ 2 D.μ) : X → ℝ)

hf_Lp_ge_ε : ∀ᵐ y ∂D.μ, ε ≤ (D.coreToL2 hf : X → ℝ) y
hu_s_ge_ε  : ∀ᵐ y ∂D.μ, ε ≤ u_s_func y
hu_s_le_Mf : ∀ᵐ y ∂D.μ, |u_s_func y| ≤ Mf
h_coreToL2_nn : (0 : Lp ℝ 2 D.μ) ≤ D.coreToL2 hf
h_orbit_nn : ∀ σ : ℝ, 0 ≤ σ → ∀ᵐ y ∂D.μ, 0 ≤ u_s_func y   -- (at σ = s; general σ available)

D1 : ℝ := ∫ y, deriv (fun x : ℝ => x ^ q) (u_s_func y) * (D.P s Af : X → ℝ) y ∂D.μ
D2 : ℝ := 2 * ρ * (grossExponent ρ p s - 1) * grossLogIntegral D hf ρ p s
```

The target (unfolding `grossPowDeriv`):
```lean
grossPowDeriv D hf ρ p s
  = 2*ρ*(grossExponent ρ p s - 1) * grossLogIntegral D hf ρ p s
    - grossExponent ρ p s
        * D.energy (u_s_func) (fun x => |u_s_func x| ^ (grossExponent ρ p s - 1))
```
(the first term is exactly `D2`). So `h_energy` reduces to:
```
D1 = - q * D.energy (u_s_func) (fun x => |u_s_func x| ^ (q - 1))
```

## Relevant structure fields / lemmas

```lean
-- GeneratorCompat:
GeneratorCompat D := ∀ {f} (hf : D.IsCore f), ∃ Af, Tendsto (...) (𝓝[Ioi 0] 0) (𝓝 Af)
                       ∧ ∀ {g} (hg : D.IsCore g), ⟪D.coreToL2 hg, Af⟫_ℝ = - D.energy g f
-- CoreSemigroupInvariant:
CoreSemigroupInvariant D := ∀ t, 0 ≤ t → ∀ {g} (hg : D.IsCore g),
    ∃ g' (hg' : D.IsCore g'), D.P t (D.coreToL2 hg) = D.coreToL2 hg'
-- Closure axiom (new):
DirichletMarkovSemigroup.IsCore_rpow_pos_strict :
    ∀ {f} (hf : IsCore f) {ε} (hε : 0 < ε), (∀ᵐ y ∂μ, ε ≤ f y) → ∀ r, IsCore (fun x => f x ^ r)
-- deriv of rpow:  Real.deriv_rpow_const' (p : ℝ) : deriv (·^p) = fun x => p * x^(p-1)
-- L2 inner = integral:  MeasureTheory.L2.inner_def, RCLike.inner_apply (real: ⟪a,b⟫ = b*a).
-- energy symmetry:  D.energy_symm.
```

## The mathematical plan

1. **Rewrite `deriv (·^q)`**: `deriv (fun x => x^q) (u_s_func y) = q * (u_s_func y)^(q-1)`
   via `Real.deriv_rpow_const'`. Pull `q` out: `D1 = q * ∫ (u_s_func y)^(q-1) * (P_s Af) y`.

2. **Identify the integral with an L² inner product**: for nonneg orbit
   (`hu_s_ge_ε` ⇒ `u_s_func ≥ 0` a.e.), `(u_s_func y)^(q-1) = |u_s_func y|^(q-1)` a.e.
   The integral `∫ |u_s_func y|^(q-1) * (P_s Af) y dν = ⟪w, P_s Af⟫_ℝ` where
   `w := MemLp.toLp (fun y => |u_s_func y|^(q-1)) _` (need it `MemLp 2`; follows from
   boundedness `ε ≤ u_s ≤ Mf` ⇒ `|u_s|^(q-1)` bounded ⇒ MemLp on the finite measure).
   Use `MeasureTheory.L2.inner_def` + `RCLike.inner_apply` (real conj trivial).

3. **The generator pairing on the orbit**: We need `⟪w, P_s Af⟫ = - energy(...)`.
   `hAf_pair` is for `Af` (generator of `f`), not `P_s Af` (generator of `u_s`).
   Bridge via `h_core` + limit uniqueness:
   - By `CoreSemigroupInvariant`, `D.P s (D.coreToL2 hf) = D.coreToL2 hg'` for some
     core `g'` (so `u_s = coreToL2 hg'` in Lp, hence `u_s_func =ᵐ g'`).
   - Apply `h_gen hg'` to get `Ag'` with `Tendsto ((P_t (coreToL2 hg') - coreToL2 hg')/t) → Ag'`
     and `∀ core h, ⟪coreToL2 hh, Ag'⟫ = - energy h g'`.
   - **`Ag' = D.P s Af`** by uniqueness of the strong-L² limit: both are
     `lim_{t→0+} (P_t u_s - u_s)/t` (use `P_semigroup` to rewrite
     `(P_{s+t} f - P_s f)/t = P_s ((P_t f - f)/t) → P_s Af`, matching the
     `Ag'` limit since `coreToL2 hg' = u_s = P_s (coreToL2 hf)`). Limits in a
     Hausdorff space are unique (`tendsto_nhds_unique`).
   - Choose `h := (g')^(q-1)`, which is `IsCore` by `IsCore_rpow_pos_strict`
     applied to `hg'` with the lower bound `g' ≥ ε` a.e. (transported from
     `hu_s_ge_ε` through `u_s_func =ᵐ g'`).
   - Then `⟪coreToL2 ((g')^(q-1)), Ag'⟫ = - energy ((g')^(q-1)) g'`.

4. **Reconcile representatives**: `coreToL2 ((g')^(q-1))` and `w` are a.e.-equal
   (both `=ᵐ |u_s_func|^(q-1)`), so their L² inner products with `Ag' = P_s Af`
   agree. And `energy ((g')^(q-1)) g'` vs `energy (u_s_func) (|u_s_func|^(q-1))`
   — here `energy` is a *total function on representatives*. **POTENTIAL GAP**:
   the abstract `D.energy` is NOT declared a.e.-invariant. Two options:
   (a) If `energy`'s value only depends on the Lp class (true for all concrete
       instances, e.g. `ouEnergyFin`), this needs either an `energy_ae_congr`
       field/lemma or a per-instance fact. Check whether such a congruence is
       derivable from the existing fields (`energy_eq_deriv` ties energy to the
       Lp pairing, which IS a.e.-invariant — this may suffice to prove
       `energy_ae_congr`).
   (b) Use `energy_symm` to match the argument order in `grossPowDeriv`
       (which has `energy (u_s_func) (|u_s_func|^(q-1))`, i.e. orbit first).

   **If a genuine a.e.-invariance gap appears, STOP and report it** — it may
   require a new structural lemma `energy_ae_congr` (provable from
   `energy_eq_deriv`, which expresses energy via the a.e.-invariant Lp inner
   product). Do not introduce an unjustified axiom.

5. **Combine**: `D1 = q · ⟪w, P_s Af⟫ = q · (- energy(...)) = - q · energy(...)`,
   so `D1 + D2 = D2 - q·energy(...) = grossPowDeriv`. Close with `unfold grossPowDeriv`
   + the pieces + `ring`.

## Known pitfalls

- `energy` is a function on `X → ℝ` representatives, NOT on Lp classes. The
  a.e.-invariance (step 4) is the subtle part — surface it explicitly if it
  blocks you.
- `Ag' = P_s Af` needs the semigroup commutation `P_{s+t} = P_s ∘ P_t` +
  CLM continuity + limit uniqueness. The helper
  `MarkovSemigroup.orbit_hasDerivWithinAt` (already in
  `Abstract/Hypercontractivity.lean`) proves `HasDerivWithinAt (fun σ => P σ f) (P s Af)`,
  whose construction contains the `(P_{s+t} f - P_s f)/t → P_s Af` argument —
  reuse its structure.
- All bounds/positivity are a.e.

## Deliverable

A single replacement for the `sorry` (a `by`-block proving `h_energy`).
If you hit the `energy_ae_congr` structural gap, prove it as a separate
`have`/lemma if derivable from `energy_eq_deriv`, else report the gap
clearly. Verify with `lake build MarkovSemigroups.Abstract.GrossODE`.
