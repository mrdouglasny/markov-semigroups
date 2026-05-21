> **📦 ARCHIVED 2026-05-21 — work complete (GrossODE.lean is sorry-free). Retained for provenance; see [`../history.md`](../history.md).**

# Vetting: `CoreLpApprox` predicate + finishing `gross_lsi_implies_hypercontractive_of_hypotheses`

**For:** deep-think external review.
**Context:** Lean 4 / Mathlib formalization of Gross's theorem (LSI ⇒
hypercontractivity) for a symmetric Markovian semigroup, hypothesis-
parameterised. Self-contained; no repo access needed.

---

## 0. What is already proved

We have a symmetric Markovian semigroup `(P_t)` on `L²(μ)`, `μ` a **probability
measure**, with Dirichlet form `E`, carré du champ, log-Sobolev constant `ρ>0`.
There is an admissible **core** algebra `IsCore ⊆ (X→ℝ)` (bounded functions in
the form domain; closed under `+`, `•`, constants, and — for strictly-positive
elements — under `x ↦ x^r`), and `coreToL2 : IsCore g → L²(μ)` sends a core
function to its `L²` class. Set `q(s) = 1 + (p-1)·e^{2ρs}` (so `q(0)=p`).

The full **Gross-ODE spine is proved, axiom-clean** (`#print axioms` =
`[propext, Classical.choice, Quot.sound]`), in particular:

> **`eLpNorm_orbit_le_of_core_pos`** (proved). For core `f` with `f ≥ ε > 0`
> a.e. and `f ≢ 0`, and `1 < p ≤ q ≤ q(t)`, `0 < t`:
> `eLpNorm (P_t (coreToL2 hf)) (ofReal q) μ ≤ eLpNorm (coreToL2 hf) (ofReal p) μ`.

(Proof: `L^q ≤ L^{q(t)}` monotonicity on the probability measure +
`‖P_s f‖_{q(s)} = exp(Λ(s))` + antitonicity of `Λ(s) = log‖P_s f‖_{q(s)}` from
LSI ⊕ Stroock–Varopoulos, with `Λ(0) = log‖f‖_p`.)

The **goal** is the general statement `IsHypercontractive`:
for `f : L²(μ)` with `MemLp f (ofReal p)`, `1 < p ≤ q`, `0 < t`,
`q ≤ q(t)`:
  `eLpNorm (P_t f) (ofReal q) μ ≤ eLpNorm (f) (ofReal p) μ`.

The gap is purely the **extension from core+strictly-positive `f` to general
`f ∈ L² ∩ L^p`**. The abstract structure has **no core-density axiom** and only
`L²`-contractivity of `P_t` (not `L^p`). So the extension needs a per-instance
("case-dependent") hypothesis, in the style of the three already-used
predicates (core-semigroup-invariance, generator–form compatibility,
Stroock–Varopoulos).

---

## 1. The proposed predicate

```lean
/-- **Core `L^p`-approximation** (per-instance hypothesis). Every nonnegative
`f ∈ L²(μ) ∩ L^p(μ)` is approximated by a sequence of *core, strictly-positive*
functions `gₙ` with `gₙ → f` in `L^p` and orbits `P_t gₙ → P_t f` `μ`-a.e. -/
def CoreLpApprox (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ {p : ℝ}, 1 ≤ p → ∀ (f : Lp ℝ 2 D.μ),
    MemLp ((f : X → ℝ)) (ENNReal.ofReal p) D.μ → 0 ≤ f →
    ∀ {t : ℝ}, 0 ≤ t →
    ∃ (g : ℕ → X → ℝ) (hg : ∀ n, D.IsCore (g n)),
      (∀ n, ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ y ∂D.μ, ε ≤ g n y) ∧
      Filter.Tendsto (fun n => eLpNorm ((f : X → ℝ) - g n) (ENNReal.ofReal p) D.μ)
        Filter.atTop (nhds 0) ∧
      ∀ᵐ y ∂D.μ, Filter.Tendsto
        (fun n => ((D.P t (D.coreToL2 (hg n)) : Lp ℝ 2 D.μ) : X → ℝ) y)
        Filter.atTop (nhds (((D.P t f : Lp ℝ 2 D.μ) : X → ℝ) y))
```

Plain English: for every nonneg `f ∈ L² ∩ L^p` and every `t ≥ 0`, there is a
sequence of core functions `gₙ`, each bounded below by some `εₙ > 0` a.e., such
that (i) `gₙ → f` in `L^p`-(semi)norm and (ii) the `L²`-orbits
`P_t (coreToL2 gₙ)` converge `μ`-a.e. to the orbit `P_t f`. (`P_t f` and
`P_t (coreToL2 gₙ)` are the **`L²` actions**; everything lives in `L²` since
`f : Lp ℝ 2` and `gₙ` are bounded core functions.)

## 2. The finished theorem (with the new hypothesis)

```lean
theorem gross_lsi_implies_hypercontractive_of_hypotheses
    (D : DirichletMarkovSemigroup X) (ρ : ℝ) (hρ : 0 < ρ)
    (h_lsi   : D.SatisfiesLogSobolev ρ)
    (h_core  : CoreSemigroupInvariant D)
    (h_gen   : GeneratorCompat D)
    (h_sv    : StroockVaropoulos D)
    (h_approx : CoreLpApprox D) :          -- ← new 4th case-dependent hypothesis
    D.toMarkovSemigroup.IsHypercontractive ρ
```

## 3. The intended abstract glue (what we prove from the hypotheses)

Fix `1 < p ≤ q`, `0 < t`, `q ≤ q(t)`, and `f : L²` with `MemLp f (ofReal p)`.

**(G1) WLOG `f ≥ 0`.** Replace `f` by `|f|` (the `Lp` lattice absolute value).
`MemLp |f| (ofReal p)` (same a.e. modulus) and `eLpNorm |f| p = eLpNorm f p`.
For the orbit: `-|f| ≤ f ≤ |f|` ⇒ (by `P_positivity`/monotonicity)
`|P_t f| ≤ P_t |f|` a.e. ⇒ `eLpNorm (P_t f) q ≤ eLpNorm (P_t |f|) q` (`eLpNorm`
monotone in the modulus). So the bound for `|f| ≥ 0` gives the bound for `f`.

**(G2) Approximate.** Apply `CoreLpApprox` to the nonneg `f` to get core
`gₙ ≥ εₙ > 0` with `gₙ → f` in `L^p` and `P_t (coreToL2 gₙ) → P_t f` a.e.
Each `gₙ ≢ 0` (since `gₙ ≥ εₙ > 0` a.e. on a probability measure).

**(G3) Termwise core bound.** By `eLpNorm_orbit_le_of_core_pos` (with `εₙ`):
`eLpNorm (P_t (coreToL2 gₙ)) q ≤ eLpNorm (coreToL2 gₙ) p = eLpNorm gₙ p`.

**(G4) Pass to the limit.**
* `eLpNorm gₙ p → eLpNorm f p` (from `eLpNorm (f - gₙ) p → 0` + the `eLpNorm`
  triangle inequality, `p ≥ 1`).
* `eLpNorm (P_t f) q ≤ liminf eLpNorm (P_t (coreToL2 gₙ)) q` — **Fatou / lower
  semicontinuity of `eLpNorm` under `μ`-a.e. convergence** (`q ≥ 1`).
* Chain: `eLpNorm (P_t f) q ≤ liminf eLpNorm (P_t (coreToL2 gₙ)) q
  ≤ liminf eLpNorm gₙ p = lim eLpNorm gₙ p = eLpNorm f p`.

(`P_t f` in G2/G4 is the `L²` action — it is the same element whose `L^q`-norm
the conclusion bounds, so no extension of `P_t` off `L²` is needed.)

---

## 4. Questions to vet

**A. Soundness / non-circularity.** Is `CoreLpApprox` a genuine
density+regularity statement (not a disguised assumption of the conclusion)?
In particular: its content is "core+positive functions approximate nonneg
`L^p` elements with a.e.-convergent orbits" — it never mentions the
hypercontractive *inequality*, so feeding it `eLpNorm_orbit_le_of_core_pos`
should not be circular. Confirm, or identify any hidden circularity / vacuity.

**B. Sufficiency of the glue.** Do steps G1–G4 actually close the theorem from
`CoreLpApprox` + `eLpNorm_orbit_le_of_core_pos`? Specifically:
  - **G1**: is `|P_t f| ≤ P_t |f|` a.e. correct (positive/Markov operator), and
    does `eLpNorm` monotonicity in the modulus give the reduction?
  - **G4 Fatou**: is `eLpNorm` lower-semicontinuous under `μ`-a.e. convergence
    for exponent `ofReal q`, `q ≥ 1` (probability measure)? (We expect a
    `lintegral` Fatou / `eLpNorm_le_liminf`-type fact.) Any measurability or
    `∞`-value caveat?
  - Is the `eLpNorm`-triangle continuity `eLpNorm gₙ p → eLpNorm f p` correct
    for `p ≥ 1`?
  Flag any missing hypothesis or false sub-step.

**C. Formulation quality.** Is the predicate well-formed and the "right"
strength? Options to weigh:
  - sequence (`ℕ`) vs net — sequences suffice (`L^p` metrizable)?
  - **a.e. orbit convergence vs in-measure** — which is the better
    case-dependent demand? (a.e. is what Fatou wants directly; in-measure is
    what `L²`-continuity of `P_t` gives, then pass to an a.e. subsequence.)
    Should the predicate ask for in-measure (weaker, easier to discharge) and
    let the abstract proof extract the a.e. subsequence?
  - `1 ≤ p` vs `1 < p`; `f : Lp ℝ 2` (an `L²` element) + `MemLp · (ofReal p)`
    vs a bare function. Any improvement?

**D. (key) Difficulty of discharging `CoreLpApprox` for our target instance.**
The intended concrete instance is the **finite-dimensional standard Gaussian
`γ` on `ℝⁿ` with the Ornstein–Uhlenbeck semigroup** `P_t` (a diffusion; core =
`C^∞` functions with bounded derivatives, plus the strict-positive rpow
closure). Assess concretely how hard `CoreLpApprox` is there, and outline the
cleanest discharge. Our expected route:
  1. Given nonneg `f ∈ L²(γ) ∩ L^p(γ)`: truncate/mollify to get **bounded
     smooth** approximants `hₙ → f` in `L^p` **and** in `L²` (smooth compactly-
     supported / Hermite / heat-mollified functions are dense in `L^r(γ)` for
     all `1 ≤ r < ∞`).
  2. Add `1/n` to enforce **strict positivity**: `gₙ := hₙ' + 1/n ≥ 1/n > 0`
     (still smooth, bounded, core; still `→ f` in `L^p`/`L²`).
  3. Orbit convergence: `gₙ → f` in `L²` ⇒ `P_t gₙ → P_t f` in `L²`
     (`P_t` is an `L²`-contraction) ⇒ a **subsequence** converges `γ`-a.e.;
     pass to that subsequence (keeping `L^p`-convergence).
Is this route correct and standard? Pitfalls (e.g. simultaneous `L^p ∩ L²`
density of *bounded smooth strictly-positive* functions; whether truncation
preserves coreness; whether the `OU` core's bounded-derivative requirement
clashes with `+1/n`; the a.e. subsequence step)? Roughly how much
formalization effort, and is anything **not** routine?

**E. Better alternatives.** Is there a cleaner or weaker case-dependent
hypothesis that closes the same theorem with comparable or less abstract glue
(e.g. assuming `L^p`-contractivity of `P_t` + plain `L^p`-density of core, and
deriving orbit a.e.-convergence differently)? If so, sketch it.

Please give a verdict on A–E, correct any wrong sub-step, and state the
recommended final form of the predicate.

---

## 5. Verdict (deep-think, 2026-05-21) — APPROVED with one refinement

Overall: the glue G1–G4 is **mathematically sound and non-circular**; the only
change is to **decouple `P_t` from the predicate** (a strict improvement).

- **A (soundness):** Sound, non-circular. The predicate is purely structural
  (density of the strictly-positive core), never mentions the hypercontractive
  inequality or `q(t)`; feeding it `eLpNorm_orbit_le_of_core_pos` is valid.
  Non-vacuous (strictly-positive smooth functions are dense over a probability
  measure).
- **B (glue):** Sufficient and correct. G1: `(P_t)` positivity-preserving ⇒
  `-P_t|f| ≤ P_t f ≤ P_t|f|` ⇒ `|P_t f| ≤ P_t|f|` a.e.; `eLpNorm` monotone over
  a.e. inequalities ⇒ reduction valid. G4: `eLpNorm` triangle holds for `p ≥ 1`
  so `‖gₙ‖_p → ‖f‖_p`; lower-semicontinuity under a.e. convergence is Fatou —
  `lintegral_liminf_le` gives `‖P_t f‖_q ≤ liminf ‖P_t gₙ‖_q` (`q ≥ 1`, `x↦x^q`
  continuous monotone). No false sub-step.
- **C & E (KEY refinement): decouple `P_t`.** Instead of requiring
  `P_t (coreToL2 gₙ) → P_t f` a.e. in the predicate, require `gₙ → f` in **both
  `L^p` and `L²`**. Then the abstract glue does: `gₙ → f` in `L²` ⇒
  `P_t gₙ → P_t f` in `L²` (`L²`-contraction) ⇒ extract an a.e.-convergent
  **subsequence** (`MeasureTheory.tendsto_Lp_implies_tendsto_ae`) ⇒ run G3/G4
  along it (`L^p`-convergence persists on the subsequence). This removes `t` and
  `P_t` entirely from the case-dependent hypothesis — purely static
  density. Sequences suffice (`L^p` metrizable).
- **D (Gaussian/OU discharge): routine, standard.** (1) bounded
  smooth/mollified truncations are dense in `L^{max(p,2)}(γ)` ⇒ converge in both
  `L^p` and `L²` (probability measure); (2) the `+1/n` strict-positivity trick
  is "flawless" — constants are core and in every `L^r(γ)`, so `hₙ + 1/n` is
  core, `≥ 1/n > 0`, and `→ f`; (3) with the decoupled predicate the instance
  **does not even need the orbit a.e.-subsequence step** (abstract glue handles
  it universally). No non-routine pitfalls.

**Recommended final predicate (decoupled — no `P_t`, no `t`):**
```lean
def CoreLpL2Approx (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ {p : ℝ}, 1 ≤ p → ∀ (f : Lp ℝ 2 D.μ),
    MemLp (⇑f) (ENNReal.ofReal p) D.μ → 0 ≤ f →
    ∃ (g : ℕ → X → ℝ) (_hg : ∀ n, D.IsCore (g n)),
      (∀ n, ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ y ∂D.μ, ε ≤ g n y) ∧
      Filter.Tendsto (fun n => eLpNorm (⇑f - g n) (ENNReal.ofReal p) D.μ) atTop (nhds 0) ∧
      Filter.Tendsto (fun n => eLpNorm (⇑f - g n) 2 D.μ) atTop (nhds 0)
```
Rating: **Standard** (textbook density + Markov `L²`-contraction; the
abstract glue is the only formalization work, ~moderate).
