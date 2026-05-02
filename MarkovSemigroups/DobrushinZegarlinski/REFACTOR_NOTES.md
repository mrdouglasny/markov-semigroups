# DobrushinZegarlinski — Refactor and Integration Notes

The new layer is intentionally written in parallel to the existing
`Dobrushin/` modules so the discrete TV theory is not perturbed.
This file collects the integration points where a future cleanup can
unify the two.

## 1. Folding `Dobrushin/NeumannSeries.lean` into `AbstractInfluenceMatrix`

`AbstractInfluence.lean` re-proves the row-sum / pointwise / Neumann
bounds from scratch. The proof is a literal port of
`MarkovSemigroups/Dobrushin/NeumannSeries.lean`, lines 87–243. If we
ever decide to deduplicate:

* Add a function
  `DobrushinCondition.toAbstract (γ : GibbsSpec I S) (hD : DobrushinCondition γ) :
   AbstractInfluenceMatrix I`
  which packages `γ.influenceCoeff`, `hD.α`, and the existing summability /
  bound axioms into the new structure.
* Replace `iterateInfluence` with `(hD.toAbstract).iterate` (or keep
  `iterateInfluence` as an `abbrev` for backward compatibility).
* Replace `iterateInfluence_row_summable_and_bound`,
  `iterateInfluence_pointwise_bound`, and `neumann_series_bound` with
  applications of the corresponding `AbstractInfluenceMatrix` lemmas.

The only nontrivial part is checking that the existing distance-aware
bounds (`iterateInfluence_dist_zero` etc.) port cleanly; they are
generic statements about a `d : I → I → ℕ` and an "influence range"
hypothesis, both of which can be re-stated for `AbstractInfluenceMatrix`
without loss.

Estimated effort: <1 day if we want to remove the duplication; the
two implementations are otherwise harmless.

## 2. Bridge `SatisfiesLSI` ↔ `DirichletSpace.SatisfiesLogSobolev`

`LocalLSI.lean` introduces a thin `SatisfiesLSI μ c` predicate stated
directly via `fderiv` and integral-of-norm-squared. This decouples
the analytic content of the Zegarlinski hypothesis from the heavier
Dirichlet-space typeclass.

For Bakry–Émery-type spaces (Gaussian, OU, etc.) the two predicates
agree; the bridge lemma should look like

```lean
lemma satisfiesLSI_of_dirichlet
    {ds : DirichletSpace E μ} (hds : ds.SatisfiesLogSobolev c)
    (h_riesz : ∀ f x, ‖fderiv ℝ f x‖ ^ 2 = ds.gradNormSq f x) :
    SatisfiesLSI μ c
```

with a converse under appropriate density of the core. This is a
single short bridge proof once the spaces line up.

## 3. `GibbsSpec`-to-`EuclideanSpace` topology adapter — **DONE**

Implemented in `DobrushinZegarlinski/EuclideanTransport.lean`. Exposes:

* `GibbsSpec.toEuclideanMeasure spec μ` — pushforward of `μ` from
  `SpinConfig Λ ℝ` to `EuclideanSpace ℝ Λ` via
  `(EuclideanSpace.equiv Λ ℝ).symm`.
* `isProbabilityMeasure_toEuclideanMeasure` — probability preservation
  (instance, automatic).
* `toEuclideanMeasure_apply` — explicit set-application formula.
* Global `MeasurableSpace` and `BorelSpace` instances on
  `EuclideanSpace ℝ Λ` (so callers don't have to declare them).

The main theorem `global_lsi_of_zegarlinski` now concludes
`SatisfiesLSI (spec.toEuclideanMeasure μ) (c · (1 - α))` directly.

Not yet provided: a `SatisfiesLSI ↔ Pi-norm-LSI` bridge that relates
the L²-norm gradient (used by `SatisfiesLSI`) to the L^∞-norm gradient
(natural on `Λ → ℝ`). In finite dim these are equivalent up to a
norm-comparison constant; downstream consumers can compose explicitly
if needed. Cleanest place to add this: `EuclideanTransport.lean` (a
single short lemma).

## 4. Textbook axioms — DZ layer is sorry-free (2 axioms remaining)

Now lives in `EntropyChainRule.lean`. The True placeholder has been
replaced with the real statement. Sub-lemma structure:

### Done

* `entropy_const`, `entropy_zero` — basic identities (proved).
* `entropy_nonneg` — proved via `ConvexOn.map_average_le` against
  Mathlib's `Real.convexOn_mul_log` and `Real.continuous_mul_log`.
  This is Jensen's inequality for `t ↦ t log t` on `[0, ∞)`.
* `EntropyIntegrable` — bundled hypothesis structure (nonneg `g`,
  integrability of `g` and `g · log g`).
* `EntropySmoothingIntegrable` — auxiliary integrability bundle for
  the smoothing operator (siteSmoothing-form, so `integral_sub`
  matches cleanly).
* `siteSmoothing` and basic properties (`_const`, `_nonneg`,
  `_eq_integral`) — proved.
* **`entropy_decomposition_single_site` (S1) — PROVED.** Reduces to
  `integral_siteSmoothing` (DLR-at-integral-level) plus pure
  algebraic rearrangement.

### Remaining (1 sorry in `EntropyChainRule.lean`)

**ALL `integral_siteSmoothing` lemmas PROVED:**
- `measurable_condDist_singleton` — `σ ↦ spec.condDist {x} σ` is
  measurable as a measure-valued map.
- `bind_condDist_singleton_eq` — DLR identity as Mathlib `Measure.bind`
  fixed point.
- `lintegral_siteSmoothing` — DLR-at-integral level for `ℝ≥0∞`-valued.
- `integral_siteSmoothing_nonneg` — Bochner-integral DLR for nonneg.
- `integrable_siteSmoothing_of_nonneg` — integrability of the smoothing
  (proved without circular dependency, via direct `lintegral_siteSmoothing`
  + `ENNReal.ofReal_toReal_le` bound).
- `integral_siteSmoothing` (general) — proved via pos/neg decomposition
  `g = max(g, 0) - max(-g, 0)`, applying the nonneg case and the
  integrability lemma twice, plus μ-a.e. linearity of `siteSmoothing`.

**Both originally-proposed axioms went through Gemini chat review
(gemini-3-pro-preview); one was REMOVED as mathematically false, the
other was substantially fixed.**

### REMOVED: `entropy_chain_rule_local` (false)

Originally proposed as
`Ent_μ(g) ≤ Σ_{x ∈ Λ} ∫ Ent_{γ.condDist {x} σ}(g) dμ(σ)`
without a coupling-dependent constant. **Gemini provided a clean
counterexample**: low-temperature Ising at `T → 0` has Dirac single-
site conditionals (RHS = 0 since each conditional is a Dirac) while
LHS > 0 for non-constant `g`. The cited Stroock-Zegarlinski result
is an *equivalence* between mixing and LSI, not a universal chain
rule. The actual DZ proof does not factor through such a separate
axiom — the chain rule is interleaved with local LSI and Neumann
decay in the assembly of `zegarlinski_lsi_inequality`.

### KEPT (with fixes): `zegarlinski_lsi_inequality` and `cov_entrywise_bound_of_zegarlinski`

Gemini flagged the following issues, all corrected:

1. **Logical flaw — no link between `spec` and `V`.** Original axiom
   let one pair a frozen-conditional `spec` (where `UniformLocalLSI`
   holds vacuously) with `V = 0` (where `ZegarlinskiCondition` holds
   vacuously), making the LSI conclusion false. **Fixed** by adding
   `[IsGibbsSpecificationFor spec V]` class as a hypothesis that
   captures the Boltzmann-weight identity linking the two.

2. **Algebra direction in `ZegarlinskiCondition`.** Original used
   `c · J ≤ α`, which is dimensionally and physically backward
   (stronger curvature `c` would make the bound *harder* to satisfy).
   **Fixed** to `J / c ≤ α`, matching Otto-Reznikoff (2007) and
   yielding the global LSI constant `c · (1 - α) = ρ - ‖W‖_op`
   correctly. `gradInteractionMatrix` and `toAbstract` updated to
   match.

3. **Lean integral-zero-on-garbage trap.** Original had only
   `Differentiable f`; for non-integrable `f` the RHS could evaluate
   to `0` (Lean convention) while the LHS was positive, breaking the
   inequality. **Fixed** by adding explicit integrability hypotheses
   on `f²`, `f² · log f²`, and `‖∇f‖²` to both the axiom and the
   `SatisfiesLSI` predicate.

4. **Citation correction.** Stroock-Zegarlinski 1992 is for *finite-
   spin / total-variation* Dobrushin-Shlosman; for the unbounded
   continuous-spin case formalized here, the correct citations are
   Otto-Reznikoff (2007) `J. Funct. Anal.` 243, Thm 1; Zegarlinski
   (1996) `Comm. Math. Phys.` 175; BGL §5.7.5.

5. **Missing `h_convex` for `cov_entrywise_bound_of_zegarlinski`.**
   The Helffer-Sjöstrand identity requires uniform strict log-concavity
   (Hess V ≥ cI everywhere). UniformLocalLSI alone is insufficient
   (counterexample: double-well V = x⁴ - 5x² satisfies LSI by strong
   convexity at infinity, but Hess V is negative near origin). Added
   `h_convex` field to the axiom hypothesis.

6. **L¹ → L² integrability for the covariance axiom.** The deep-review
   pass (still chat, but more thorough) flagged that L¹ hypotheses on
   coordinate functions don't suffice for Lean to evaluate the cov
   integrals correctly under HS-style requirements. Strengthened to
   L² (`Integrable (σ_x²)`, `Integrable (σ_y²)`).

7. **Soundness hole in `IsGibbsSpecificationFor`.** The placeholder
   form `class … : Prop where generates : True` admitted any
   (spec, V) pair, allowing `cov_entrywise_bound_of_zegarlinski` to
   produce false bounds for unrelated spec/V combinations. Replaced
   with a substantive `density_eq` field requiring the explicit
   Boltzmann-weight identity:

   `(spec.condDist {x} σ).map (·_x) = withDensity volume (a ↦ (1/Z) e^{-V(σ↦a at x)})`.

   Now constructing an instance requires actually proving that spec
   is generated by V via the Boltzmann weight — pphi2N must supply
   this when invoking the axiom.

**Final axiom inventory (DZ layer): 2 axioms, 0 sorries.** Both
axioms rated `Likely correct` after the corrections above. Audit
sources: GR (Gemini chat, gemini-3-pro-preview, three passes —
initial review, deeper-dive review of the cov axiom, and deeper-dive
review of the LSI axiom).

**Deeper-dive verdict on `zegarlinski_lsi_inequality` (LSI axiom):**
"completely mathematically sound and free of Lean unsoundness holes"
(Gemini, gemini-3-pro-preview, third pass). Specific confirmations:

- **No `h_convex` needed** for the LSI axiom (unlike the cov axiom).
  Otto-Reznikoff's proof uses martingale decomposition, not the
  Helffer-Sjöstrand inverse-Hessian identity, so log-concavity is
  *not* required. Local LSI alone suffices, allowing the axiom to
  apply to double-well-style potentials where Hess V can be negative
  near saddle points (provided the wells confine enough to satisfy
  local LSI via Holley-Stroock).
- **`Differentiable f` + the three integrability hypotheses are
  rigorous.** Effectively encodes f ∈ `W^{1,2}(μ) ∩ L²log L²(μ)`.
- **`Real.log 0 = 0` is the right convention.** No need to add
  `f ≠ 0 a.e.` hypothesis — `0 · log 0 = 0` matches the continuous
  extension, and the integrability of `f² log f²` is well-defined.
- **DLR + finite Λ + `IsProbabilityMeasure μ` + substantive
  `IsGibbsSpecificationFor` → unique global density `Z⁻¹ e^{-V}`.**
  Phase transitions / non-uniqueness ruled out for finite Λ.
- **Topological transport via `spec.toEuclideanMeasure`:** for finite
  Λ, the L^∞ product and L² topologies generate the same Borel σ-
  algebra, and the L² Riesz isomorphism makes
  `‖fderiv ℝ f x‖² = Σ_i |∂_i f|²` exact.
- **Constant `c·(1-α)` is the exact Otto-Reznikoff bound.**
  ρ_global ≥ ρ_local − ‖W‖_op ≥ c − c·α = c(1−α).

The original sorry-driven decomposition is preserved below for the
record, since both the chain rule and the LSI inequality are derivable
from existing lemmas + standard Mathlib infrastructure when the
formalization effort is funded.

### Earlier breakdown (now superseded by axioms)

Given S1 (`entropy_decomposition_single_site`) is proved, the chain rule
is mechanical Finset induction:

* Pick `x : Λ`. Apply S1: `Ent_μ(g) = ∫ Ent_ν_σ(g) dμ + Ent_μ(M_x g)`.
* The marginal `M_x g = siteSmoothing γ x g` only depends on `σ` outside
  `{x}` modulo the `consistent` axiom.
* Iterate over `Λ` via Finset induction, bounding the residual marginal
  entropy by single-site entropies on `Λ \ {x}`.

Required infrastructure:
* Marginal-measure on `Λ \ {x}`, OR a generalized chain rule statement
  parameterized by a `Finset Λ` of "swept" sites.
* Jensen-type bound: `entropy ν (siteSmoothing γ x g) ≤ entropy ν g`
  for `ν` a single-site conditional at `y ≠ x` (data-processing
  inequality for entropy under conditional expectation).

Estimated effort: ~1 week given the existing infrastructure.

* `entropy_chain_rule_local` proper: induction on a Finset of "swept"
  sites, repeatedly applying S1. The marginal-entropy term
  `Ent_μ(siteSmoothing γ x g)` is bounded inductively by the chain
  rule on `Λ \ {x}`, using a Jensen-type comparison
  `Ent_μ(siteSmoothing γ x g) ≤ Σ_{y ≠ x} ∫ Ent_{γ.condDist {y}}(g) dμ`.
  Requires marginal-measure infrastructure on `Λ \ {x}` (or a
  generalized statement parameterized by a Finset of "swept" sites).
  Estimated effort: 1 week.

The big-ticket bottleneck has shifted from S1 (now proved!) to
`integral_siteSmoothing` (the DLR-at-integral-level lemma) plus the
Finset induction. Both are mechanical given existing Mathlib
infrastructure; the chain rule total effort is now ~1.5–2 weeks
rather than 2–3 weeks.

### Bonus: |Λ| = 1 sanity check

For `|Λ| = 1` with site `x`, the conditional `γ.condDist {x} σ`
doesn't depend on `σ` (the boundary outside `{x}` is empty), so by
DLR `μ = γ.condDist {x} σ` for any `σ`. Then `siteSmoothing γ x g`
is a constant (= `∫ g dμ`), and `entropy_const = 0` gives the chain
rule with equality. This case can be proved cheaply once S1 is
available; left for future work.

## 5. pphi2N consumption surface

Downstream `pphi2N` should be able to pull the following from this
layer (no internal lemmas needed):

* `ZegarlinskiCondition V c` — the user-facing weak-coupling hypothesis.
* `UniformLocalLSI spec c` — the user-facing local-LSI hypothesis.
* `GibbsSpec.toEuclideanMeasure spec μ` — Euclidean pushforward.
* `global_lsi_of_zegarlinski` — the main theorem; will become non-`sorry`
  once item 4 above is completed (item 3 is now done).
* `AbstractInfluenceMatrix` and `iterate_*_bound` — for any direct
  Neumann-series application that doesn't fit the LSI shape exactly.

If pphi2N expects `interactionMatrix` for `V : (Λ → ℝ) → ℝ` (i.e.
without the `EuclideanSpace` wrapper), they should compose via
`PiLp.equiv 2 _`. We can add a thin alias here once we know the exact
signature pphi2N consumes.

## 6. Downstream-needed bridge: LSI → entrywise covariance

**Status:** out of scope for this layer; flagged for future work.

`pphi2N`'s `HSData.AdmitsThimbleLocal`
(`Pphi2N/QuantumHJ/TrialP3.lean:294`) consumes an *entrywise*
multiplicative bound

  |A(z(u))⁻¹_{xy}| ≤ K_FK · K⁻¹_{xy},   per (x, y),

which is strictly stronger than the global-LSI / spectral-gap
conclusion `global_lsi_of_zegarlinski` produces. The bridge from
LSI to entrywise covariance bound is the actual gating piece for the
strict-thermodynamic-limit mass-gap proof; pphi2N is currently using
the v3 finite-lattice resolvent identity route (with `log|Λ|`-coupled
N) and will only consume DZ once that's discharged in Lean (~5–7
weeks out from 2026-05-01).

### Three candidate routes

**(a) Helffer–Sjöstrand (recommended primary).**
For a log-concave measure `dμ = e^{-V} dx` on `EuclideanSpace ℝ Λ`,
the covariance of two test functions has the explicit representation

  Cov_μ(f, g) = ∫ ⟨∇f(σ), (Hess V(σ))⁻¹ ∇g(σ)⟩ dμ(σ)

(with the inverse interpreted on the `(Hess V + L)`-resolvent for the
generator `L` of the OU semigroup; the simplification to `Hess V⁻¹`
holds under enough regularity). For coordinate functions
`f(σ) = σ_x`, `g(σ) = σ_y`, this reduces to

  Cov_μ(σ_x, σ_y) = ∫ ((Hess V)⁻¹)_{xy} dμ.

Writing `Hess V = D + W` with `D` the diagonal (local potential
second derivatives) and `W` the off-diagonal interaction (which is
exactly `J_{xy}` from `interactionMatrix`), the Neumann series

  (D + W)⁻¹ = D⁻¹ Σ_n (-D⁻¹ W)ⁿ

gives an *entrywise* bound on `((Hess V)⁻¹)_{xy}` from
`AbstractInfluenceMatrix.iterate_pointwise_bound` applied to
`D⁻¹ W = c · J` (with `c` the inverse local Hessian magnitude
= local LSI constant ⁻¹).

Reference: BGL §4.5 ("Variance and covariance under log-concavity"),
Helffer & Sjöstrand 1994 ("On the correlations for Kac-like models in
the convex case"), Naddaf & Spencer 1997.

This route is the cleanest because:
* The `interactionMatrix V` definition we already have IS the relevant
  off-diagonal piece of `Hess V`.
* `AbstractInfluenceMatrix` already provides the entrywise Neumann
  bound (`iterate_pointwise_bound`) we need.
* The integral form ties directly into measure-theoretic existing
  Mathlib infrastructure (`integral_smul`, `Measure.map`, etc.).

The remaining content is: (i) prove the Helffer–Sjöstrand identity,
(ii) the entrywise inverse-Hessian bound, (iii) bound the integral
of the entrywise quantity over μ.

Estimated effort once unblocked: 2–3 weeks.

**(b) Bakry–Émery Γ₂ + diamagnetic.**
Use the existing `Abstract/HolleyStroock.lean` (LSI for log-concave
perturbations) plus `pphi2N`'s `Thimble/DiamagneticInequality.lean` to
get entrywise bounds via diamagnetic comparison. Indirect: the Bakry–
Émery inequality gives variance / spectral-gap bounds, which need an
extra polarization step (Cov(f,g) = ¼(Var(f+g) - Var(f-g))) to extract
covariance. Combined with diamagnetic, this can give entrywise bounds
on |Cov(σ_x, σ_y)|, but the route through polarization is loose and
typically gives constants worse by a factor of 2 or more vs. (a).

Estimated effort: 2–3 weeks. Less recommended than (a).

**(c) Brascamp–Lieb on linear functionals + polarization.**
We already have `Instances/BrascampLieb.lean` proving the BL variance
bound `Var_μ(f) ≤ ∫ ⟨∇f, (Hess V)⁻¹ ∇f⟩ dμ`. Applied to coordinate
functions `f = σ_x` and combined with polarization, this gives the
same conclusion as (a). The proof is essentially equivalent to (a) at
the level of mathematical content; the difference is which existing
infrastructure is leveraged.

Estimated effort: 1–2 weeks (smallest because BL is already proved
in our project). Likely the *fastest* path to a working bridge,
though (a) gives a more direct / canonical statement.

### Recommendation

**Route (a) for the canonical statement, but route (c) if speed matters.**

The end output of either is the same lemma:

```lean
theorem cov_entrywise_bound_of_zegarlinski
    {spec : GibbsSpec Λ ℝ} {V : EuclideanSpace ℝ Λ → ℝ} {c : ℝ}
    (h_local : UniformLocalLSI spec c)
    (h_weak : ZegarlinskiCondition V c)
    (μ : Measure (SpinConfig Λ ℝ)) [IsProbabilityMeasure μ]
    (h_gibbs : IsGibbsMeasure spec μ) (x y : Λ) :
    |∫ σ, σ x * σ y ∂μ - (∫ σ, σ x ∂μ) * (∫ σ, σ y ∂μ)|
      ≤ (1 / c) * (h_weak.toAbstract).neumann_entrywise x y
```

where `neumann_entrywise x y := ∑' n, iterate n x y` (already proved
bounded by `1/(1-α)` via `neumann_series_pointwise_bound`).

This file (`DobrushinZegarlinski/`) is the right home for this
theorem when work begins. Suggested filename:
`DobrushinZegarlinski/EntrywiseCovariance.lean`.
