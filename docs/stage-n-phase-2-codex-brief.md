# Codex hand-off — Phase 2 of the Lp-carrier MarkovSemigroup refactor

**Mission**: build the concrete `DirichletMarkovSemigroup (Fin n → ℝ)`
instance for the multivariate standard Gaussian OU semigroup, using
the new Phase 1 Lp-carrier framework. Concretely: instantiate the
Mehler semigroup as an `Lp ℝ 2 (γFin n) →L[ℝ] Lp ℝ 2 (γFin n)` operator
family, prove all 8 `MarkovSemigroup` fields, and assemble the
`DirichletMarkovSemigroup` bundle. **No new axioms.** Estimated
~3-5 active days.

This is Phase 2 of a 3-phase project; Phase 1 (the abstract
Lp-carrier refactor) landed on main at commit `e1e2011`. Phase 3
(gaussian-hilbert wire-in to discharge
`ouSemigroupAct_eLpNorm_hypercontractive`) comes after this.

## Repository setup

- **Repo**: `~/Documents/GitHub/markov-semigroups`
- **Base branch**: `main` at `e1e2011` (includes Phase 1's Lp-carrier
  refactor and the multivariate Gaussian BE-instance from N1).
- **Working branch**: `feat/lp-carrier-stdGaussianFin-dirichletmarkov`
- Run with `isolation: "worktree"`.
- Build: `lake build` from the repo root.

## Reading list (in order, before any code)

1. **`docs/lp-carrier-refactor-design.md`** (this repo) — overall
   design, especially the Phase 2 section.
2. **`MarkovSemigroups/Abstract/Hypercontractivity.lean`** — read the
   new `MarkovSemigroup` (line 78) and `DirichletMarkovSemigroup`
   (line 149) structure definitions and their 22 fields. Especially:
   * The `hρ : 0 < ρ` hypothesis on `gross_lsi_implies_hypercontractive`
     (line 261) — your wire-in will pass `1 > 0` here.
   * The `coreToL2` helper at line 190.
3. **`MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean`** —
   the existing multivariate Gaussian BE-instance + pointwise
   infrastructure. Especially:
   * `γFin n : Measure (Fin n → ℝ)` (line 31)
   * `ouShiftFin`, `ouSemigroupFin` (lines 39-45)
   * `IsCoreFin` (line 137), and its closure lemmas
   * `ouSemigroupFin_zero/mean/contraction/selfAdjoint/compose` (lines
     1017, 1049, 1128, 1264, 1358)
   * `ouSemigroupFin_gradient_decay` (line 1812)
   * `ouSemigroupFin_ergodic`, `ouSemigroupFin_entropy_sq_ergodic`
     (lines 2284, 2400)
   * `stein_partialDeriv_ouShiftFin` (line 242) — the sectionwise
     Stein identity
   * `ouSemigroupFin_preserves_IsCore` (line 2771) — vetted axiom
   * `stdGaussianFin.bakryEmerySpace` (line 2814) — the BE instance
     (will be cited but not consumed directly; you're building a
     parallel Lp-flavored instance)
4. **`MarkovSemigroups/Instances/WorkInProgress/EuclideanStein.lean`** —
   particularly `gaussian_dirichlet_form_identity` (1D Stein-based
   energy-derivative identity at `t=0`). Phase 2's `energy_eq_deriv`
   will need a Fubini lift of this.
5. **`.lake/packages/HilleYosida/HilleYosida/StronglyContinuousSemigroup.lean`** —
   the strong-continuity API you'll mirror.
6. **`~/.claude/AXIOM_AUDIT_FORMAT.md`** — audit-doc conventions.

After reading, write a one-paragraph scope summary and **pause for
confirmation** before writing code.

## Anti-delegation guards (non-negotiable)

- **No new axioms.** If you genuinely cannot prove a field (e.g.
  `energy_eq_deriv` stalls), **stop and report**. Don't silently add
  an axiom.
- **No `:= by simpa using upstream` delegations** that just rename an
  existing axiom or proved theorem.
- **No `sorry` in committed code.** Use `sorry` during development if
  necessary, but the final commit must be sorry-free.
- **Do not modify Phase 1 files** (`Abstract/Hypercontractivity.lean`)
  or the BE-instance file (`EuclideanFin.lean`) other than possibly
  adding a small `private` helper if needed. The main work lives in a
  new file.
- **Do not modify gaussian-hilbert** — that's Phase 3.

## Deliverables

### 1. New file: `MarkovSemigroups/Instances/WorkInProgress/EuclideanFinLp.lean`

Approximate structure (follow the design + this skeleton):

```lean
import MarkovSemigroups.Abstract.Hypercontractivity
import MarkovSemigroups.Instances.WorkInProgress.EuclideanFin

namespace GaussianFin

open MeasureTheory ENNReal

/-! # Lp-valued multivariate Gaussian OU semigroup -/

variable {n : ℕ}

/-- The multivariate OU semigroup at time `t` as a bounded linear
operator on `L²(γFin n)`. Well-defined on a.e.-equivalence classes
because the Mehler integral respects a.e.-equality of inputs. -/
noncomputable def ouSemigroupFinLp (t : ℝ) :
    Lp ℝ 2 (γFin n) →L[ℝ] Lp ℝ 2 (γFin n) := ...

/-- The Lp action agrees a.e. with the pointwise action on a representative. -/
theorem ouSemigroupFinLp_coeFn_ae (t : ℝ) (f : Lp ℝ 2 (γFin n)) :
    (ouSemigroupFinLp t f : (Fin n → ℝ) → ℝ) =ᵐ[γFin n]
      ouSemigroupFin t ((⇑f) : (Fin n → ℝ) → ℝ) := ...

-- Then 8 lemmas establishing the MarkovSemigroup laws:
theorem ouSemigroupFinLp_zero :
    ouSemigroupFinLp (n := n) 0 = ContinuousLinearMap.id ℝ (Lp ℝ 2 (γFin n)) := ...

theorem ouSemigroupFinLp_semigroup (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ouSemigroupFinLp (n := n) (s + t) =
    (ouSemigroupFinLp s).comp (ouSemigroupFinLp t) := ...

theorem ouSemigroupFinLp_strong_cont (f : Lp ℝ 2 (γFin n)) :
    Filter.Tendsto (fun t : ℝ => ouSemigroupFinLp (n := n) t f)
      (nhdsWithin 0 (Set.Ici 0)) (nhds f) := ...

theorem ouSemigroupFinLp_contraction (t : ℝ) (ht : 0 ≤ t) :
    ‖ouSemigroupFinLp (n := n) t‖ ≤ 1 := ...

theorem ouSemigroupFinLp_conservation (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (γFin n)) (hf : ∀ᵐ x ∂(γFin n), (⇑f : (Fin n → ℝ) → ℝ) x = 1) :
    ouSemigroupFinLp t f = f := ...

theorem ouSemigroupFinLp_positivity (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (γFin n)) (hf : 0 ≤ f) :
    0 ≤ ouSemigroupFinLp t f := ...

theorem ouSemigroupFinLp_symmetric (t : ℝ) (ht : 0 ≤ t)
    (f g : Lp ℝ 2 (γFin n)) :
    ⟪f, ouSemigroupFinLp t g⟫_ℝ = ⟪ouSemigroupFinLp t f, g⟫_ℝ := ...

/-! ## The MarkovSemigroup instance -/

noncomputable def markovSemigroup (n : ℕ) :
    MarkovSemigroup.MarkovSemigroup (Fin n → ℝ) := {
  μ := γFin n
  hμ := inferInstance
  P := ouSemigroupFinLp
  P_zero := ouSemigroupFinLp_zero
  P_semigroup := ouSemigroupFinLp_semigroup
  P_strong_cont := ouSemigroupFinLp_strong_cont
  P_contraction := ouSemigroupFinLp_contraction
  P_conservation := ouSemigroupFinLp_conservation
  P_positivity := ouSemigroupFinLp_positivity
  P_symmetric := ouSemigroupFinLp_symmetric
}

/-! ## IsCoreFin elements of L²(γFin n) -/

theorem isCoreFin_memLp (f : (Fin n → ℝ) → ℝ) (hf : IsCoreFin f) :
    MemLp f 2 (γFin n) := ...   -- bounded function on probability space

/-! ## The energy_eq_deriv compatibility (the hard one) -/

/-- The Dirichlet-form / generator compatibility for the multivariate
Gaussian OU semigroup.

For IsCoreFin functions f, g:
  `(d/dt)|_{t=0+} ⟨[f], P_t [g]⟩_{L²(γ_n)} = -ouEnergyFin f g`.

Proved via Fubini lift of the 1D `gaussian_dirichlet_form_identity`
(Stein + IBP at t = 0). -/
theorem ouSemigroupFin_energy_eq_deriv (f g : (Fin n → ℝ) → ℝ)
    (hf : IsCoreFin f) (hg : IsCoreFin g) :
    HasDerivWithinAt
      (fun t : ℝ => ⟪(isCoreFin_memLp f hf).toLp f,
                     ouSemigroupFinLp t ((isCoreFin_memLp g hg).toLp g)⟫_ℝ)
      (-(ouEnergyFin f g)) (Set.Ici 0) 0 := ...

/-! ## The DirichletMarkovSemigroup instance -/

noncomputable def stdGaussianFin_dirichletMarkovSemigroup (n : ℕ) :
    DirichletMarkovSemigroup (Fin n → ℝ) := {
  toMarkovSemigroup := markovSemigroup n
  energy := ouEnergyFin
  energy_symm := ...                  -- from BE instance
  energy_nonneg := ...                -- from BE instance
  IsCore := IsCoreFin
  IsCore_const := ...                 -- from BE instance
  IsCore_add := ...                   -- from BE instance
  IsCore_smul := ...                  -- from BE instance
  energy_add_left := ...              -- from BE instance (energy is integral of Γ)
  energy_smul_left := ...
  energy_const := ...
  IsCore_memLp := isCoreFin_memLp
  energy_eq_deriv := ouSemigroupFin_energy_eq_deriv
}

end GaussianFin
```

Approximate line budget: **~500-800 lines** (substantial because each
of the 8 Markov fields needs a real proof, and the energy_eq_deriv
field is non-trivial Stein-IBP work).

### 2. Update `MarkovSemigroups.lean` (library root)

Add an import for the new file.

### 3. Update `AXIOM_AUDIT.md`

Add a short note in the GaussianFin section about Phase 2 of the
Lp-carrier refactor. No new axioms expected; the count stays at 11.

## Sub-stage checkpoints (recommended order)

| Sub-stage | Estimated effort | Why this order |
|---|---|---|
| 2.0: `ouSemigroupFinLp` definition + `ouSemigroupFinLp_coeFn_ae` | ~0.5-1 day | Foundation — every field depends on this |
| 2.1: P_zero, P_conservation, P_positivity, P_symmetric | ~0.5 day | Mechanical from existing pointwise proofs |
| 2.2: P_contraction (op norm) | ~0.5 day | Jensen / L²-contraction lift |
| 2.3: P_semigroup | ~0.5-1 day | Composition equality via `ouSemigroupFin_compose` lifted |
| 2.4: P_strong_cont | ~1 day | DCT-based, new analytic content |
| 2.5: isCoreFin_memLp + Dirichlet form fields | ~0.5 day | Bounded function on probability space |
| 2.6: energy_eq_deriv | ~1-2 days | **Hardest**. Fubini lift of 1D Stein identity at t=0 |
| 2.7: Assembly + smoke test | ~0.5 day | Confirm `stdGaussianFin_dirichletMarkovSemigroup 2` typechecks |

## Tactical recommendations

1. **`ouSemigroupFinLp` definition**: Use `LinearMap.mkContinuous` with
   the L²-contraction bound directly. The key technical move: show that
   the map `f₀ ↦ ouSemigroupFin t f₀` from L²-representatives respects
   a.e.-equality and gives an L² element. Mathlib's
   `MeasureTheory.MemLp.toLp_congr_ae` and `Lp.coeFn_congr` are useful.

2. **`P_zero`**: Use `ContinuousLinearMap.ext` and `Lp.ext` (a.e.-equality)
   to reduce to the pointwise `ouSemigroupFin 0 f = f` fact.

3. **`P_conservation`**: For an Lp element `f` with `f =ᵐ 1`, we have
   `(P t f)(x) = ∫ y, f(...) dγ = ∫ y, 1 dγ = 1` a.e. So `P t f =ᵐ 1 =ᵐ f`,
   i.e., `P t f = f` in Lp.

4. **`P_strong_cont`**: For each `f : Lp ℝ 2 γ_n` and ε > 0, find δ > 0
   such that `‖P t f - f‖_{L²} < ε` for `t ∈ [0, δ)`. Density of IsCoreFin
   in L² + uniform-on-IsCoreFin convergence + L²-contraction. May require
   ~100-200 lines.

5. **`P_semigroup`**: The pointwise `ouSemigroupFin_compose` has an
   `IsCoreFin f` hypothesis. To lift to Lp, extend by density via L²-norm
   continuity of both sides. Or: prove the Fubini-on-Mehler-product
   directly for any `f : Lp ℝ 2 γ_n`.

6. **`energy_eq_deriv`**: The 1D analogue is
   `gaussian_dirichlet_form_identity` in `EuclideanStein.lean` (Stein
   identity + IBP at t = 0). Multivariate lift via Fubini: split the
   integral `∫ f · P_t g dγ_n` over the first coordinate; differentiate
   in t under the 1D-section integral using the 1D identity; sum over
   coordinates. The `stein_partialDeriv_ouShiftFin` already-proved
   helper (`EuclideanFin.lean:242`) is the key input. **If this stalls
   past 2 active days, stop and report** rather than guess.

## Final reporting

When you finish:

1. Final commit hash on `feat/lp-carrier-stdGaussianFin-dirichletmarkov`.
2. Worktree path.
3. `lake build` status (full clean expected).
4. `#print axioms stdGaussianFin_dirichletMarkovSemigroup` — expected
   closure: `[propext, Classical.choice, Quot.sound,
   ouSemigroupFin_l2_sq_hasDerivWithinAt,
   ouSemigroupFin_preserves_IsCore,
   ouSemigroupFin_entropy_sq_decay_bound]`. Anything else is unexpected.
5. Line counts per sub-stage.
6. Smoke test: `example : DirichletMarkovSemigroup (Fin 2 → ℝ) :=
   stdGaussianFin_dirichletMarkovSemigroup 2` typechecks.
7. Any deviations from the design.

If you hit a true blocker requiring a new axiom, **stop and report**
rather than adding it. We'll consult on whether to vet + add or find
another route.

## Risks and exit ramps

### Risk 1: `energy_eq_deriv` is harder than expected

The multivariate Stein-IBP identity at t=0 is the load-bearing piece.
If the Fubini-coordinate-decomposition route doesn't close after ~2
days, possible alternatives:
- Factor a clearly-named helper lemma (not an axiom) that captures
  the multivariate Stein identity, and prove it separately.
- Use a direct PDE-style argument (differentiate the Mehler integral
  under the integral sign at t=0).

### Risk 2: `P_strong_cont` density argument

The DCT-based strong-continuity proof on Lp may run into measurability
or integrability subtleties. If the direct route stalls, the fallback
is density of IsCoreFin in L² (proven elsewhere) + uniform L²-norm
convergence on a dense subset.

### Risk 3: `P_semigroup` extension from IsCoreFin to Lp

The IsCoreFin → Lp extension by density uses operator-norm continuity
of both sides. If `ContinuousLinearMap.ext_on` doesn't apply directly,
the manual Lp.ext path is always available.

In all three cases: **prove or stop**. Do not add axioms.

## Estimated total

~500-800 lines, ~3-5 active days.
