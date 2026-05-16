# MarkovSemigroups/Diffusion

**View-only concordance — do not treat as build documentation.**
Generated 2026-05-16 by static read of module docstrings + repo
`status.md` + `refs/summaries/`. No `.lean` file was modified.

Layer 2 of the abstraction hierarchy: the *carré du champ* refinement
of the abstract Dirichlet-form layer (`Abstract/`). A
`BakryEmerySpace` adds the squared-gradient operator Γ, the iterated
Γ₂, and a curvature lower bound ρ > 0 on top of a `DirichletSpace`.
From CD(ρ, ∞) one derives Poincaré, log-Sobolev, and exponential
variance/entropy decay; the Gaussian Ornstein–Uhlenbeck prototype is
the canonical instance (CD(1, ∞)). No manifold or metric is assumed —
the algebra is the abstract diffusion generator.

This is the analytic spine of the library. Concrete instances (ℝⁿ,
Tᵈ) live under `Instances/`, not here.

## Modules

| Module | Role | Canonical source | Status |
|--------|------|------------------|--------|
| `CarreDuChamp.lean` | `BakryEmerySpace` typeclass = `DirichletSpace` + Γ + curvature ρ; proves Poincaré(ρ) and `variance_decay` Var(P_t f) ≤ e^{−2ρt}Var(f) | Ledoux 2000 §1.1–1.2 (Γ = ½(L(fg)−fLg−gLf); diffusion chain rule (1.3); IBP (1.4)) ≈ BGL Part I | sorry-free, axiom-free |
| `BakryEmery.lean` | Bakry–Émery criterion: Γ₂ ≥ ρΓ ⟹ LSI(ρ) and Poincaré(ρ); OU has ρ = 1; Δ−m² on Tᵈ has ρ = m² | Ledoux 2000 §1.2, Def. 1.2 (CD(R,n)), Lemma 1.2/1.3 (commutation); Bakry–Émery LNM 1123 (1985); BGL Ch. 1, 5 | sorry-free, axiom-free |
| `L2Semigroup.lean` | Bridge from `BakryEmerySpace.semigroup` (acting on X → ℝ) to the `hille-yosida` `StronglyContinuousSemigroup` on L²(μ); energy identity d/dt ∫(P_t f)² = −2 E(P_t f) | Guionnet–Zegarliński Ch. 1, esp. Def. 1.1–1.5 and **Thm 1.7 (Hille–Yosida for Markov semigroups, pp. 8–14)**; BGL Ch. 1; Engel–Nagel Ch. II | **1 sorry** (generator step of the energy identity — stated as a theorem-with-sorry by design; see Gaps) |
| `InvariantMeasure.lean` | Invariant-measure theory: μ invariant ⟺ ∫ Lf dμ = 0; OU invariant measure is Gaussian; spectral gap ⟹ uniqueness | Ledoux 2000 §1.1 (invariance/reversibility: ∫Lf dμ = 0, ∫fLg = ∫gLf); FOT Ch. 1 (symmetric forms / Markovian semigroups); BGL Ch. 4; Da Prato–Zabczyk Ch. 11 | sorry-free, axiom-free |
| `OrnsteinUhlenbeck.lean` | Abstract OU semigroup on a Hilbert space with trace-class covariance C; Mehler's formula; contraction on L²(γ_C); Bakry–Émery ρ = λ_min(C⁻¹) | Ledoux 2000 §1.1–1.2 (OU is the running example; OU generator is CD(1,∞)); GZ Ch. 1 (OU as Exercise 1.4/1.6, Mehler form); BGL Ch. 2 | sorry-free, axiom-free |

Status corroborated by repo `status.md`: *"Zero sorry's in the main
tree (Abstract/, Diffusion/, …)"* with the Diffusion row listing 5
modules / 0 sorry / 0 axiom. The single `sorry` token in
`L2Semigroup.lean` (line 47) sits inside the **module docstring**
describing the deliberate design choice, not in compiled tactic code —
hence the main-tree count remains zero.

## Gaps

- **Γ as energy measure / LeJan refinement absent.** The Γ here is the
  pointwise carré du champ of a *diffusion* generator (Ledoux §1.1).
  The measure-valued energy-measure refinement and the LeJan local
  representation of the strongly-local part of a regular Dirichlet
  form are **not** present in this directory. Canonical source:
  Fukushima–Oshima–Takeda §3.2, *Formulae of Beurling–Deny and LeJan*,
  **Thm 3.2.1 p. 120**, LeJan refinement **pp. 123–130**. Tracked in
  [`plans/beurling-deny.md`](../../plans/beurling-deny.md).
- **L² semigroup bridge incomplete.** `L2Semigroup.lean` states the
  energy identity with a `sorry` on the generator step and leaves the
  full unbounded-generator L²(μ) operator theory unformalized: (1)
  realizing `BakryEmerySpace.semigroup` as operators on `Lp ℝ 2 μ`,
  (2) strong continuity on L², (3) hooking into
  `hille-yosida.StronglyContinuousSemigroup`. The missing analytic
  input is the **unbounded self-adjoint spectral theorem / Hille–Yosida
  generation theorem** (GZ Ch. 1 Thm 1.7; Engel–Nagel Ch. II) — each
  step is standard but needs substantial Mathlib Lp plumbing.
- **CD(R,n) finite-dimension branch unused.** Modules consume only the
  pure-curvature CD(ρ, ∞) condition (Γ₂ ≥ ρΓ). The finite-n
  curvature–dimension hypothesis and its sharp-constant / comparison
  consequences (Ledoux §1.2 Def. 1.2, Lemma 1.3; §3) are not exercised
  here.
- **Reversibility vs. invariance.** `InvariantMeasure.lean` works at
  the invariance level (∫Lf dμ = 0). The FOT symmetric-form
  (reversibility ⟺ self-adjoint generator) machinery is cited but the
  full Dirichlet-form symmetry equivalence is in `Abstract/`, not
  re-derived here.

## Cross-refs

- Ledoux 2000 — [`refs/summaries/Ledoux-2000/01-geometric-aspects-of-diffusion-generators.md`](../../refs/summaries/Ledoux-2000/01-geometric-aspects-of-diffusion-generators.md)
  (§1.1 Γ, §1.2 Γ₂ / CD(R,n) / commutation Lemmas 1.2–1.3) ·
  [`00-index.md`](../../refs/summaries/Ledoux-2000/00-index.md)
- Guionnet–Zegarliński 2002 — [`refs/summaries/Guionnet-Zegarlinski/01-markov-semigroups.md`](../../refs/summaries/Guionnet-Zegarlinski/01-markov-semigroups.md)
  (Defs 1.1–1.5, Thm 1.7 Hille–Yosida, OU example) — relevant to
  `L2Semigroup.lean` and the `hille-yosida` dependency
- Fukushima–Oshima–Takeda 2011 —
  [`refs/summaries/Fukushima-Oshima-Takeda/01-basic-theory-dirichlet-forms.md`](../../refs/summaries/Fukushima-Oshima-Takeda/01-basic-theory-dirichlet-forms.md)
  (Ch. 1 symmetric forms / Markovian semigroups) ·
  [`03-scope-of-dirichlet-forms.md`](../../refs/summaries/Fukushima-Oshima-Takeda/03-scope-of-dirichlet-forms.md)
  (§3.2 Beurling–Deny / LeJan, Thm 3.2.1 p. 120, pp. 123–130 — the
  Gaps anchor)
- Bakry–Gentil–Ledoux 2014 — [`refs/summaries/BGL-2014/00-index.md`](../../refs/summaries/BGL-2014/00-index.md)
  (truncated teaser; analytic program covered by Ledoux-2000)
- Plan — [`plans/beurling-deny.md`](../../plans/beurling-deny.md)
  (energy-measure / LeJan refinement roadmap)
