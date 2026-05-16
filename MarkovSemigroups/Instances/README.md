# `MarkovSemigroups/Instances/` — concordance (VIEW-ONLY)

Concrete, **sorry-free** instances of the abstract Markov-semigroup /
Bakry–Émery machinery. These are the "production" instances; the
honest-sorry experimental ones live in
[`WorkInProgress/`](WorkInProgress/README.md).

This file is a navigation aid only. It does not modify any `.lean`
source. Status is cross-checked against the repo-root
[`status.md`](../../status.md) (the canonical sorry/axiom audit).

| Module | Role | Canonical source | Status |
|--------|------|------------------|--------|
| `BrascampLieb.lean` | Brascamp–Lieb variance inequality for log-concave `μ = e^{-V}dx` on ℝⁿ (`Var_μ f ≤ ∫⟨∇f,(Hess V)⁻¹∇f⟩dμ`) and its Poincaré corollary `Var ≤ (1/ρ)∫‖∇f‖²`. The three "elementary" results (resolvent IBP, Bochner/Weitzenböck, weighted Young) are **promoted to `LogConcaveMeasure` structure fields**, not free axioms; `brascampLieb` and `brascampLieb_poincare` are proved from them. | Brascamp–Lieb, *J. Funct. Anal.* 22 (1976) 366–389; BGL-2014 §4.9. BGL local PDF is a publisher teaser (truncated), so the **analytic-spine cross-ref is Ledoux-2000** (Poincaré ↔ log-Sobolev limiting cases, §1.3, §4.6). | **0 sorry, 0 free axiom.** Fully proved. (status.md: `Instances/BrascampLieb` 1 decl, 0 sorry, 0 axiom.) |
| `Torus.lean` | Ornstein–Uhlenbeck / heat semigroup on `T^d_L = (ℝ/Lℤ)^d` with massive Laplacian `Δ − m²`: Fourier-mode decomposition `dz_k = −λ_k z_k dt + √2 dβ_k`, `λ_k = 4π²|k|²/L² + m²`. Provides `torusHeatSemigroup` (C₀-semigroup via hille-yosida), `torusOUSemigroup`, spectral gap `m² + 4π²/L²`, Bakry–Émery curvature `ρ = m²`, and GFF LSI. | Da Prato–Zabczyk, *Stochastic Equations in Infinite Dimensions*, Cambridge 2014, Ch. 5. Analytic background: Ledoux-2000 §1 (OU generator is `CD(1,∞)`; Gaussian = limiting/extremal case) and §1.3 Poincaré/log-Sobolev. | **0 sorry, 0 axiom.** Header module wiring the abstract OU instance to the torus. |
| `GFFIdentification.lean` | Identifies the OU invariant measure on `T^d` (generator `Δ − m²`) with the Gaussian free field of the gaussian-field library, both centered Gaussian with covariance `(−Δ + m²)⁻¹`, via `gaussian_measure_unique_of_covariance`. Free-field (P=0) case of stochastic quantization. Main result `torusOU_invariantMeasure_eq_gff`. | Nelson, "The free Markoff field," *J. Funct. Anal.* 12 (1973) 211–227; Simon, *The P(φ)₂ Euclidean QFT*, Princeton 1974, Ch. I. Lattice analogue / Green-function = covariance identity: Friedli–Velenik Ch. 8 (GFF as invariant measure of OU/Langevin dynamics; §8.4–8.5 Green-function representation). | **0 sorry, 0 axiom.** Header/identification module. |

## Gaps

None in this directory. All three modules are sorry-free and
free-axiom-free per `status.md`. The "three textbook results" once
flagged for `BrascampLieb` were discharged by promotion to
`LogConcaveMeasure` structure fields (`resolvent_ibp_axiom`,
`integrated_bochner_axiom` → structure fields; see `status.md`
Axioms / "Promoted to `LogConcaveMeasure` structure fields").

Caveat on sourcing: the local **BGL-2014 PDF is a truncated
publisher teaser** (8 pp.), so its §4.9 / Ch. 2 contents are *not*
verifiable from the local summary; for anything beyond the chapter
heading, cite **Ledoux-2000** (the full free survey covering the same
analytic program) rather than the BGL summary text.

## Cross-refs

- Brascamp–Lieb / log-concave Poincaré — analytic spine:
  [`refs/summaries/Ledoux-2000/01-geometric-aspects-of-diffusion-generators.md`](../../refs/summaries/Ledoux-2000/01-geometric-aspects-of-diffusion-generators.md)
  (OU generator `CD(1,∞)`, Poincaré/log-Sobolev as limiting cases),
  [`refs/summaries/Ledoux-2000/04-sobolev-inequalities-and-heat-kernel-bounds.md`](../../refs/summaries/Ledoux-2000/04-sobolev-inequalities-and-heat-kernel-bounds.md).
  BGL §4.9 heading only:
  [`refs/summaries/BGL-2014/00-index.md`](../../refs/summaries/BGL-2014/00-index.md)
  (teaser — flagged unreliable).
- Torus OU / heat semigroup:
  [`refs/summaries/Ledoux-2000/01-geometric-aspects-of-diffusion-generators.md`](../../refs/summaries/Ledoux-2000/01-geometric-aspects-of-diffusion-generators.md).
- GFF = OU invariant measure (lattice analogue, Green-function =
  covariance):
  [`refs/summaries/Friedli-Velenik/08-gaussian-free-field.md`](../../refs/summaries/Friedli-Velenik/08-gaussian-free-field.md).
- Repo-root audit: [`status.md`](../../status.md).
