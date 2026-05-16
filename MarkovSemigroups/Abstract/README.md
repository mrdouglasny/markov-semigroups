# MarkovSemigroups/Abstract

Layer 1 of the abstraction hierarchy: the analytic spine of functional
inequalities with **no gradient, metric, or manifold structure** assumed.
A `DirichletSpace` bundles a probability measure with a symmetric energy
form; on top of it sit Poincaré, log-Sobolev, the Holley–Stroock
perturbation lemma, the Gross hypercontractivity equivalence, and the
Herbst concentration consequence. This is the entry point consumed by the
`Diffusion/`, `Convergence/`, and `DobrushinZegarlinski/` layers.

## Modules

| Module | Role (from docstring) | Canonical source | Status |
|--------|-----------------------|------------------|--------|
| `DirichletForm.lean` | `DirichletSpace`: probability measure + symmetric energy form; `variance`, `entropy`. Minimal structure for Poincaré/LSI. | Fukushima–Oshima–Takeda Ch. 1 (Basic theory of Dirichlet forms, pp. 3–65; closed forms/semigroups §1.3 p. 16, Markovian semigroups §1.4 p. 25). Ledoux 2000 §1 (Γ form, eqn (1.4)). | sorry-free, 0 axioms |
| `Poincare.lean` | `PoincareInequality` predicate; `poincare_of_spectralGap`; `variance_exponential_decay`. Optimal constant = spectral gap of the generator. | Guionnet–Zegarliński Ch. 2 (Spectral Gap Inequality and L² Ergodicity, pp. 15–22; "directly underlies `Abstract/Poincare.lean`"). Also BGL 2014 Ch. 4 (per module docstring). | sorry-free, 0 axioms |
| `LogSobolev.lean` | `LogSobolevInequality` predicate; `gross_log_sobolev_gaussian`; `logSobolev_implies_poincare`; `entropy_exponential_decay`. | Guionnet–Zegarliński Ch. 4 (Logarithmic Sobolev Inequalities and Hypercontractivity, pp. 33–48). Ledoux 2000 §4.2 (Gross equivalence, pp. 346–362). Also Gross (1975); BGL 2014 Ch. 5 (per module docstring). | sorry-free, 0 axioms |
| `HolleyStroock.lean` | `holleyStroock_logSobolev` / `holleyStroock_poincare`: bounded perturbation `μ₁ = (1/Z)e^{−V}μ₀` keeps LSI with `ρ₁ = ρ₀·e^{−osc(V)}`. | Guionnet–Zegarliński **Property 4.6, article p. 40 (PDF p. 43)** — the exact statement formalized here. Holley–Stroock (1987). | sorry-free, 0 axioms |
| `Hypercontractivity.lean` | `MarkovSemigroup` (L²-carried), `DirichletMarkovSemigroup`, `IsHypercontractive`; Gross LSI ⇔ hypercontractivity. | Ledoux 2000 **Corollary 4.3** (Gross hypercontractivity equivalence, §4.2 pp. 346–362) and van Handel **§8.2** (pp. 260–269, time–exponent relation `e^{2t/C}=(q(t)−1)/(p−1)`) — the authoritative vetting citations. GZ Ch. 4 Theorem 4.1. | sorry-free, **3 axioms** |
| `Concentration.lean` | Borell/Herbst sub-Gaussian concentration of Lipschitz functions from LSI: `μ(F−E F > t) ≤ exp(−c t²/(2L²))`. | van Handel Ch. 3 §3.3 (The entropy method / Herbst argument, pp. 55–63). BGL 2014 §5.4 (Herbst's lemma); Ledoux (2001) §1; Otto–Villani (2000). | sorry-free, **2 axioms** |

Directory totals (status.md row): 6 modules, 0 sorries, 4 distinct
audited-axiom families; per-file grep confirms 3 axioms in
`Hypercontractivity.lean` and 2 in `Concentration.lean` (no other axioms),
all sorry-free.

### Axioms in this layer (textbook, audited)

- `Hypercontractivity.lean`: `gross_lsi_implies_hypercontractive`
  (Gross 1975 Thm 1), `gross_hypercontractive_implies_lsi` (Gross 1975
  Thm 2) — both stated on the bundled `DirichletMarkovSemigroup`;
  `stroock_varopoulos` (BGL Prop 1.7.1 / §1.7, vetted **Standard**,
  intermediate step toward a Gross discharge, no internal consumers yet).
- `Concentration.lean`: `herbst_mgf_bound` (BGL §5.4.1; the full theorem
  `lipschitz_concentration_of_lsi` is *proven* from it via Mathlib
  Chernoff), `poincare_of_lsi` (BGL Prop 5.1.3; LSI ⇒ Poincaré, the
  Lipschitz variance bound is *proven* from it).

## Gaps

- **Sobolev / ultracontractivity not formalized here.** The classical
  Sobolev inequality and ultracontractive `L¹→L^∞` bounds (Guionnet–
  Zegarliński Ch. 3; Ledoux 2000 §3–§4 heat-kernel bounds) have no
  module in `Abstract/`; only the LSI/hypercontractivity slice is
  present.
- **No closed-form / generator theory.** `DirichletForm.lean` carries
  only an abstract symmetric energy form. The Fukushima–Oshima–Takeda
  Ch. 1 §1.3–§1.4 closed-form ⇔ semigroup ⇔ self-adjoint generator
  dictionary is *not* built here, and its prerequisite wall — capacity
  theory and the Kato-style form representation underlying the closed
  Dirichlet form (FOT Ch. 2, the capacity prerequisite) — is absent.
  The form-vs-semigroup link is instead axiomatized structurally in
  `Hypercontractivity.lean` via `DirichletMarkovSemigroup`.
- **Γ₂ / Bakry–Émery curvature** (Ledoux 2000 §1 CD(R,n)) lives in the
  `Diffusion/` layer, not here, by design (Layer 1 assumes no Γ).
- The two Gross axioms remain textbook debt: `stroock_varopoulos` is a
  partial step toward discharging them but has no internal consumers.

## Cross-refs

- [`refs/summaries/Fukushima-Oshima-Takeda/01-basic-theory-dirichlet-forms.md`](../../refs/summaries/Fukushima-Oshima-Takeda/01-basic-theory-dirichlet-forms.md) — Ch. 1, `DirichletForm`
- [`refs/summaries/Fukushima-Oshima-Takeda/02-potential-theory.md`](../../refs/summaries/Fukushima-Oshima-Takeda/02-potential-theory.md) — Ch. 2, capacity prerequisite wall
- [`refs/summaries/Guionnet-Zegarlinski/02-spectral-gap-l2-ergodicity.md`](../../refs/summaries/Guionnet-Zegarlinski/02-spectral-gap-l2-ergodicity.md) — Ch. 2, `Poincare`
- [`refs/summaries/Guionnet-Zegarlinski/04-log-sobolev-hypercontractivity.md`](../../refs/summaries/Guionnet-Zegarlinski/04-log-sobolev-hypercontractivity.md) — Ch. 4, `LogSobolev` + `HolleyStroock` (Property 4.6, p. 40)
- [`refs/summaries/Guionnet-Zegarlinski/03-classical-sobolev-ultracontractivity.md`](../../refs/summaries/Guionnet-Zegarlinski/03-classical-sobolev-ultracontractivity.md) — Ch. 3, the unformalized Sobolev/ultracontractivity gap
- [`refs/summaries/Ledoux-2000/01-geometric-aspects-of-diffusion-generators.md`](../../refs/summaries/Ledoux-2000/01-geometric-aspects-of-diffusion-generators.md) — §1, Γ form
- [`refs/summaries/Ledoux-2000/04-sobolev-inequalities-and-heat-kernel-bounds.md`](../../refs/summaries/Ledoux-2000/04-sobolev-inequalities-and-heat-kernel-bounds.md) — §4.2 Cor 4.3, `Hypercontractivity`
- [`refs/summaries/vanHandel/03-subgaussian-logsobolev.md`](../../refs/summaries/vanHandel/03-subgaussian-logsobolev.md) — Ch. 3 §3.3 Herbst, `Concentration`
- [`refs/summaries/vanHandel/08-sharp-transitions-hypercontractivity.md`](../../refs/summaries/vanHandel/08-sharp-transitions-hypercontractivity.md) — Ch. 8 §8.2 Gross, `Hypercontractivity`
- [`refs/summaries/README.md`](../../refs/summaries/README.md) — summary index + the cross-cutting Hypercontractivity 2-axiom vetting note
