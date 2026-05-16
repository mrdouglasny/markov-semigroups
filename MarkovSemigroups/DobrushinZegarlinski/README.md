# MarkovSemigroups/DobrushinZegarlinski

**View-only concordance. No `.lean` file in this directory was moved,
renamed, or edited to produce this file.**

This directory is the namesake formalization of the **Guionnet–Zegarliński
lectures** (*Lectures on Logarithmic Sobolev Inequalities*, Séminaire de
Probabilités / Numdam, 2002) — specifically the LSI ⇔ Dobrushin-type
strong-mixing thread for **continuous spin systems** on
`EuclideanSpace ℝ Λ`. The mathematical capstone of that thread is the
**Guionnet–Zegarliński Equivalence Theorem 8.8 (article p. 102, PDF
p. 105)**:

> For a local specification from a product reference measure and a
> finite-range potential, uniformly in `Λ ⊂⊂ ℤ^d` and boundary `ω`:
> **(i) Dobrushin–Shlosman strong mixing ⇔ (ii) complete analyticity ⇔
> (iii) uniform spectral gap ⇔ (iv) uniform log-Sobolev.**

This layer formalizes the **(i)/(iv) ⇒ global LSI** direction
constructively (the Chapter 5/7 spatial-sweeping construction) together
with the linear-algebraic Neumann-series backend and the
Helffer–Sjöstrand entrywise-covariance corollary that downstream
`pphi2N` consumes for the strict-thermodynamic-limit mass-gap proof.
The continuous-spin variant assembled here is Zegarliński's hypothesis
(uniform single-site LSI + weak gradient coupling `Σ J/c ≤ α < 1`, the
Otto–Reznikoff form); the discrete-TV Dobrushin uniqueness theorem
itself lives one directory over in `MarkovSemigroups/Dobrushin/`
(Friedli–Velenik §6.5.2).

Status snapshot (matches repo `status.md`): **0 `sorry`, 2 textbook
axioms** across these modules. Both axioms are the *functional-inequality
assemblies* — the positivity / linear-algebra / DLR-integral arms are
proved.

## Modules

| Module | Role | Canonical source | Status |
|--------|------|------------------|--------|
| `AbstractInfluence.lean` | Probability-free linear-algebra core: a nonnegative matrix with row/column sums `≤ α < 1` has a convergent Neumann series with `n`-th iterate row sum `≤ αⁿ`. Shared backend of the discrete-TV (`Dobrushin/NeumannSeries`) and continuous-gradient (`InteractionMatrix`) specializations. | Neumann series in the Dobrushin influence matrix `(c_{ij})`, `c(π)=sup_i Σ_j c_{ij}<1`; Guionnet–Zegarliński Ch. 5 strategy (Ciii), §5.2 `c=c̄/(1−λ)`; Friedli–Velenik §6.5.2, p. 268 (Dobrushin comparison / Neumann-type series). | Proved (sorry-free, no axiom) |
| `InteractionMatrix.lean` | Gradient interaction matrix `J_{xy}(V) = sup_ψ |∂_y∂_x V(ψ)|` from the mixed `fderiv` of the potential on `EuclideanSpace ℝ Λ = PiLp 2`; packages `c·J` (`gradInteractionMatrix`, gated on `ContDiff ℝ 2 V`) for `AbstractInfluenceMatrix`. The continuous analogue of the Dobrushin interdependence matrix. | Guionnet–Zegarliński Ch. 5 §5.1 (finite-range potential `Φ`, `‖Φ‖<∞`); Dobrushin interdependence (influence) matrix, Friedli–Velenik §6.5.2–6.5.3, pp. 268–271 (single-site oscillation bound feeding `c_{ij}`). | Proved (sorry-free, no axiom) |
| `LocalLSI.lean` | Thin `fderiv`-based LSI predicate `Ent_μ(f²) ≤ (2/c) ∫‖∇f‖² dμ` decoupled from the Dirichlet-space scaffold; `UniformLocalLSI` class = single-site conditional LSI with the *same* `c`, uniformly in the boundary. The (iv)-side per-site hypothesis of Thm 8.8. | Guionnet–Zegarliński Ch. 4, Thm 4.1 (LSI definition, eq. 4.0.1), p. 34; uniform-in-`Λ,ω` LSI = condition (iv) of Equivalence Thm 8.8, p. 102. | Proved (sorry-free, no axiom) |
| `EntropyChainRule.lean` | `entropy`, `siteSmoothing`, the **proved** DLR-at-Bochner-integral identity (`integral_siteSmoothing`) and the single-site decomposition `entropy_decomposition_single_site` (S1). Spatial-sweeping / Doob-martingale decomposition of relative entropy. (Earlier `entropy_chain_rule_local` axiom was removed after review — false without a coupling term.) | Guionnet–Zegarliński Ch. 5 §5.2 telescoping identity and Ch. 7 (Lu–Yau martingale expansion of relative entropy along an increasing filtration), pp. 50–73, 83–94; BGL §5.7.4; Stroock–Zegarliński, *CMP* 144 (1992) §3. | Proved (sorry-free, no axiom; S1 proved, no global chain-rule axiom) |
| `GlobalLSI.lean` | `ZegarlinskiCondition` (`Σ J/c ≤ α < 1`, Otto–Reznikoff form), the `IsGibbsSpecificationFor` link class, and `global_lsi_of_zegarlinski`: uniform local LSI + weak coupling ⇒ volume-independent global LSI with `C = c·(1−α)`. Positivity arm proved; functional inequality is the axiom. | Guionnet–Zegarliński Ch. 5 §5.2 (auxiliary-chain template, `c=c̄/(1−λ)`) and Equivalence Thm 8.8 (i)/(iv) ⇒ global LSI, p. 102; Zegarliński, *Lett. Math. Phys.* 20 (1990); Otto–Reznikoff, *JFA* 243 (2007) Thm 1; BGL Thm 5.7.5. | **1 axiom** `zegarlinski_lsi_inequality` (rated *Likely correct*, GR / Gemini) |
| `EntrywiseCovariance.lean` | `neumannEntrywise`, `coord`, `covCoord`; entrywise covariance bound `|Cov_μ(σ_x,σ_y)| ≤ (1/c)·neumannEntrywise(J/c) x y` via Helffer–Sjöstrand + Neumann expansion of the inverse Hessian + log-concavity, with the finite-range exponential-decay corollary. The bridge `pphi2N`'s mass-gap proof consumes. | Helffer–Sjöstrand representation of covariance, Naddaf–Spencer *CMP* 183 (1997), Helffer–Sjöstrand *JSP* 74 (1994); BGL §4.5; consistent with Guionnet–Zegarliński Ch. 5 strong-mixing / covariance-decay (`|E_Λ^ω(f,g)| ≤ e^{−M·d}`, Thm 8.8 (i)). | **1 axiom** `cov_entrywise_bound_of_zegarlinski` (rated *Likely correct*, GR / Gemini; needs `h_convex` uniform log-concavity, L² integrability) |
| `Concentration.lean` | Zegarliński-specific Lipschitz concentration: composes the proved positivity arm of `global_lsi_of_zegarlinski` with the Borell–Herbst entropy-method bound to get `μ_eucl({F−E F > t}) ≤ exp(−c(1−α)t²/2L²)`. No new axiom (reuses `Abstract/Concentration` and the `GlobalLSI` axiom). | Herbst argument from LSI: van Handel Ch. 3 §3.3, pp. 55–63 (Ent ⇒ subgaussian Lipschitz tail `P(f−Ef≥t) ≤ e^{−t²/2C‖f‖_Lip²}`); discrete/spin-system entropy method van Handel §3.4. | Proved here (sorry-free, no own axiom; depends on `GlobalLSI` axiom) |
| `EuclideanTransport.lean` | Type-side adapter: `GibbsSpec.toEuclideanMeasure` pushes a Gibbs measure from `SpinConfig Λ ℝ = Λ→ℝ` (product / `L^∞`) onto `EuclideanSpace ℝ Λ = PiLp 2` (`ℓ²` Borel), with probability preservation proved. Bookkeeping bridge so the LSI predicate and the Gibbs framework share a carrier. | Carrier/topology bookkeeping (`L^∞` vs `ℓ²`) for the LSI ⇒ transport hierarchy; context: van Handel Ch. 4 §4.4 (Otto–Villani LSI ⇒ T₂ ⇒ Gaussian concentration), pp. 99–112. No formalized transport theorem here — name reflects the `EuclideanSpace` carrier the transport-side arguments expect. | Proved (sorry-free, no axiom) |

## Gaps

- **`zegarlinski_lsi_inequality` (`GlobalLSI.lean:234`).** Textbook
  axiom: the functional-inequality assembly of `global_lsi_of_zegarlinski`.
  It composes the proved `entropy_decomposition_single_site`, the
  uniform local LSI, and the `AbstractInfluence` Neumann row bound on
  `J/c` (Schur estimate). Positivity arm is proved separately; this
  axiom is the entropy-chain ⇒ global-LSI step (the standard
  Ch. 5 §5.2 / BGL §5.7 measure-theoretic content). Rated
  *Likely correct* (GR, Gemini chat) after fixes to algebra direction
  (`Σ J/c ≤ α`, **not** `c·J ≤ α`), integrability of
  `f², f²·log f², ‖∇f‖²`, and the `IsGibbsSpecificationFor` spec↔V
  link. Debt, not a free lemma — discharge target is the Lu–Yau /
  spatial-sweeping construction (Ch. 5 §5.2, Ch. 7).
- **`cov_entrywise_bound_of_zegarlinski` (`EntrywiseCovariance.lean:146`).**
  Textbook axiom: Helffer–Sjöstrand covariance identity + Neumann
  inverse-Hessian expansion + log-concavity. Rated *Likely correct*
  (GR, Gemini) after five fixes, notably the **separately required**
  `h_convex` (uniform `Hess V_xx ≥ c`; *not* implied by local LSI
  alone — double-well counterexample), a substantive
  `IsGibbsSpecificationFor` (closing a soundness hole), and L²
  (not L¹) integrability of coordinate functions.
- **No formalized Equivalence Theorem 8.8.** Only the `(i)/(iv) ⇒
  global LSI` direction and its corollaries are mechanized. The full
  four-way equivalence (complete analyticity, (iii)⇒(i) via the
  exponential-approximation property of GZ §8.1) is *not* formalized
  here; cited as the orienting capstone, not a proved object.
- **`EuclideanTransport.lean` proves no transport inequality.** It is
  a carrier/measurability adapter; the LSI ⇒ T₂ (Otto–Villani)
  content of van Handel §4.4 is context only, not mechanized.
- **`status.md` lists "7 files"** for this directory but there are 8
  `.lean` modules — `Concentration.lean` is the one omitted from that
  enumeration (it is the van-Handel-§3.3 Herbst composition). Flagged
  as a doc-count discrepancy in `status.md`, not a code defect.

## Cross-refs

Reference summaries live in
[`refs/summaries/`](../../refs/summaries/README.md) (untracked,
generated 2026-05-16). Key chapter pages for this directory:

- **Guionnet–Zegarliński 2002** — the namesake source:
  - [`Guionnet-Zegarlinski/04-log-sobolev-hypercontractivity.md`](../../refs/summaries/Guionnet-Zegarlinski/04-log-sobolev-hypercontractivity.md)
    — Thm 4.1 (LSI definition, p. 34), Property 4.6 (Holley–Stroock,
    p. 40), Thm 4.9 (LSI ⇒ spectral gap, p. 42). Backs `LocalLSI`.
  - [`Guionnet-Zegarlinski/05-lsi-spin-systems-lattice.md`](../../refs/summaries/Guionnet-Zegarlinski/05-lsi-spin-systems-lattice.md)
    — §5.1 finite-range framework, §5.2 strategy `(Ci)–(Civ)`,
    `c=c̄/(1−λ)`. Backs `InteractionMatrix`, `EntropyChainRule`,
    `GlobalLSI`, `AbstractInfluence`.
  - [`Guionnet-Zegarlinski/07-lsi-long-range-martingale.md`](../../refs/summaries/Guionnet-Zegarlinski/07-lsi-long-range-martingale.md)
    — Lu–Yau martingale entropy expansion. Backs `EntropyChainRule`.
  - [`Guionnet-Zegarlinski/08-infinite-volume-ergodicity.md`](../../refs/summaries/Guionnet-Zegarlinski/08-infinite-volume-ergodicity.md)
    — **Equivalence Thm 8.8, p. 102** (the capstone), Thm 8.2
    (exponential-approximation property), Thm 8.5 (uniform ergodicity).
- **van Handel (lecture notes)** — concentration / transport:
  - [`vanHandel/03-subgaussian-logsobolev.md`](../../refs/summaries/vanHandel/03-subgaussian-logsobolev.md)
    — §3.3 entropy method / Herbst argument, §3.4 modified LSI for
    spin systems. Backs `Concentration`.
  - [`vanHandel/04-lipschitz-transportation.md`](../../refs/summaries/vanHandel/04-lipschitz-transportation.md)
    — §4.4 Otto–Villani LSI ⇒ T₂ ⇒ Gaussian concentration. Context
    for `EuclideanTransport`.
- **Friedli–Velenik 2017** — Dobrushin interaction matrix:
  - [`Friedli-Velenik/06-infinite-volume-gibbs.md`](../../refs/summaries/Friedli-Velenik/06-infinite-volume-gibbs.md)
    — **§6.5.2, p. 268** Dobrushin interdependence matrix `c_{ij}`,
    condition `sup_i Σ_j c_{ij}<1`, Neumann-type series; §6.5.3
    p. 271 high-temperature derivation. Backs `InteractionMatrix`
    and `AbstractInfluence`.

### Fidelity caveats

- The Numdam scan of Guionnet–Zegarliński cites "[22]" inline for
  Dobrushin–Shlosman in Thm 8.8, but its printed bibliography numbers
  the Dobrushin–Shlosman papers [31]/[32]/[33] ([22] = Deuschel–Stroock);
  a scan-numbering inconsistency recorded in the GZ summary index,
  not corrected here.
- Page numbers above are *article* pages from the GZ summaries
  (Numdam pagination); PDF offsets differ (e.g. Thm 8.8 = article
  p. 102 / PDF p. 105) and are given where the summaries record them.
- Citations reflect only what the `refs/summaries/` files state;
  Helffer–Sjöstrand / Otto–Reznikoff specifics for the two axioms are
  taken from `status.md`'s axiom-audit rows, not from the textbook
  summaries (which do not cover those papers).
