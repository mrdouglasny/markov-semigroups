# MarkovSemigroups/Convergence

View-only concordance for the **convergence-to-equilibrium** layer of
`markov-semigroups`. These modules turn a single quantitative
input — a spectral gap, a log-Sobolev constant, or a Doeblin
minorization — into exponential mixing, entropy decay, ergodicity,
and the QFT-side clustering property (OS4). Layer 1 (the abstract
Dirichlet form + invariant measure) is the only structure required;
no carré-du-champ or curvature assumptions enter here.

This file is documentation only. It does **not** move, rename, or
modify any `.lean` source. Statuses are taken from the repo-root
`status.md` (the canonical sorry/axiom audit, table line 53:
*Convergence/ — 5 decls, 0 sorry, 0 axiom*) and verified by
`grep` of the sources.

| Module | Role | Canonical source | Status |
|--------|------|------------------|--------|
| `SpectralGap.lean` | Spectral gap λ₁ of the generator ⇒ exponential decay of correlations `\|⟨f,P_t g⟩−μ(f)μ(g)\| ≤ e^{−λ₁t}‖f‖₂‖g‖₂`; variance decay `Var(P_t f) ≤ e^{−2λ₁t}Var(f)`; Poincaré constant = spectral gap. Discrete-time QFT mass-gap / clustering analogue. | Guionnet–Zegarliński 2002, **Ch. 2 (Spectral Gap Inequality and L² Ergodicity), pp. 15–22** — the equivalence `m·μ((f−μf)²) ≤ μ(Γ₁) ⇔ ‖Pₜf−μf‖₂ ≤ e^{−mt}‖f−μf‖₂`. Module docstring additionally cites Reed–Simon IV (1978) and BGL 2014 Ch. 4. | proved (0 sorry, 0 axiom) |
| `RelativeEntropy.lean` | Exponential decay of relative entropy (KL divergence) `H(P_t^*μ \| μ_∞) ≤ e^{−2ρt}H(μ \| μ_∞)` under LSI(ρ); Pinsker ⇒ TV decay `‖P_t^*μ−μ_∞‖_TV ≤ √(2H(μ\|μ_∞))`; explicit rate from the LSI constant. | Bakry–Gentil–Ledoux 2014, **Ch. 5** (log-Sobolev / entropy decay; module docstring). Local BGL PDF is a truncated teaser — analytic spine covered by Ledoux 2000 (entropy/LSI program). | proved (0 sorry, 0 axiom) |
| `Ergodicity.lean` | Spectral gap ⇒ ergodicity: unique invariant measure and time-average convergence `(1/T)∫₀ᵀ f(X_t)dt → μ(f)`. Markov-semigroup form of OS4 ergodicity. | Da Prato–Zabczyk, *Stochastic Equations in Infinite Dimensions*, Cambridge 2014, **Ch. 11** (module docstring). Lattice infinite-volume analogue: Guionnet–Zegarliński 2002 **Ch. 8 (Equivalence Thm 8.8, p. 102)**. | proved (0 sorry, 0 axiom) |
| `IntegralBounds.lean` | TV-integral toolbox: `∫f dμ ≥ c` for prob. measures; layer-cake integrability of `t ↦ ν.real{f≥t}`; `tv_integral_bound`: `\|∫f dμ−∫f dπ\| ≤ Cδ` (layer-cake). Feeds `Doeblin.lean`. | Levin–Peres–Wilmer 2017, **Ch. 4 §4.1** (variational/TV characterization) and **Ch. 5 §5.2** (coupling/integral bounds); layer-cake = Mathlib `Integrable.integral_eq_integral_meas_lt`. | proved (0 sorry, 0 axiom) |
| `Doeblin.lean` | Doeblin minorization ⇒ exponential mixing: one-step / kernel contraction `\|·−π(A)\| ≤ 1−ε`, TV contraction `≤ (1−ε)δ`, n-step mixing `\|Tⁿ(δ_x)(A)−π(A)\| ≤ (1−ε)ⁿ`, correlation decay `\|cov\| ≤ 4B²(1−ε)^d`. | Levin–Peres–Wilmer 2017, **Ch. 5 §5.4** (grand couplings; minorization decay `d(t) ≤ (1−α)^{⌊t/k⌋}`) with **Ch. 4 §4.3** Convergence Theorem `max_x‖Pᵗ(x,·)−π‖_TV ≤ Cρᵗ`. Doeblin (1937). | proved (0 sorry, 0 axiom) |

## Gaps

- **None as live `sorry`/`axiom` declarations.** `grep -n
  "sorry\|axiom "` finds zero true declarations across all five
  modules; `status.md` line 53 records *Convergence/ — 0 sorry,
  0 axiom*, and the Doeblin block (status.md §"Doeblin's condition")
  marks `doeblin_one_step_contraction`, `doeblin_tv_contraction`,
  `doeblin_n_step_mixing`, `doeblin_correlation_decay` all **proved**.
- **Stale in-file prose (not a real gap).** `Doeblin.lean`:11,13
  still annotate `doeblin_tv_contraction` / `doeblin_correlation_decay`
  as "(**axiom**)" and lines 126–139 narrate "the sorry is the layer
  cake integration step". These are leftover docstring text from an
  earlier development state; the actual theorems are fully proved
  (status.md is authoritative). No source edit is made here — flagged
  only as a documentation discrepancy for a future cleanup pass.
- **Citation-precision caveats** (from `refs/summaries/README.md`):
  Levin–Peres–Wilmer proposition/theorem *numbers* are
  knowledge-based (only the TOC was scanned); chapter/section/page
  structure is from the PDF TOC and is reliable. The BGL-2014 local
  PDF is a truncated publisher teaser, so the RelativeEntropy "Ch. 5"
  anchor rests on the module docstring + the Ledoux-2000 entropy
  program, not on read BGL chapter text.

## Cross-refs

- `refs/summaries/Guionnet-Zegarlinski/02-spectral-gap-l2-ergodicity.md`
  — backs `SpectralGap.lean` (and the Poincaré ⇔ L²-ergodicity rate).
- `refs/summaries/Guionnet-Zegarlinski/08-infinite-volume-ergodicity.md`
  — backs `Ergodicity.lean` (infinite-volume / Thm 8.8 equivalence).
- `refs/summaries/Levin-Peres-Wilmer/04-introduction-mixing.md`
  — TV distance + Convergence Theorem; backs `IntegralBounds.lean`,
  `Doeblin.lean`.
- `refs/summaries/Levin-Peres-Wilmer/05-coupling.md`
  — §5.4 grand couplings / Doeblin minorization decay; backs
  `Doeblin.lean`.
- `refs/summaries/Ledoux-2000/00-index.md`
  — analytic entropy/LSI spine standing in for the truncated
  BGL-2014; context for `RelativeEntropy.lean`.
- `refs/summaries/BGL-2014/01-introduction.md`
  — Part II (Poincaré / spectral gap, log-Sobolev) overview;
  context for `SpectralGap.lean`, `RelativeEntropy.lean`.
- `refs/summaries/README.md`
  — fidelity caveats and the cross-cutting citation index.
