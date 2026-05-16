# Bibliography & Reading Map

How the mathematics formalized in `markov-semigroups` maps onto the
literature, and where to read each piece. The repo deliberately fuses
**three traditions** that do not appear together in any single textbook:

1. **Analytic Γ-calculus / functional inequalities** — Bakry–Gentil–Ledoux.
2. **Dirichlet-form structure theory** — Fukushima–Oshima–Takeda.
3. **Statistical mechanics / Dobrushin uniqueness for spin systems** —
   Guionnet–Zegarliński, Georgii.

No book spans all three; this document + `README.md` + `plans/history.md`
are effectively the synthesis. Access status verified May 2026.
"Free" = legally author/publisher/NUMDAM-hosted open PDF.

---

## Primary references

### 1. Bakry, Gentil & Ledoux — *Analysis and Geometry of Markov Diffusion Operators* (Springer, Grundlehren 348, 2014)

The spine. Markov semigroups & generators, carré du champ Γ/Γ₂,
Bakry–Émery curvature CD(ρ,∞), Poincaré, log-Sobolev,
hypercontractivity (Gross), convergence to equilibrium — in one unified
framework that explains how the inequalities imply one another.

- **Covers:** `Diffusion/` (Ch. 1, 3), `Abstract/{Poincare,LogSobolev,
  Hypercontractivity}` (Ch. 4, 5), `Convergence/` (Ch. 2.2, 4.2),
  `Instances/BrascampLieb` (§4.9).
- **Access:** book paywalled (Springer). **Free substitutes:**
  - Book front matter + introduction (co-author Gentil's site):
    <https://math.univ-lyon1.fr/~gentil/BGL-introduction.pdf>
  - Ledoux, *The geometry of Markov diffusion generators*, Ann. Fac.
    Sci. Toulouse 9 (2000) 305–366 — the precursor survey of the whole
    Γ-calculus program, **open access (NUMDAM):**
    <https://www.numdam.org/item/AFST_2000_6_9_2_305_0.pdf>
    (author copy: <https://www.math.univ-toulouse.fr/~ledoux/Zurich.pdf>)

### 2. Fukushima, Oshima & Takeda — *Dirichlet Forms and Symmetric Markov Processes* (de Gruyter, 2nd ed. 2011)

The systematic source for Dirichlet-form **structure theory**: regular
forms, capacity, quasi-continuity, the form ↔ Hunt-process
correspondence, and the **Beurling–Deny + LeJan decomposition**
(§3.2 — the theorem targeted in `Abstract/BeurlingDeny.lean`).

- **Covers:** `Abstract/DirichletForm.lean`, planned
  `Abstract/BeurlingDeny.lean`.
- **Access:** paywalled (de Gruyter); no open full text. **Free
  companions:** Ledoux survey above (Γ-side); for the
  Beurling–Deny formula specifically there is no open textbook — §3.2
  of FOT is canonical. Ma & Röckner, *Introduction to the Theory of
  (Non-Symmetric) Dirichlet Forms* (Springer, 1992) is the
  non-symmetric companion (also paywalled).

### 3. Guionnet & Zegarliński — *Lectures on Logarithmic Sobolev Inequalities*, Séminaire de Probabilités XXXVI, LNM 1801 (Springer, 2002), pp. 1–134

Closest single source to the project's **origin thread**: Holley–Stroock
→ interacting-LSI → Dobrushin–Shlosman mixing. Namesake of the
`DobrushinZegarlinski/` directory; relates LSI to Dobrushin-type
conditions for spin systems.

- **Covers:** `Abstract/HolleyStroock`, `DobrushinZegarlinski/*`,
  parts of `Dobrushin/*`.
- **Access:** **free, open access (NUMDAM):**
  <https://www.numdam.org/item/SPS_2002__36__1_0/>

### 4. Georgii — *Gibbs Measures and Phase Transitions* (de Gruyter, 2nd ed. 2011)

Gibbs specifications and Dobrushin uniqueness, statistical-mechanics
formulation.

- **Covers:** `Dobrushin/{Specification,Uniqueness}`,
  `DobrushinZegarlinski/InteractionMatrix`.
- **Access:** paywalled. **Free substitute (recommended):** Friedli &
  Velenik, *Statistical Mechanics of Lattice Systems: A Concrete
  Mathematical Introduction* (Cambridge, 2017) — full book free from
  the authors, Dobrushin's uniqueness theorem proved in detail:
  <https://www.unige.ch/math/folks/velenik/smbook/Statistical_Mechanics_of_Lattice_Systems.pdf>
  (landing: <https://www.unige.ch/math/folks/velenik/smbook/>)

### 5. Levin, Peres & Wilmer — *Markov Chains and Mixing Times* (AMS, 2nd ed. 2017)

Discrete/probabilistic coupling, total-variation distance, Doeblin
minorization, mixing times.

- **Covers:** `Coupling/*`, `Convergence/Doeblin`,
  `Convergence/IntegralBounds`.
- **Access:** **free, author-hosted (2nd ed.):**
  <https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf>
  (landing + errata: <https://pages.uoregon.edu/dlevin/MARKOV/>)

---

## Supporting / topical

| Topic | Reference | Access |
|---|---|---|
| Γ-calculus crash course (before BGL) | Ledoux, *Geometry of Markov diffusion generators* (2000) | Free, NUMDAM (above) |
| LSI gentle intro | Royer, *An Initiation to Logarithmic Sobolev Inequalities* (AMS/SMF, 2007) | Paywalled; use Guionnet–Zegarliński + Ledoux survey |
| Functional ineq. ↔ spectral/semigroup dictionary | Feng-Yu Wang, *Functional Inequalities, Markov Semigroups and Spectral Theory* (2005) | Paywalled |
| Concentration / high-dim probability context | van Handel, *Probability in High Dimension* (Princeton lecture notes) | Free: <https://web.math.princeton.edu/~rvan/APC550.pdf> |
| `Matrix/{HeatKernel,Diamagnetic}` (positivity, Trotter) | Simon, *Functional Integration and Quantum Physics* (1979), Ch. 22; Berman & Plemmons, *Nonnegative Matrices* | Paywalled |
| Hypercontractivity (original) | Gross, *Logarithmic Sobolev inequalities*, Amer. J. Math. 97 (1975) | Paywalled (JSTOR) |
| Dobrushin uniqueness (original) | Dobrushin, *Teor. Veroyatnost. i Primenen.* 13 (1968) | Paywalled |

---

## Layer → source map

| Project layer | Best source | Free? |
|---|---|---|
| `Diffusion/` (Γ, Bakry–Émery), `Abstract/{Poincare,LogSobolev}` | BGL Ch. 1–5 | intro + Ledoux survey free |
| `Abstract/Hypercontractivity` | BGL §5.2; Gross 1975 | no |
| `Abstract/HolleyStroock` | Guionnet–Zegarliński §2 | yes (NUMDAM) |
| `Abstract/DirichletForm`, `BeurlingDeny` | FOT Ch. 1, §3.2 | no |
| `Convergence/{SpectralGap,RelativeEntropy,Ergodicity}` | BGL Ch. 2, 4 | intro free |
| `Convergence/Doeblin`, `Coupling/*` | Levin–Peres–Wilmer Ch. 4–5, 12 | yes (author) |
| `Dobrushin/*`, `DobrushinZegarlinski/*` | Guionnet–Zegarliński; Georgii Ch. 8 | G–Z free; Georgii→Friedli–Velenik free |
| `Instances/BrascampLieb` | BGL §4.9 | intro free |
| `Matrix/*` | Simon Ch. 22; Berman–Plemmons | no |

---

## Recommended reading path

1. **Ledoux (2000) survey** — free, ~60 pp, the entire Γ-calculus
   program in one sitting. Start here.
2. **Guionnet–Zegarliński (2002)** — free, the Holley–Stroock →
   Dobrushin spin-system thread that motivated the repo.
3. **BGL (2014)** — the systematic treatment; read the free
   introduction first, then the relevant chapters.
4. **Friedli–Velenik (2017)** — free, for the Gibbs/Dobrushin side
   (substitutes Georgii).
5. **Levin–Peres–Wilmer (2017)** — free, for the coupling/mixing layer.
6. **FOT §3.2** — for the Beurling–Deny structure theorem (no free
   equivalent; library access required).
