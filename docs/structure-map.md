# Structure map: repo organization vs. textbook taxonomies

**Mode: 2C (view-only).** This document and the per-directory
`README.md` concordances impose the textbook organization as a
*navigable view*. No module is moved or renamed; `lgt`, `pphi2`,
`gaussian-hilbert` import paths are untouched. The "target
architecture" in §5 is a non-binding reference for incremental
migration if/when subtrees are touched anyway.

Source summaries: `refs/summaries/` (untracked). Per-directory
concordances: `MarkovSemigroups/<Dir>/README.md`.

---

## 1. The fusion problem

The repo spans **three textbook traditions** that no single book
unifies:

| Tradition | Canonical text | Shape |
|---|---|---|
| Γ-calculus / functional inequalities | Bakry–Gentil–Ledoux 2014; Ledoux 2000 | **vertical**: (semigroup, generator, Γ) → inequalities → curvature |
| Dirichlet-form structure theory | Fukushima–Oshima–Takeda 2011 | **form-centric**: form → potential theory/capacity → Beurling–Deny → process |
| Statistical mechanics / mixing | Georgii / Friedli–Velenik; Guionnet–Zegarliński; Levin–Peres–Wilmer | **path**: Gibbs/DLR → Dobrushin uniqueness; semigroup → gap → LSI → spin systems → equivalence |

Any single-book layout is therefore wrong by construction. The
question is which tradition is the **spine** and which become
labelled application layers.

## 2. Canonical taxonomies (the yardsticks)

**BGL / Ledoux 2000** (the analytic spine):
1. Markov triple $(E,\mu,\Gamma)$: semigroup, generator $\mathrm L$,
   carré du champ $\Gamma$, symmetry/invariance.
2. Functional inequalities: Poincaré → log-Sobolev → Sobolev →
   hypercontractivity (Gross).
3. Geometry: $\Gamma_2$, Bakry–Émery $CD(\rho,n)$, comparison.
4. Examples/instances: OU, sphere, torus, Gaussian.

**FOT** (the structure spine): Ch.1 forms (Markovian, closed) →
Ch.2 potential theory / **capacity / quasi-continuity** → Ch.3
**Beurling–Deny + LeJan** (§3.2 pp.120–130) + examples → Ch.4–7
process correspondence & stochastic analysis.

**Guionnet–Zegarliński** (the spin-system path): Ch.1 semigroups →
Ch.2 spectral gap → Ch.3 Sobolev/ultracontractivity → Ch.4
LSI/hypercontractivity (**Holley–Stroock Prop 4.6 p.40**) → Ch.5
LSI for lattice spin systems → … → Ch.8 **Equivalence Thm 8.8
p.102** (mixing ⇔ analyticity ⇔ gap ⇔ LSI).

**Friedli–Velenik / LPW** (the consumed layers): F–V Ch.6
Gibbs/DLR/**Dobrushin uniqueness §6.5.2 p.268**; LPW Ch.4–5
TV/coupling/**Doeblin minorization §5.4**, Ch.14 path coupling.

## 3. Current repo vs. taxonomy

| Repo dir | Closest tradition | Maps to |
|---|---|---|
| `Abstract/` | BGL spine + FOT Ch.1 | Markov-triple + inequalities, but **mixed levels**: `DirichletForm` (FOT Ch.1 / triple) sits beside `Hypercontractivity` (BGL Part II terminal) |
| `Diffusion/` | BGL Part I + III | Γ/Γ₂/Bakry–Émery + OU example + L²/Hille–Yosida bridge |
| `Convergence/` | BGL Ch.2/4 + LPW | consequences: gap→mixing, entropy decay, Doeblin |
| `Coupling/` | LPW Ch.4–5,14 | TV/coupling toolbox |
| `Dobrushin/` | F–V Ch.6 / Georgii | Gibbs specification + uniqueness (consumed by `lgt`) |
| `DobrushinZegarliński/` | GZ (whole) | the GZ-lectures formalization, capstone Thm 8.8 |
| `Instances/` | BGL Ch. examples | concrete spaces (Brascamp–Lieb, torus, GFF, Euclidean WIP) |
| `Matrix/` | Simon Ch.22 (off-tradition) | finite-dim positivity/Trotter; feeds finite Beurling–Deny |
| `General/`,`Tools/` | utility | OU entropy decomposition; disintegration tooling |

**Observation:** the repo is *already* a recognizable BGL-spine +
spin-system-applications layout. The organization is sound; what is
missing is (a) the explicit spine ordering and (b) visibility of the
structure-theory branch (FOT) and its prerequisite gaps.

## 4. Gaps the taxonomy exposes ("chapters with no module")

- **FOT Ch.2 capacity / quasi-continuity** — absent; the long pole
  for general Beurling–Deny (`plans/beurling-deny.md`). No catalog
  coverage anywhere.
- **Kato form-representation + unbounded spectral theorem** —
  absent; gates the Beurling–Deny *criteria* and the
  form→$e^{-tA}$ tie-in. To be **consumed** from quantumlib
  (memory `quantumlib-unbounded-spectral-theorem`), not built.
- **FOT §3.2 LeJan energy-measure refinement** (pp.123–130) —
  needs `CarreDuChamp` upgraded to a measure-valued $\mu_{\langle
  u\rangle}$; out of scope of the current B–D plan.
- **BGL Sobolev / Nash / ultracontractivity** (GZ Ch.3; Ledoux §4)
  — no module; only Poincaré/LSI/hypercontractivity present.
- **FOT Ch.4–7 process correspondence** — deliberately out of
  scope (analytic project, not pathwise).

## 5. Target architecture (non-binding, for incremental 2A later)

If subtrees are migrated when next touched, the BGL spine gives the
natural top level (names illustrative):

```
Foundations/   ← Markov triple: DirichletForm, CarreDuChamp, L2Semigroup, InvariantMeasure  (FOT Ch.1 + BGL Part I)
Inequalities/  ← Poincare, LogSobolev, Hypercontractivity, HolleyStroock, Concentration     (BGL Part II / GZ Ch.2,4)
Geometry/      ← BakryEmery (+ Γ₂)                                                          (BGL Part III / Ledoux §1.2)
Structure/     ← (planned) BeurlingDeny; capacity gap lives here                            (FOT Ch.3 §3.2)
Convergence/   ← SpectralGap, RelativeEntropy, Ergodicity, Doeblin, IntegralBounds          (BGL Ch.2,4 / LPW)
SpinSystems/   ← Dobrushin/*, DobrushinZegarlinski/*                                        (F–V Ch.6 / GZ)
Coupling/      ← unchanged (LPW toolbox)
Instances/     ← unchanged
Matrix/        ← unchanged (off-spine finite-dim)
```

This is **not** scheduled work; it records where each subtree would
land so a future migration is mechanical and amortized into work
already happening (cf. `plans/repo-reorg.md` if/when created).

---

## 6. Module → chapter concordance

Per-directory `README.md` files carry the authoritative
module-level table (module · role · canonical Book/Ch/§/p · status):

- [`MarkovSemigroups/Abstract/README.md`](../MarkovSemigroups/Abstract/README.md)
- [`MarkovSemigroups/Diffusion/README.md`](../MarkovSemigroups/Diffusion/README.md)
- [`MarkovSemigroups/Convergence/README.md`](../MarkovSemigroups/Convergence/README.md)
- [`MarkovSemigroups/Coupling/README.md`](../MarkovSemigroups/Coupling/README.md)
- [`MarkovSemigroups/Dobrushin/README.md`](../MarkovSemigroups/Dobrushin/README.md)
- [`MarkovSemigroups/DobrushinZegarlinski/README.md`](../MarkovSemigroups/DobrushinZegarlinski/README.md)
- [`MarkovSemigroups/Instances/README.md`](../MarkovSemigroups/Instances/README.md)
  · [`Instances/WorkInProgress/README.md`](../MarkovSemigroups/Instances/WorkInProgress/README.md)
- [`MarkovSemigroups/Matrix/README.md`](../MarkovSemigroups/Matrix/README.md)
- [`MarkovSemigroups/General/README.md`](../MarkovSemigroups/General/README.md)
  · [`MarkovSemigroups/Tools/README.md`](../MarkovSemigroups/Tools/README.md)

### 6a. Anchor-hint corrections (agents vs. my initial map)

- `Convergence/SpectralGap` → **GZ Ch. 2** (not Ledoux §1.3, which
  does not exist as a section); module docstring cites Reed–Simon
  IV + BGL Ch. 4.
- `Convergence/Ergodicity` → docstring cites **Da Prato–Zabczyk
  Ch. 11**; GZ Ch. 8 (Thm 8.8) is the lattice analogue only.
- `Instances/Torus` → primary is **Da Prato–Zabczyk Ch. 5**, not
  BGL/Ledoux.
- `General/OUEntropyDecomposition` → **BGL §5.5 Thm 5.5.2** (de
  Bruijn / Fisher-info); Ledoux cross-check is §1 (OU = CD(1,∞)),
  not §4.
- `Diffusion/L2Semigroup` → **GZ Ch. 1 Thm 1.7** (Hille–Yosida,
  pp. 8–14); bridges the `hille-yosida` dependency.
- `DobrushinZegarlinski/EntrywiseCovariance` → primary is
  **Helffer–Sjöstrand / Naddaf–Spencer / BGL §4.5** (per status.md
  audit), not GZ Ch. 5.
- `Instances/BrascampLieb` → BGL §4.9 is heading-only in the local
  teaser PDF; substantive cross-ref is Ledoux §1/§4.
- "BGL Part I/III" anywhere → read as **Ledoux-2000** (the local
  BGL PDF is an 8-pp teaser).

### 6b. `status.md` discrepancies — reconciliation status

1. **`Matrix/` axiom overcount — FIXED in `status.md`.** Verified:
   `m_matrix_inverse_nonneg` is now a *theorem* re-exported from
   `SpectralPositivity` (`LaplaceTransform.lean:82`); only
   `diamagnetic_resolvent` (Diamagnetic.lean:57) is local. status.md
   table updated 2→**1** and the stale `m_matrix_inverse_nonneg`
   audit row replaced with a relocation note.
2. **`DobrushinZegarlinski/` file count — FIXED in `status.md`.**
   Verified 8 modules (`Concentration.lean` was omitted); table
   updated 7→**8**.
3. **`Instances/BrascampLieb` — NO `status.md` defect.** status.md
   was already correct: the project table shows BrascampLieb
   `1 | 0 | 0`, and `resolvent_ibp_axiom` /
   `integrated_bochner_axiom` are already listed under "Former
   axiom | How proved" as promoted to `LogConcaveMeasure` structure
   fields. The original §6b wording overstated this — it was an
   agent-hint-vs-reality artifact, not a status.md error. No edit
   made; wording corrected here.
4. **Stale docstring prose** (in `.lean`; left as-is — editing code
   docstrings is out of scope of this view-only doc task):
   `Doeblin.lean` (lines 11,13,126–139), `L2Semigroup.lean`
   (line 47 design note), `Uniqueness.lean` (claims
   `TVCoupling.exists_maximal_coupling` still `sorry`).
5. **Conflict resolved.** `TVCoupling.exists_maximal_coupling`
   (TVCoupling.lean:352) is a **proved theorem** (Hahn
   decomposition); `Coupling/` is entirely sorry-/axiom-free. The
   `lgt` mass-gap path is not blocked here. (Dobrushin README
   corrected; `Uniqueness.lean` docstring left stale.)

**RESOLVED 2026-05-16 (full audit pass).** The aggregate was
reconciled across all three docs. Findings: `OUEntropyDecomposition`
is **axiom-free** (status.md line 56's "3 atomic axioms live there"
was stale — they are discharged theorems; AXIOM_AUDIT.md confirms);
`General/SchwartzConvolution`'s `contDiff_top_convolution_schwartzKernel`
was a **real but unregistered** axiom — now registered in
`AXIOM_AUDIT.md` as **Needs review / NOT VERIFIED** (no consumers).
`status.md` line 41 + project table corrected (Abstract 4→5, added
`General/`/`Tools/`/`EuclideanFin`/`EuclideanTests` rows); README
inline counts synced; `AXIOM_AUDIT.md` summary 11→12 + EuclideanTests
4 scaffolding axioms acknowledged as excluded-by-policy. Authoritative
count: **12 registered** (9 non-WIP + 3 WIP GaussianFin); 4
`EuclideanTests` scaffolding axioms excluded.

### 6c. Verified custom-axiom inventory (2026-05-16)

| Module | Custom axioms | Note |
|---|---|---|
| `Abstract/Hypercontractivity` | 3 | `gross_lsi_implies_hypercontractive`, `gross_hypercontractive_implies_lsi`, `stroock_varopoulos`; cite Ledoux Cor 4.3 / vanHandel §8.2 for vetting |
| `Abstract/Concentration` | 2 | `herbst_mgf_bound`, `poincare_of_lsi` |
| `DobrushinZegarlinski` | 2 | `zegarlinski_lsi_inequality`, `cov_entrywise_bound_of_zegarlinski` (Likely correct, GR) |
| `General/OUEntropyDecomposition` | **0** | axiom-free (de Bruijn/Fisher facts discharged as theorems; the earlier "3 axioms" claim was stale) |
| `General/SchwartzConvolution` | 1 | `contDiff_top_convolution_schwartzKernel` — registered 2026-05-16, Needs review / NOT VERIFIED, no consumers |
| `Matrix/Diamagnetic` | 1 | `diamagnetic_resolvent` |
| `Instances/WorkInProgress` | 7+ | EuclideanFin 3, EuclideanTests 4 (scaffolding); Euclidean.lean 2 `sorry`; TwoPoint 2 math-false `sorry` |

All of `Abstract` (mains), `Diffusion` (mains), `Convergence`,
`Coupling`, `Dobrushin`, `Tools`, `Instances` (non-WIP) are
sorry-free and free of *custom* axioms.
