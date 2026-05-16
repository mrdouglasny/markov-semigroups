# MarkovSemigroups/Matrix

Finite-dimensional matrix-semigroup layer. This directory builds the
semigroup proof of the **diamagnetic inequality** for finite matrices
(§11 of `mass-gap-v3.tex`) from four reusable pieces: heat-kernel
positivity for Z-matrices, the Laplace-transform resolvent
representation, the Lie–Trotter product formula, and the entrywise
phase/triangle assembly. The `IsZMatrix` / `IsEntryNonneg` API in
`HeatKernel.lean` is the entrywise-positivity backbone reused by the
planned finite Beurling–Deny work.

This is a view-only concordance. Citations are taken verbatim from
the module header docstrings; the primary references (Simon 1979
Ch. 22; Berman–Plemmons) are paywalled and **not present in
`refs/`** — see Cross-refs.

| Module | Role | Canonical source | Status (sorry/axiom) |
|--------|------|------------------|----------------------|
| `HeatKernel.lean` | `exp(-tM) ≥ 0` entrywise for Z-matrices (−M Metzler ⇒ positive semigroup); Euler-product proof. Exports `IsZMatrix` / `IsEntryNonneg` API. | Simon, *Functional Integration and Quantum Physics* (1979), Ch. 22; Berman–Plemmons, *Nonnegative Matrices in the Mathematical Sciences* | 0 / 0 (proved) |
| `LaplaceTransform.lean` | Resolvent as semigroup Laplace transform: `M⁻¹ = ∫₀^∞ exp(-tM) dt` for PD `M` (Step 1). Local `IsPosDef` ↔ Mathlib `Matrix.PosDef` bridge. | Simon (1979), Ch. 22 | 0 / 0 (proved) — see Gaps re: upstream `m_matrix_inverse_nonneg` |
| `Trotter.lean` | Lie–Trotter product formula `exp(A+B) = lim (exp(A/n)·exp(B/n))^n` over ℂ (Step 2); telescoping norm bound. | Trotter, *Proc. AMS* 10 (1959) 545–551; Reed–Simon I, §VIII.8 | 0 / 0 (proved) |
| `Diamagnetic.lean` | Main result: `|(M+iV)⁻¹(x,y)| ≤ M⁻¹(x,y)` for real PD Z-matrix `M`, real diagonal `V`; assembles the 5 steps. | Simon (1979), Ch. 22; Reed–Simon IV, §X.4 (Kato's inequality) | 0 / **1 axiom** (`diamagnetic_resolvent`, Diamagnetic.lean:57) |

## Gaps

- **`diamagnetic_resolvent`** (Diamagnetic.lean:57) — the sole *local*
  axiom in this directory. Per `status.md` it is rated against Simon
  Ch. 22; the obstacle recorded is "assembles the 5-step proof"
  (Laplace transform + Trotter + phase bound `|exp(iV)| = 1` + heat
  kernel positivity + entrywise triangle inequality). The four
  component lemmas are individually proved here; the axiom is the
  final assembly only.
- **Anchor-hint correction.** The hint stated
  `LaplaceTransform.lean` carries 1 axiom. It does **not** — it is
  `0 sorry / 0 axiom` and is a proved theorem. The formerly-local
  axiom `m_matrix_inverse_nonneg` (Berman–Plemmons Ch. 6, Laplace
  transform integral) was migrated upstream to the
  `SpectralPositivity` project (`import
  SpectralPositivity.Matrix.MMatrixInverse`); `LaplaceTransform.lean`
  now re-exports it under the historical name as a theorem. It still
  appears in the repo-root `status.md` Matrix/ axiom table because
  the axiom *exists upstream*, but it is not charged to this
  directory. Net: Matrix/ carries **1 local axiom**
  (`diamagnetic_resolvent`); the repo-level count of 2 includes the
  upstream-relocated `m_matrix_inverse_nonneg`.
- No `sorry` anywhere in this directory.

## Cross-refs

- **`plans/beurling-deny.md`** — the planned finite Beurling–Deny
  formalization reuses `HeatKernel.lean`'s `IsZMatrix` /
  `IsEntryNonneg` entrywise-positivity API as its backbone; treat
  `HeatKernel.lean` as a stable downstream dependency.
- **`SpectralPositivity` project** (`spectral-positivity`) —
  `LaplaceTransform.lean` imports
  `SpectralPositivity.Matrix.MMatrixInverse` for the M-matrix inverse
  nonnegativity result (`m_matrix_inverse_nonneg`); see Gaps.
- **Repo root** — `status.md` §"Matrix/" holds the canonical axiom
  audit for this directory; `CLAUDE.md` File Structure section
  describes the layer.
- **References not locally available.** Simon, *Functional
  Integration and Quantum Physics* (1979), Ch. 22 and
  Berman–Plemmons, *Nonnegative Matrices in the Mathematical
  Sciences* are paywalled and absent from `refs/` /
  `refs/summaries/`; they are cited here only as named in the module
  header docstrings and `status.md`, not from local copies.
  Trotter (1959) and Reed–Simon I §VIII.8 / IV §X.4 are likewise
  cited from docstrings.
