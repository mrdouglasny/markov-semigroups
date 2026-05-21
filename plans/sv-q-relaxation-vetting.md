# Vetting request: relaxing the Stroock–Varopoulos exponent hypothesis from `2 ≤ q` to `1 < q`

**For:** deep-think external review.
**Context:** Lean 4 / Mathlib formalization of Gross's theorem (LSI ⇒
hypercontractivity) for a symmetric Markovian semigroup, via the
semigroup-interpolation method. This document is self-contained; no
repository access is needed to evaluate the claim.

---

## 0. The one-line claim to vet

In the formalization, the **Stroock–Varopoulos inequality** is supplied as a
hypothesis predicate. Its exponent antecedent was stated as `2 ≤ q`. I
**relaxed it to `1 < q`**. I claim this is (a) **mathematically true** (the
S–V inequality holds for all `q > 1`, with *equality* for diffusion/gradient
forms), (b) **necessary** for the downstream proof, and (c) **logically sound**
(it strengthens a hypothesis, so it cannot make a false theorem provable), and
(d) **still dischargeable** for the target Gaussian / Ornstein–Uhlenbeck
instance. Please check each of (a)–(d), and flag any error.

---

## 1. Mathematical setting

Let `(P_t)_{t≥0}` be a symmetric Markovian semigroup on `L²(μ)`, `μ` a
probability measure, with self-adjoint generator `L` (so `P_t = e^{tL}`,
`L ≤ 0`), Dirichlet form

  `E(f, g) = -⟨f, L g⟩_{L²(μ)} = ⟨(-L)^{1/2} f, (-L)^{1/2} g⟩`,

and carré du champ `Γ` (`E(f,g) = ∫ Γ(f,g) dμ`). Assume the **log-Sobolev
inequality** with constant `ρ > 0`:

  `Ent_μ(f²) ≤ (2/ρ) · E(f, f)`  for all core `f`,     (LSI)

where `Ent_μ(g) = ∫ g log g dμ − (∫ g dμ) log(∫ g dμ)`.

**Goal (Gross 1975).** Hypercontractivity: `‖P_t f‖_{q(t)} ≤ ‖f‖_p` whenever
`1 < p ≤ q` and `q ≤ q(t) := 1 + (p−1) e^{2ρt}`.

**Method.** Fix `p > 1` and the interpolation path `q(s) := 1 + (p−1) e^{2ρs}`,
so `q'(s) = 2ρ(q(s) − 1)`. Set `u_s := P_s f` (`f ≥ 0`) and

  `F(s) := ∫ u_s^{q(s)} dμ = ‖u_s‖_{q(s)}^{q(s)}`,
  `Λ(s) := log ‖u_s‖_{q(s)} = q(s)^{−1} log F(s)`.

One shows `Λ` is non-increasing on `[0,∞)` (`Λ(t) ≤ Λ(0)` gives the bound).
The chain rule yields, for the right derivative,

  `Λ'(s) = (q'(s)/(q(s)² F(s))) · Ent_μ(u_s^{q(s)}) − E(u_s, u_s^{q(s)−1}) / F(s)`.

(In the formalization the first/analytic half — that `Λ` has this right
derivative — is a separately completed, axiom-clean theorem. The step under
review is only the sign `Λ'(s) ≤ 0`.)

The sign is obtained from **two** ingredients applied at exponent
`q := q(s)`:

* **(LSI)** applied to `v = u_s^{q/2}` (note `v² = u_s^q`):
  `Ent_μ(u_s^q) ≤ (2/ρ) · E(u_s^{q/2}, u_s^{q/2})`.

* **(S–V)** the Stroock–Varopoulos inequality:
  `(4(q−1)/q²) · E(u_s^{q/2}, u_s^{q/2}) ≤ E(u_s, u_s^{q−1})`.

Combining (using `q' = 2ρ(q−1)`, `ρ > 0`, `q > 1`, `F > 0`):

  `(q'/(q²F)) Ent_μ(u_s^q)
     ≤ (2ρ(q−1)/(q²F)) (2/ρ) E(u_s^{q/2},u_s^{q/2})
     = (4(q−1)/(q²F)) E(u_s^{q/2},u_s^{q/2})
     ≤ E(u_s, u_s^{q−1}) / F`,

hence `Λ'(s) ≤ 0`. (S–V is exactly the comparison that converts the LSI
energy `E(u^{q/2},u^{q/2})` into the "true" energy `E(u, u^{q−1})` appearing
in `Λ'`.)

---

## 2. The exact Lean predicate (before / after)

The S–V inequality is **not proved in the abstract development**; it is a
`Prop`-valued hypothesis carried by the LSI⇒HC theorem and discharged
per concrete instance. It is stated in *generator-paired* form: instead of
the symbol `E(u, u^{q−1})` (which requires `u^{q−1}` to be a form-domain
element), it pairs the test function `u^{q−1}` against the generator `Au` of
`u`, supplied together with the strong-`L²` limit witnessing `Au` (this is an
existential-generator workaround and is orthogonal to the point under review).

```lean
-- BEFORE
def StroockVaropoulos (D : DirichletMarkovSemigroup X) : Prop :=
  ∀ {u : X → ℝ} (hu : D.IsCore u) (q : ℝ) (_hq : 2 ≤ q)        -- ← antecedent
    (_hu_half : D.IsCore (fun x => u x ^ (q / 2)))
    (hu_one   : D.IsCore (fun x => u x ^ (q - 1)))
    (Au : Lp ℝ 2 D.μ),
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (D.P t (D.coreToL2 hu) - D.coreToL2 hu))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds Au) →
    (4 * (q - 1) / q ^ 2) *
        D.energy (fun x => u x ^ (q / 2)) (fun x => u x ^ (q / 2))
      ≤ ⟪D.coreToL2 hu_one, - Au⟫_ℝ

-- AFTER  (only the antecedent changed)
    ... (q : ℝ) (_hq : 1 < q) ...                               -- ← relaxed
```

Here `D.energy f g = E(f,g)`, `D.IsCore` is the admissible test-function
algebra, `coreToL2` injects a core function into its `L²(μ)` class, and the
`Tendsto … (nhds Au)` premise says `Au` is the strong-`L²` generator value
`L u`. Via the generator–form compatibility used elsewhere
(`⟨coreToL2 g, Au⟩ = − E(g, u)`), the right-hand side
`⟨coreToL2(u^{q−1}), −Au⟩` equals `E(u^{q−1}, u) = E(u, u^{q−1})`, so the
conclusion is precisely

  `(4(q−1)/q²) · E(u^{q/2}, u^{q/2}) ≤ E(u, u^{q−1})`.   (S–V)

**Concretely the only change is `2 ≤ q` ⟶ `1 < q`.** Everything else
(including the `_hu_half`, `hu_one` core-membership antecedents and the
generator premise) is unchanged.

---

## 3. (a) Mathematical truth — does S–V hold for all `q > 1`?

I claim **yes**.

**General symmetric Markovian case.** The integrated S–V inequality
`(4(q−1)/q²) E(u^{q/2},u^{q/2}) ≤ E(u, u^{q−1})` (for `u ≥ 0`) follows from
the **elementary pointwise Stroock–Varopoulos inequality**

  `(a − b)(a^{q−1} − b^{q−1}) ≥ (4(q−1)/q²) (a^{q/2} − b^{q/2})²`,
  for all `a, b ≥ 0` and `q ≥ 1`,                           (SV-elem)

applied to the Beurling–Deny / jump representation of `E`, plus the diffusion
part handled by the chain rule below. `(SV-elem)` is classically stated for
`q ≥ 1` (it is an equality-type estimate that degenerates to `0 ≥ 0` at
`q = 1`; both sides are smooth in `q` and the constant `4(q−1)/q²` is the sharp
one). I am not aware of any obstruction at `q ∈ (1,2)`.

**Diffusion / gradient case (the actual target).** If the operator is a
diffusion — `Γ(φ(u)) = φ'(u)² Γ(u)` (equivalently `Γ` is a gradient form,
e.g. `Γ(f,g) = ∇f·∇g` for the Ornstein–Uhlenbeck / Gaussian generator) — the
chain rule gives, for `u > 0`,

  `Γ(u, u^{q−1}) = (q−1) u^{q−2} Γ(u)`,
  `Γ(u^{q/2}, u^{q/2}) = ((q/2) u^{q/2−1})² Γ(u) = (q²/4) u^{q−2} Γ(u)`,

so

  `(4(q−1)/q²) Γ(u^{q/2}, u^{q/2}) = (q−1) u^{q−2} Γ(u) = Γ(u, u^{q−1})`,

an **identity for every real `q`** (with `u > 0`). Integrating gives S–V as an
**equality** for diffusions, with no restriction on `q` beyond what makes the
powers meaningful (`u > 0`, which holds in our setting — the orbit is bounded
below by `ε > 0`).

So `2 ≤ q` was a *strictly conservative* antecedent; the inequality is in fact
true (and tight) for all `q > 1` — indeed an equality for the gradient-form
instances we care about.

**Question A.** Is `(SV-elem)` correct for `q ∈ (1, 2)` (sharp constant
`4(q−1)/q²`)? Is the diffusion chain-rule identity above correct, so that the
integrated S–V is an equality for `q > 1` for gradient forms? Any caveat
(e.g. integrability, sign of `q−1`, behavior near `q = 1`)?

---

## 4. (b) Necessity — why `q ≥ 2` is too strong

In the downstream theorem, the predicate is instantiated at
`q = q(s) = 1 + (p−1) e^{2ρs}` for `p > 1` and `s > 0`. Then

  `q(s) = 1 + (p−1) e^{2ρs} > 1 + (p−1) = p > 1`,

so `q(s) > 1` always, but for `p ∈ (1, 2)` and `s` small, `q(s) ∈ (p, 2)`,
i.e. `q(s) < 2`. The antitonicity of `Λ` (needed for the hypercontractivity
bound at every `1 < p`) requires `Λ'(s) ≤ 0` for **all** `s > 0`, hence S–V at
**every** `q(s) > 1`. With the antecedent `2 ≤ q`, the S–V hypothesis simply
does not apply on the sub-range `q(s) ∈ (1, 2)`, and `Λ'(s) ≤ 0` cannot be
concluded there. So either (i) relax to `1 < q`, or (ii) restrict the whole
hypercontractivity theorem to `p ≥ 2` (a strictly weaker result than Gross's,
which holds for all `p > 1`). I chose (i).

**Question B.** Is this necessity analysis correct — in particular, is it true
that the standard Gross interpolation proof genuinely needs S–V on all of
`q > 1` (equivalently `q > p`), not merely `q ≥ 2`, when `1 < p < 2`?

---

## 5. (c) Logical soundness of the change

`StroockVaropoulos D` is a **hypothesis** of the theorems (`P3`:
`Λ'(s) ≤ 0`; and the final LSI⇒HC theorem), not a conclusion. Replacing the
antecedent `2 ≤ q` by `1 < q` makes the predicate quantify over a **larger**
set of `q` (`(1,∞) ⊃ [2,∞)`), i.e. it is a **logically stronger** hypothesis
(harder to satisfy). Consequences:

* Theorems that *consume* `StroockVaropoulos D` can only become *easier* to
  prove; no previously-valid instance is invalidated at the level of the
  abstract theorems (they receive `h_sv` and merely apply it at a specific
  `q`).
* Strengthening a hypothesis can never make a *false* conclusion derivable; the
  only soundness risk would be **vacuity** (if the strengthened hypothesis were
  *unsatisfiable*, the theorem would be vacuously true and useless). Section 3
  rules this out: the relaxed predicate is satisfiable (true) — and provably so
  for the target instance (Section 6).
* No instance currently discharges `StroockVaropoulos D` in this development
  (the per-instance "wiring" step is still pending), so the change breaks no
  existing proof.

**Question C.** Is the soundness reasoning correct (strengthening a hypothesis;
no new vacuity given Section 3)? Is there any subtlety I am missing — e.g. some
*other* lemma that depends on the predicate being *false* outside `[2,∞)`, or a
direction in which a stronger hypothesis could be problematic?

---

## 6. (d) Dischargeability for the Gaussian / OU target

The target concrete instance is the finite-dimensional standard Gaussian with
the Ornstein–Uhlenbeck semigroup, whose Dirichlet form is the gradient (carré
du champ) form `E(f,g) = ∫ ∇f·∇g dγ` — a **diffusion**. By the chain-rule
identity in Section 3, S–V is an **equality** there for all `q > 1`
(`u = P_s f > 0`, smooth core function), so the relaxed predicate is
discharged on `(1,∞)` exactly as easily (in fact identically) as it would have
been on `[2,∞)`. The relaxation imposes no new analytic burden on the instance.

**Question D.** Agreed that for the OU/Gaussian gradient form the relaxed
predicate (`q > 1`) is dischargeable with no more difficulty than `q ≥ 2`
(indeed it is an equality)?

---

## 7. Summary of what to confirm or refute

1. **A:** S–V `(4(q−1)/q²) E(u^{q/2},u^{q/2}) ≤ E(u,u^{q−1})` is valid for all
   `q > 1` (general symmetric Markov), and an equality for `q > 1` (diffusions /
   gradient forms). Sharp constant `4(q−1)/q²`. Any caveats?
2. **B:** The downstream proof genuinely requires S–V on all `q > 1` (not just
   `q ≥ 2`) to cover `1 < p < 2`.
3. **C:** The relaxation `2 ≤ q ⟶ 1 < q` is a hypothesis *strengthening* and is
   logically sound (no new vacuity; cannot make a false theorem provable).
4. **D:** The relaxed hypothesis remains dischargeable for the OU/Gaussian
   instance.

If any of A–D is wrong (e.g. S–V fails or has a different sharp constant on
`(1,2)`, or the constant `4(q−1)/q²` is not what the proof needs there), please
state the corrected statement and the correct exponent range.

**References for cross-check:** Bakry–Gentil–Ledoux, *Analysis and Geometry of
Markov Diffusion Operators* (Springer, 2014), §1.11 (S–V inequalities) and the
LSI ⇒ hypercontractivity argument; Gross, *Logarithmic Sobolev inequalities*,
Amer. J. Math. 97 (1975); Stroock, *Logarithmic Sobolev inequalities for
gases*; Varopoulos.

---

## 8. Verdict (deep-think, 2026-05-21) — CONFIRMED, no caveats

External review (deep-think) confirmed **all four claims A–D** with **no
caveats and no required corrections**:

* **A (truth):** The elementary pointwise S–V inequality holds for all real
  `a,b ≥ 0` and `q ≥ 1` — *no phase transition / singularity / failure on
  `(1,2)`*; the constant `4(q−1)/q²` is **sharp across the whole regime
  `q > 1`**, degenerating to `0 ≥ 0` at `q = 1`. The diffusion chain-rule
  derivation is "flawless": S–V is an **exact identity** for gradient forms for
  all `q ∈ ℝ` (given `u > 0`, guaranteed here by the strict-positivity
  `u = P_t f ≥ ε` bound).
* **B (necessity):** Confirmed — for `p ∈ (1,2)` the path `q(s)` sweeps `(1,2)`
  (starting at `q(0)=p`), so gating S–V behind `q ≥ 2` forces the theorem to
  restrict to `p ≥ 2`, weakening Gross's theorem; `1 < q` is strictly
  necessary to recover the full `1 < p` range.
* **C (soundness):** Confirmed — relaxing the antecedent expands the universal
  quantifier's domain, making the predicate **logically stronger**; consuming
  theorems assume more (always sound), and the only risk (vacuity) is ruled out
  by A. Structurally safe.
* **D (dischargeability):** Confirmed — the OU/Gaussian form is a true diffusion,
  so the discharge is an *equality* rewrite (chain rule), with **zero additional
  burden**; the simplifier does not distinguish `q ≥ 2` from `q > 1`.

**Resolution:** the relaxation `2 ≤ q ⟶ 1 < q` stands. Provenance for the audit:
`DT` (deep-think), rating **Standard** (textbook S–V, sharp constant `q > 1`).
