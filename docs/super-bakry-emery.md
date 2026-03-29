# Super Bakry-Émery: Graded Extension of the Functional Inequality Framework

## Motivation

The `BakryEmerySpace` typeclass (Layer 2 of the current architecture)
bundles a probability measure $\mu$, a carré du champ $\Gamma$, a
curvature bound $\rho > 0$, and a Markov semigroup $P_t$. Supersymmetric
quantum field theory suggests a natural extension: add a
$\mathbb{Z}_2$-grading and a "square root" operator $Q$ with $H = Q^2$.

This gives strictly stronger functional inequalities (spectral gap of $H$
from spectral gap of $Q$), connects to Witten's Morse theory and
localization, and potentially resolves the Holley-Stroock obstacle for
interacting theories via SUSY cancellations.

## 1. Review: The Standard BakryEmerySpace

The current typeclass (in `Diffusion/CarreDuChamp.lean`) has:

- **Probability measure** $\mu$ on $X$
- **Carré du champ** $\Gamma(f,g) : X \to \mathbb{R}$ — abstract
  "inner product of gradients," satisfying Leibniz and $\mathcal{E}(f,g) = \int \Gamma(f,g)\, d\mu$
- **Semigroup** $P_t = e^{tL}$ — the diffusion (heat) semigroup on $L^2(\mu)$
- **Curvature bound** $\rho > 0$ — axiomatized via gradient decay
  $\int \Gamma(P_t f)\, d\mu \leq e^{-2\rho t} \int \Gamma(f)\, d\mu$,
  equivalent to $\Gamma_2 \geq \rho\, \Gamma$

The semigroup $P_t$ is:
- Positive ($f \geq 0 \Rightarrow P_t f \geq 0$)
- Contractive ($\|P_t f\|_2 \leq \|f\|_2$)
- Self-adjoint ($\langle P_t f, g \rangle = \langle f, P_t g \rangle$)
- Mean-preserving ($\int P_t f\, d\mu = \int f\, d\mu$)

All elements of $L^2(\mu)$ are "even" — there is no grading.

## 2. The Graded Extension

### The Z₂-graded Hilbert space

Replace $L^2(\mu)$ with a graded Hilbert space

$$\mathcal{H} = \mathcal{H}_+ \oplus \mathcal{H}_-$$

equipped with a self-adjoint involution $\Gamma$ (the **grading operator**)
satisfying $\Gamma^2 = I$ and $\Gamma^* = \Gamma$. The eigenspaces are:
- $\mathcal{H}_+ = \ker(\Gamma - I)$ — **even** (bosonic) states
- $\mathcal{H}_- = \ker(\Gamma + I)$ — **odd** (fermionic) states

**Physical examples:**
- SUSY quantum mechanics on $M$:
  $\mathcal{H}_+ = L^2(\Omega^{\mathrm{even}}(M))$,
  $\mathcal{H}_- = L^2(\Omega^{\mathrm{odd}}(M))$,
  $\Gamma = (-1)^p$ on $p$-forms
- WZ model: $\mathcal{H}_+ = \mathcal{H}_b \otimes \mathcal{H}_{f,\mathrm{even}}$,
  $\mathcal{H}_- = \mathcal{H}_b \otimes \mathcal{H}_{f,\mathrm{odd}}$,
  $\Gamma = (-1)^{N_f}$

### The supercharge Q

The supercharge $Q : \mathcal{H} \to \mathcal{H}$ is:
- **Self-adjoint** ($Q^* = Q$)
- **Odd** ($Q\Gamma + \Gamma Q = 0$, i.e., $Q$ maps even to odd and vice versa)

In matrix form relative to the grading:

$$Q = \begin{pmatrix} 0 & Q_- \\ Q_+ & 0 \end{pmatrix}$$

where $Q_+ : \mathcal{H}_+ \to \mathcal{H}_-$ and $Q_- = Q_+^*$.

### The Hamiltonian H = Q²

The **SUSY relation** $H = Q^2$ defines the Hamiltonian. Since $Q$ is odd,
$H = Q^2$ is **even** (commutes with $\Gamma$):

$$H = Q^2 = \begin{pmatrix} Q_- Q_+ & 0 \\ 0 & Q_+ Q_- \end{pmatrix}$$

The semigroup $P_t = e^{-tH}$ preserves the grading:
$P_t(\mathcal{H}_\pm) \subseteq \mathcal{H}_\pm$.

### The super carré du champ

$$\Gamma_Q(f,f)(x) = |Qf(x)|^2$$

This replaces the standard $\Gamma(f,f) = |\nabla f|^2$. On a manifold
with $Q = d + d^*$:
- For a function $f$ (0-form): $\Gamma_Q(f,f) = |df|^2 = |\nabla f|^2 = \Gamma(f,f)$ — agrees with standard
- For a 1-form $\alpha$: $\Gamma_Q(\alpha,\alpha) = |d\alpha|^2 + |d^*\alpha|^2$ — includes both exterior derivative and codifferential

So $\Gamma_Q$ is strictly more informative than $\Gamma$ when applied to
higher-degree forms.

### The super Γ₂ and curvature

$$\Gamma_{2,Q}(f,f) = \tfrac{1}{2}\bigl(H\, \Gamma_Q(f,f) - 2\langle Qf, Q(Hf) \rangle\bigr)$$

The super Bakry-Émery condition is $\Gamma_{2,Q} \geq \rho\, \Gamma_Q$.
As in the standard case, we axiomatize this via gradient decay:

$$\int \Gamma_Q(P_t f, P_t f)\, d\mu \leq e^{-2\rho t} \int \Gamma_Q(f, f)\, d\mu$$

but now for **all** $f \in \mathcal{H}$ (both even and odd), not just
functions.

## 3. What the Super Version Gives Beyond Standard

### Spectral gap from Q, not H

**Standard:** Bakry-Émery with curvature $\rho$ gives spectral gap
$\lambda_1(H) \geq \rho$.

**Super:** The spectral gap of $H = Q^2$ is the square of the spectral
gap of $Q$:

$$\lambda_1(H) = (\inf\{\|Qf\| / \|f\| : f \perp \ker Q\})^2$$

If we can show $\|Qf\| \geq \sqrt{\rho}\, \|f\|$ for $f \perp \ker Q$
(a bound on the first-order operator $Q$), we immediately get
$\lambda_1(H) \geq \rho$. First-order bounds are often easier than
second-order bounds.

### The Witten index (topological invariant)

The **supertrace** of the heat semigroup:

$$\mathrm{STr}(e^{-tH}) = \mathrm{Tr}(\Gamma\, e^{-tH}) = \mathrm{Tr}(e^{-tQ_- Q_+}) - \mathrm{Tr}(e^{-tQ_+ Q_-})$$

is **independent of $t$** (because nonzero eigenvalues of $Q_- Q_+$ and
$Q_+ Q_-$ are identical, and cancel in the supertrace). It equals:

$$\mathrm{STr}(e^{-tH}) = \dim\ker Q_+ - \dim\ker Q_- = \mathrm{ind}(Q_+)$$

This is the **Witten index** — a topological invariant computable from
the functional inequality data.

### Witten deformation and localization

Given a function $f : X \to \mathbb{R}$ (a "Morse function"), define the
**Witten-deformed supercharge:**

$$Q_t = Q + t\, [Q, f] = Q + t\, (df \wedge + \iota_{\nabla f})$$

(In the abstract setting: $Q_t = e^{-tf} Q\, e^{tf}$.) Then $H_t = Q_t^2$
gives a one-parameter family of super Bakry-Émery structures with:

- $H_0 = H$ (the original theory)
- As $t \to \infty$: eigenstates of $H_t$ concentrate near critical
  points of $f$
- The Witten index $\mathrm{ind}(Q_{+,t})$ is $t$-independent (homotopy
  invariance of the index)
- The spectral gap of $H_t$ grows like $t \cdot \rho$ near nondegenerate
  critical points (the Hessian of $f$ contributes)

This is **localization as a Bakry-Émery phenomenon**: the functional
inequality structure degenerates in a controlled way, concentrating the
measure onto the critical set.

### Morse inequalities from functional inequalities

The number of eigenvalues of $H_t$ below any threshold $E$ is bounded by
the Morse data of $f$:

$$\dim\{H_t|_{\mathcal{H}_p} \leq E\} \leq \#\{\text{critical points of } f \text{ with Morse index } p\}$$

These are the **strong Morse inequalities**, proved by Witten (1982) using
the $t \to \infty$ analysis of $H_t$. In the Bakry-Émery framework, they
follow from the $t$-dependence of the spectral gap and the constancy of
the Witten index.

## 4. Typeclass Design

### Option A: Extend BakryEmerySpace (measure-theoretic)

Stay in the $L^2(\mu)$ world. Model the grading via a direct sum of two
function spaces.

```lean
class SuperBakryEmerySpace (X : Type*) [MeasurableSpace X]
    extends DirichletSpace X where
  -- Even and odd subspaces of L²(μ)
  -- Modeled as: even = functions, odd = "1-form-like" objects
  -- For SQM: even = L²(Ω^even), odd = L²(Ω^odd)
  -- Abstract: two copies of L²(μ) with Q mapping between them

  /-- The supercharge Q₊ : even → odd -/
  Q_plus : (X → ℝ) → (X → ℝ)
  /-- The adjoint Q₋ = Q₊* : odd → even -/
  Q_minus : (X → ℝ) → (X → ℝ)
  /-- Adjoint relation -/
  Q_adjoint : ∀ f g, ∫ x, Q_plus f x * g x ∂μ = ∫ x, f x * Q_minus g x ∂μ

  /-- H₊ = Q₋ Q₊ on even subspace -/
  H_even (f : X → ℝ) : X → ℝ := Q_minus (Q_plus f)
  /-- H₋ = Q₊ Q₋ on odd subspace -/
  H_odd (f : X → ℝ) : X → ℝ := Q_plus (Q_minus f)

  /-- Energy = ‖Q₊f‖² (for even f) -/
  energy_eq_Q : ∀ f, energy f f = ∫ x, (Q_plus f x) ^ 2 ∂μ

  /-- Curvature bound -/
  ρ : ℝ
  hρ : 0 < ρ
  /-- Gradient decay for the super carré du champ -/
  super_gradient_decay : ∀ (f : X → ℝ) (t : ℝ), 0 ≤ t →
    ∫ x, (Q_plus (semigroup_even t f) x) ^ 2 ∂μ ≤
    Real.exp (-2 * ρ * t) * ∫ x, (Q_plus f x) ^ 2 ∂μ

  /-- Even semigroup P_t^{++} = e^{-tH₊} -/
  semigroup_even : ℝ → (X → ℝ) → (X → ℝ)
  /-- Odd semigroup P_t^{--} = e^{-tH₋} -/
  semigroup_odd : ℝ → (X → ℝ) → (X → ℝ)
```

**Pro:** Stays close to the existing `DirichletSpace` / `BakryEmerySpace`.
**Con:** The two separate function spaces (even/odd) are awkward; the
grading structure is implicit rather than first-class.

### Option B: Hilbert space with involution (operator-theoretic)

Work with an abstract Hilbert space $\mathcal{H}$ equipped with a
grading operator $\Gamma$.

```lean
class SuperDirichletSpace (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] where
  /-- Z₂-grading: self-adjoint involution Γ with Γ² = I -/
  Γ : H →L[ℝ] H
  Γ_involution : Γ ∘L Γ = ContinuousLinearMap.id ℝ H
  Γ_selfAdjoint : ∀ f g, ⟨Γ f, g⟩ = ⟨f, Γ g⟩

  /-- Supercharge Q: odd (anticommutes with Γ), self-adjoint -/
  Q : H → H  -- unbounded, defined on a dense domain
  Q_domain : Submodule ℝ H  -- dense domain of Q
  Q_selfAdjoint : ∀ f g ∈ Q_domain, ⟨Q f, g⟩ = ⟨f, Q g⟩
  Q_anticommutes : ∀ f ∈ Q_domain, Q (Γ f) = -(Γ (Q f))

  /-- Hamiltonian H = Q² -/
  H_op : H → H
  H_eq_Q_sq : ∀ f ∈ Q_domain, H_op f = Q (Q f)

  /-- Semigroup e^{-tH} -/
  semigroup : ℝ → H →L[ℝ] H
  semigroup_generator : ∀ f ∈ Q_domain,
    Tendsto (fun t => (1/t) • (semigroup t f - f)) (nhds 0) (nhds (-H_op f))

  /-- Spectral gap of Q -/
  gap : ℝ
  hgap : 0 < gap
  Q_gap : ∀ f ∈ Q_domain, f ∈ (ker Q)ᗮ → gap * ‖f‖ ≤ ‖Q f‖
```

**Pro:** Clean, first-class grading, natural for index theory.
**Con:** Works at the Hilbert space level, not the measure level. Needs
a bridge to connect to `BakryEmerySpace`.

### Option C: Both, with a bridge (recommended)

Define both and connect them:

1. `SuperDirichletSpace H` — the operator-theoretic version (Option B)
2. `SuperBakryEmerySpace X` — the measure-theoretic version (Option A)
3. A **bridge theorem**: if $\mu$ is the invariant measure of the
   semigroup generated by $H = Q^2$, and $\mathcal{H} = L^2(\mu) \oplus L^2(\mu)$ with $Q$ acting between the two copies, then
   `SuperDirichletSpace` induces `SuperBakryEmerySpace`.

This mirrors the architecture of the WZ project itself (Measure/ +
Operator/ + Bridge/).

## 5. Instances

### SUSY quantum mechanics on ℝⁿ

- $\mathcal{H} = L^2(\Omega^\bullet(\mathbb{R}^n), e^{-2f}\, dx)$
  for a Morse function $f$
- $Q = e^{-f}(d + d^*)e^f = d + df \wedge + d^* + \iota_{\nabla f}$
- $H = Q^2 = \Delta_f$ (Witten Laplacian)
- $\Gamma_Q(g,g) = |dg + df \wedge g|^2 + |d^*g + \iota_{\nabla f} g|^2$
- Curvature $\rho = \min(\mathrm{eigenvalues\ of\ Hess}(f))$ at critical points

### OU process on T^d (free field)

- $\mathcal{H} = L^2(\mu_{\mathrm{GFF}}) \oplus L^2(\mu_{\mathrm{GFF}})$
- $Q_+ = $ the Dirac operator $\not\partial + m$ on $T^d$ acting on
  GFF-distributed fields
- $H = Q^2 = -\Delta + m^2$ (the free Hamiltonian)
- Spectral gap of $Q$: $\sqrt{m^2 + 4\pi^2/L^2}$
- Spectral gap of $H$: $m^2 + 4\pi^2/L^2$ (the square)

### WZ model (interacting)

- $Q = Q_0 + Q_i$ (free supercharge + interaction)
- $H = Q^2$ (the JLW Hamiltonian)
- The spectral gap of $Q$ is bounded below by the SUSY cancellations
- The Witten index $\mathrm{ind}(Q_+) = n - 1$

## 6. File Structure

```
MarkovSemigroups/
  Graded/
    SuperDirichletSpace.lean    -- Option B: Hilbert space + Γ + Q
    SuperBakryEmery.lean        -- Option A: measure-theoretic extension
    Bridge.lean                 -- Option C: connecting the two
    WittenIndex.lean            -- STr(e^{-tH}) = ind(Q₊) = topological
    WittenDeformation.lean      -- Q_t = e^{-tf} Q e^{tf}, localization
    MorseInequalities.lean      -- dim ker H_p ≤ #(critical pts of index p)
  Instances/
    SUSYQuantumMechanics.lean   -- SQM on ℝⁿ with Morse function
    FreeFieldSuper.lean         -- Free OU + grading on T^d
```

## 7. Relation to Other Modules

The graded extension sits between the existing abstract/diffusion layers:

```
Abstract/                    -- Layer 1: no geometry
  DirichletForm.lean         -- E(f,g), Poincaré, LSI, Holley-Stroock

Diffusion/                   -- Layer 2: Γ, Γ₂, curvature
  CarreDuChamp.lean          -- BakryEmerySpace typeclass

Graded/                      -- Layer 2.5: Z₂-grading, Q, H = Q²  [NEW]
  SuperDirichletSpace.lean   -- Hilbert space + grading + supercharge
  SuperBakryEmery.lean       -- Measure-theoretic super Bakry-Émery
  Bridge.lean                -- Connecting operator and measure sides

Instances/                   -- Layer 3: concrete spaces
  Torus.lean                 -- T^d (standard BakryEmerySpace instance)
  Euclidean.lean             -- ℝⁿ (standard)
  SUSYQuantumMechanics.lean  -- SQM on ℝⁿ (SuperBakryEmerySpace instance)  [NEW]
  FreeFieldSuper.lean        -- Free field on T^d (super instance)          [NEW]
```

The `Graded/` module uses `Diffusion/` (it extends `BakryEmerySpace`)
and is used by `Instances/` (which provides concrete super instances).
The `Abstract/` layer is untouched — Poincaré, LSI, and Holley-Stroock
remain at the ungraded level, and the graded versions call into them.

## References

- Witten, "Supersymmetry and Morse theory," J. Diff. Geom. 17 (1982),
  661-692
- Cycon, Froese, Kirsch, Simon, *Schrödinger Operators with Application
  to Quantum Mechanics and Global Geometry*, Springer, 1987, Ch. 11
- Helffer and Sjöstrand, "Puits multiples en mécanique semi-classique
  IV," Comm. PDE 10 (1985), 245-340
- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014
- Jaffe, Lesniewski, Weitsman, "The two-dimensional, N=2 Wess-Zumino
  model on a cylinder," CMP 114 (1988)
