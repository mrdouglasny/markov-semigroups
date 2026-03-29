/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bakry-Émery Criterion

The Bakry-Émery criterion: if the generator L of a Markov diffusion
satisfies the curvature condition
  Γ₂(f, f) ≥ ρ · Γ(f, f)

for some ρ > 0 and all f, where Γ is the carré du champ and Γ₂ is
the iterated carré du champ, then the invariant measure satisfies
both the log-Sobolev inequality and the Poincaré inequality with
constant ρ.

For the OU generator Lf = Δf - ⟨x, ∇f⟩ on ℝⁿ with invariant measure
γ, one has Γ₂ ≥ Γ (i.e., ρ = 1), recovering Gross's LSI for Gaussians.

For L = Δ - m²·Id on T^d, the curvature is ρ = m² (from the mass term).
This gives the spectral gap directly.

## Main results

- `BakryEmeryCurvature` — the Γ₂ ≥ ρΓ condition
- `bakryEmery_logSobolev` — curvature ρ implies LSI with constant ρ
- `bakryEmery_poincare` — curvature ρ implies Poincaré with constant ρ
- `ou_bakryEmery` — OU generator has curvature ρ = 1

## References

- Bakry and Émery, "Diffusions hypercontractives," Séminaire de
  probabilités XIX, Springer LNM 1123 (1985), 177–206
- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 1 and 5
-/
