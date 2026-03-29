/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Carré du Champ and Iterated Carré du Champ

For a Markov diffusion generator L on a Riemannian manifold (M, g),
the carré du champ (squared field operator) is:

  Γ(f, g) = ½(L(fg) - f·Lg - g·Lf)

For L = Δ - ∇U · ∇ (diffusion with potential U), this equals:
  Γ(f, g) = ⟨∇f, ∇g⟩_g

The iterated carré du champ is:
  Γ₂(f, g) = ½(L Γ(f,g) - Γ(f, Lg) - Γ(g, Lf))

By the Bochner-Weitzenböck formula:
  Γ₂(f, f) = ‖Hess f‖² + Ric(∇f, ∇f) + Hess(U)(∇f, ∇f)

The Bakry-Émery condition Γ₂ ≥ ρ Γ encodes a lower bound on the
"generalized Ricci curvature" Ric + Hess(U) ≥ ρ g.

## Main definitions

- `carreDuChamp` (Γ) — for an abstract diffusion generator
- `iteratedCarreDuChamp` (Γ₂) — the iterated version
- `BakryEmeryCurvature L ρ` — the condition Γ₂(f) ≥ ρ Γ(f) for all f

These are defined abstractly (for any generator with suitable domain)
and then instantiated for specific manifolds in `Instances/`.

## References

- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 1 and 3
- Bakry and Émery, "Diffusions hypercontractives," Séminaire de
  probabilités XIX, Springer LNM 1123 (1985), 177–206
-/
