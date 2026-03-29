/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Log-Sobolev Inequality

A probability measure μ satisfies a log-Sobolev inequality (LSI) with
constant ρ > 0 if:
  Ent_μ(f²) ≤ (2/ρ) ∫ |∇f|² dμ

where Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log(∫ g dμ) is the entropy.

The LSI is strictly stronger than the Poincaré inequality (ρ_PI ≥ ρ_LSI)
and is equivalent to hypercontractivity of the associated semigroup
(Gross's theorem).

## Main results

- `LogSobolevInequality` — the LSI as a predicate on measures
- `gross_log_sobolev_gaussian` — standard Gaussian satisfies LSI with ρ = 1
- `logSobolev_implies_poincare` — LSI implies Poincaré with same constant
- `entropy_exponential_decay` — LSI implies Ent_μ(P_t f) ≤ e^{-2ρt} Ent_μ(f)

## References

- Gross, "Logarithmic Sobolev inequalities," Amer. J. Math. 97 (1975),
  1061–1083
- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 5
-/
