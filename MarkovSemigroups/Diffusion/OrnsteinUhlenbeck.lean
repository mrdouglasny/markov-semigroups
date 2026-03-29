/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Abstract Ornstein-Uhlenbeck Semigroup

The Ornstein-Uhlenbeck semigroup on a Hilbert space H with covariance
operator C (positive, trace-class) is the Markov semigroup with
generator:

  L f(x) = Tr(C D²f(x)) - ⟨x, C⁻¹ ∇f(x)⟩

The OU semigroup is given by Mehler's formula:
  P_t f(x) = ∫ f(e^{-t} x + √(1 - e^{-2t}) y) dγ_C(y)

where γ_C is the centered Gaussian measure with covariance C.

Properties:
- γ_C is the unique invariant measure
- P_t is a contraction semigroup on L²(γ_C)
- P_t satisfies Bakry-Émery with ρ = λ_min(C⁻¹) (smallest eigenvalue
  of the precision matrix)
- P_t is hypercontractive (Nelson/Gross)

This file defines the OU semigroup abstractly. Concrete instances
(R^n, T^d) are in `Instances/`.

## Main definitions

- `OUSemigroup C` — the OU semigroup with covariance C
- `OUSemigroup.invariantMeasure` — the Gaussian invariant measure γ_C

## Main theorems

- `OUSemigroup.mehler` — Mehler's formula
- `OUSemigroup.contraction` — contraction on L²(γ_C)
- `OUSemigroup.bakryEmery` — Bakry-Émery curvature = λ_min(C⁻¹)

## References

- Bakry, Gentil, and Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014, Ch. 2
- Da Prato and Zabczyk, *Stochastic Equations in Infinite Dimensions*,
  Cambridge, 2014, Ch. 5 and 11
-/
