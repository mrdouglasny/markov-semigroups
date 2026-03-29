/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Equivalence: Log-Sobolev ↔ Hypercontractivity

Gross's theorem (1975): A Markov semigroup P_t is hypercontractive
(i.e., P_t : L^p → L^q is bounded for q = 1 + (p-1)e^{2ρt}) if and
only if its invariant measure satisfies the log-Sobolev inequality
with constant ρ.

This closes the circle:
- gaussian-field proves hypercontractivity directly (Nelson's estimate)
- This module derives it from the log-Sobolev inequality
- The two approaches are equivalent by Gross's theorem

## Main results

- `gross_equivalence` — LSI with constant ρ ↔ hypercontractivity with
  rate ρ for the associated semigroup
- `hypercontractive_of_logSobolev` — LSI → hypercontractivity
- `logSobolev_of_hypercontractive` — hypercontractivity → LSI

## References

- Gross, "Logarithmic Sobolev inequalities," Amer. J. Math. 97 (1975),
  1061–1083
- Gross, "Hypercontractivity and logarithmic Sobolev inequalities for
  the Clifford-Dirichlet form," Duke Math. J. 42 (1975), 383–396
-/
