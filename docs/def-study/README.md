# Definition study

Notes on Lean/Mathlib design choices for mathematical definitions —
why a particular bundling, typing, or junk-value convention is or
isn't a good fit for a given use case. The recurring theme is that
**the best choice cannot be decided without looking at common use
cases**: types that describe the mathematics perfectly may still be
operationally inconvenient, and Mathlib has consciously made
trade-offs (e.g., junk values) in many places to optimize for
usability.

Started from observations at ICERM (talks by Jireh Loreaux on
operator algebras / CFC, among others).

## Entries

* [`bundled-vs-unbundled.md`](bundled-vs-unbundled.md) — the
  fundamental trade-off: bundled-with-properties definitions vs.
  unbundled / junk-value definitions. CFC for bounded operators as
  the canonical Mathlib example. Our own `MarkovSemigroup` carrier
  refactor (2026-05-13) as a project-internal example.
