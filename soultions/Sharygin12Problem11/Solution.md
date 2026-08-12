# Sharygin, PDF page 12, problem 11

## Problem

Given a triangle with side lengths `a`, `b`, and `c`, prove the median formula
`m_a^2 = (2b^2 + 2c^2 - a^2) / 4`.

The Lean conclusion uses the division-free form
`2 AB^2 + 2 AC^2 = 4 AM^2 + BC^2`.

## Proof represented in Lean

Let `M` be the midpoint of `BC`, and reflect `A` through `M` to a point `A'`.  The quadrilateral
`ABA'C` is a parallelogram because its diagonals bisect each other at `M`.  Apply the
parallelogram diagonal-square identity.  Here one diagonal is `BC`, the other is `AA' = 2 AM`,
and the two pairs of opposite sides have lengths `AB` and `AC`.

Substituting these identities and expanding the square of `2 AM` gives the stated equation,
which rearranges to the familiar median formula.

## Formalization audit

The configuration assumes only a nondegenerate triangle and an actual midpoint of `BC`.
The reflected point and parallelogram are constructed inside the proof.  The theorem proves the
full squared-median relation, with no median formula or auxiliary metric equality in its inputs.
