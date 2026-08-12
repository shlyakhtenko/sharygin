# Sharygin, PDF page 11, problem 3

## Problem

For a triangle inscribed in a circle, prove that the circle's diameter equals a side divided by
the sine of the opposite angle.  The Lean formula is written without division as

`sin(angle) * diameter = opposite side`.

## Proof currently represented in Lean

For the side `BC`, reflect `B` in the circle center to obtain the antipodal point `D`.  The chord
`BD` is a diameter.  The inscribed-angle theorem shows that `BDC` and `BAC` have the same doubled
angle measure.  Since `BD` is a diameter, the inscribed angle `BCD` is right.  Thus `BCD` is a
right-triangle realization of the sine of the angle opposite `BC`.

By the right-triangle definition, this realization has sine `BC / BD`.  Multiplying by `BD`, and
using the scalar inverse law together with `BC != 0`, gives

`sin(BAC) * BD = BC`.

If `D = C`, the opposite angle is itself right; its sine is defined to be one and the same identity
follows immediately.

## Formalization audit

The circle, its three boundary points, and noncollinearity are exactly the data of a nondegenerate
inscribed triangle.  The antipodal point, right triangle, inscribed-angle identities, and diameter
length are constructed and proved; no metric formula is assumed by the caller.

There is, however, a remaining formalization caveat.  `SineAngle` presently bundles an angle with
one chosen right-triangle realization, and the final theorem constructs a realization for which
the formula holds.  The repository has not yet proved that `realizationValue` is independent of
the chosen realization.  Consequently the present existential statement is weaker than a theorem
about a globally well-defined sine function.  This problem must not be regarded as fully audited
until realization independence is derived from the problem-local similarity machinery and the
final statement is strengthened accordingly.
