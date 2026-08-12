# Sharygin, PDF page 12, problem 7

## Problem

From a point at distance `a > R` from the center of a circle of radius `R`, draw an arbitrary
secant meeting the circle at `A` and `B`.  Prove that `|MA| |MB|` is constant and equals
`a^2 - R^2`.

## Proof represented in Lean

Through the exterior point, first construct the radial secant through the center.  Along that
line, segment additivity and the difference-of-squares identity compute the product of the two
radial secant pieces as `MO^2 - R^2`.

For an arbitrary secant, the intersecting-chords argument applied after extending the lines to
the circle proves that its near-distance times far-distance equals the corresponding product on
the radial secant.  Substitution gives `MA * MB = MO^2 - R^2`, which is independent of the
chosen secant.

## Formalization audit

The configuration contains only the exterior point, the ordered two circle intersections, and
their incidence with the circle.  The radial chord and all product identities are constructed and
proved.  The theorem uses actual scalar lengths and squares, and its conclusion is exactly the
division-free power-of-a-point formula in the source statement.  No constancy or product formula
is assumed.
