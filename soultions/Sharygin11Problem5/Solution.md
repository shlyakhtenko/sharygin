# Sharygin, PDF page 11, problem 5

## Problem

The vertex of an angle lies inside a circle.  Prove that the angle is half the sum of the arc
between its sides and the arc between the extensions of those sides.

The Lean conclusion is division-free: twice the angle equals the sum of the two selected arc
measures.

## Proof represented in Lean

Label the endpoints of the two intersecting chords so that `A` and `B` lie on the two sides of
the chosen angle, while `C` and `D` lie on their opposite extensions.  The proof derives the
triangle angle-sum and inscribed-angle theorem locally from the plane and angle axioms.

The vertical angle at the chord intersection, followed by the exterior-angle identity in an
auxiliary triangle, writes the required angle as a sum of two inscribed angles.  One of these
inscribed angles subtends the arc `AB`, and the other subtends the extension arc `CD`.  Doubling
the equality and applying the inscribed-angle theorem to both terms gives

`2 * angle = measure(arc AB) + measure(arc CD)`.

## Formalization audit

`InteriorChordConfiguration` records an interior point, the two chords passing through it, and
explicit directed choices of the enclosed and extension arcs.  These data disambiguate the
diagram but contain no angle or arc-measure formula.  The proof establishes the needed vertical,
exterior, and inscribed-angle facts internally.  The conclusion is exactly the printed half-sum
statement, with multiplication by two used in place of division.
