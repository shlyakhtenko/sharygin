# Sharygin, PDF pages 11-12, problem 6

## Problem

Let `AB` be a chord of a circle and let a line be tangent to the circle at `A`.  Prove that each
of the two angles between the chord and tangent is half the measure of the arc enclosed by that
angle.

## Proof represented in Lean

Choose the directed arc corresponding to the angle under consideration.  Reflect a second point
of the tangent line through the contact point `A`.  The uniqueness definition of tangency is used
to derive the perpendicular-radius property: the center is equidistant from the tangent point and
its reflection, and the center cannot lie on the tangent.

The resulting isosceles and supplementary-angle calculation converts the tangent-chord angle
into an inscribed angle subtending the chosen arc.  The problem-local inscribed-angle theorem then
identifies twice this angle with the central angle over the same arc.  Since an arc's angular
measure is defined to be that central angle, this is the required result.

## Formalization audit

`TangentChordConfiguration` consists of a circle, a directed arc beginning at the contact point,
and a second point specifying the tangent line.  `TangentAt` means that the contact point is the
line's unique point on the circle; the tangent-radius facts are derived from this definition and
the plane axioms.  Choosing the opposite tangent ray and complementary directed arc gives the
other angle in the printed statement, so the universally quantified directed configuration
covers either of the two angles.  No tangent-chord or arc formula is assumed.
