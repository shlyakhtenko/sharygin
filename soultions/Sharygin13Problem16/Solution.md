# Sharygin, PDF page 13, problem 16

## Problem

Prove that the inradius `r` of a right triangle with legs `a` and `b` and hypotenuse `c` is

`r = (a + b - c) / 2`.

The Lean conclusion is the division-free equality `r + r = a + b - c`.

## Formalization audit

The earlier formalization assumed that the right-angle vertex, the two adjacent contact points, and the incenter formed a rectangle. The proof then used the diagonal-bisection part of that assumed rectangle to obtain the crucial equality between a tangent segment and the radius. That was a substantive intermediate theorem not present in the source problem.

The corrected `Configuration` contains:

- the three vertices and a nondegeneracy condition;
- a reflected-point/equidistance certificate expressing that the angle at `rightVertex` is right;
- the three incircle contact points, each lying between the appropriate side endpoints;
- tangency of the three side lines to the stated circle; and
- an explicit nonoverlapping decomposition of the triangular region into the three triangles obtained by joining the incenter to the vertices.

The last item is region-partition data, not an area equation. Finite additivity is used in the proof to derive the corresponding area equality.

No rectangle, tangent-length formula, Pythagorean equation, triangle-area equation, or requested inradius equation occurs in the configuration.

## Proof

The reflected-point right-angle certificate first yields the measured right angle at the given vertex. The problem-local right-triangle area theorem then gives

`2S = ab`.

The same reflected-point construction also gives Pythagoras:

`a² + b² = c²`.

For each side, the radius to its point of tangency is perpendicular to the tangent line. The locally derived base-times-height theorem therefore gives twice the area of each of the three incenter fan triangles as the corresponding side length times `r`. Finite additivity of the explicit fan partition yields

`2S = r(a + b + c)`.

Combining this with `2S = ab` gives

`r(a + b + c) = ab`.

Pythagoras implies the scalar identity

`(a + b - c)(a + b + c) = 2ab`.

Doubling the preceding area identity also gives

`(2r)(a + b + c) = 2ab`.

The perimeter is nonzero because the triangle is nondegenerate. Cancelling it from these two equations proves

`2r = a + b - c`,

as required.
