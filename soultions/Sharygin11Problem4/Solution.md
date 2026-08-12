# Sharygin, PDF page 11, problem 4

## Problem

The vertex of an angle lies outside a circle, and both sides of the angle are secants.  Prove
that the angle is half the difference of the two intercepted arcs lying inside the angle.

In division-free form, the Lean conclusion says that twice the exterior angle equals the far
arc measure minus the near arc measure.

## Proof represented in Lean

The proof first derives, locally from the plane and angle axioms, that the directed angles of a
triangle add to a half-turn.  It then derives the inscribed-angle theorem: twice an inscribed
angle is the corresponding central angle, which by definition is the angular measure of the
selected arc.

Let the two rays from the exterior vertex meet the circle first at the endpoints of the near arc
and then at the endpoints of the far arc.  Form the inscribed angle subtending the far arc and
the inscribed angle subtending the near arc.  The exterior-angle identity in the triangle made by
the exterior vertex and the relevant circle points gives

`far inscribed angle = exterior angle + near inscribed angle`.

Doubling this equality and replacing the two doubled inscribed angles by their central-angle,
or arc-measure, values gives

`2 * exterior angle + near arc = far arc`.

Additive cancellation yields the required difference formula.

## Formalization audit

`ExternalSecantConfiguration` records exactly the original geometric situation: an exterior
vertex, the two ordered intersections on each secant ray, and explicit choices of the near and
far directed arcs.  Its same-ray and orientation fields identify which of the two arcs and which
directed angle the statement means; they do not assert an angle formula.  Triangle angle sum,
the inscribed-angle theorem, and the exterior-angle calculation are all proved in the problem's
own Lean file.  No circle-area or arc theorem is assumed, and the final statement matches the
printed half-difference claim.
