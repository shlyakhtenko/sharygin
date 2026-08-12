# Sharygin, PDF page 13, problem 13

## Problem

Prove that the area of a polygon circumscribed about a circle is the product of the circle's radius and the polygon's semiperimeter.

## Formalization audit

`CircumscribedPolygon` is an ordered, closed chain of at least three tangent sides. Consecutive sides share their named endpoints, every point of tangency lies on its side segment, and the circle center lies consistently on the interior side of every oriented edge. These are geometric conditions defining the polygon, not equations used to obtain the requested area formula.

The polygon region is the union of the fan triangles formed by the center and the individual sides. `FanDisjoint` records that successive pieces overlap only in area-zero boundary pieces. Finite additivity then proves—rather than defines—that the measured area of this region is the sum of the triangle areas. Its perimeter is the sum of the side lengths.

## Proof

For one side, join its endpoints to the circle center. The radius to the point of tangency is perpendicular to the tangent side. The local area development derives, from rectangle area and finite additivity, that twice the area of this triangle is the side length times the circle radius.

Apply this identity to every side and add the equalities. Distributivity factors out the common radius, giving

`2 · area = radius · perimeter`.

This is exactly the division-free form of `area = radius · semiperimeter`.
