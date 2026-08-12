# Sharygin, PDF page 14, problem 20

## Problem

1. Prove that the altitudes of a triangle are concurrent.
2. Prove that the distance from any vertex to the point where the altitudes meet is twice the
   distance from the center of the circumscribed circle to the opposite side.

## Construction

Let `O` be the circumcenter of the nondegenerate inscribed triangle `ABC`. Let `Mₐ`, `Mᵇ`,
and `Mᶜ` be the midpoints of `BC`, `CA`, and `AB`. Reflect `O` in these three midpoints,
obtaining `A'`, `B'`, and `C'`.

The Lean proof derives that the three pairs `(A',A)`, `(B',B)`, and `(C',C)` have one common
midpoint `N`. It then reflects `O` in `N` and calls the resulting point `H`.

## Proof that the common midpoint exists

For the first two pairs, the proof separates the cases in which `BC` or `CA` is a diameter.
If, for example, `BC` is a diameter, its midpoint is `O`, so `A' = O`; the local inverse
midpoint-grid theorem then shows that the midpoint of `OA` also bisects `B'B`. The other
diameter case is cyclically identical.

Suppose neither adjacent side is a diameter. The half-turns about `Mₐ` and `Mᵇ` give

- `OC ∥ A'B`, and
- `OC ∥ B'A`.

When the two target lines are distinct, Playfair uniqueness makes them parallel to one another,
and the two reflected-center midpoint connectors similarly give `A'B' ∥ AB`. Thus
`A'B'AB` is a parallelogram, whose diagonals `A'A` and `B'B` bisect one another.

The proof also treats the possible coincident-line case directly. It reflects `B` through the
midpoint of `A'A`, obtains a candidate `X`, and proves that `X` and `B'` lie on the same line
and have equal distances from both `A` and `A'`. Two points on a nondegenerate line with equal
distances from two distinct fixed points must coincide: otherwise both fixed points would be
midpoints of the segment joining them. Hence `X = B'`.

Finally, the apparent exception in which `O`, `A'`, and `B'` are collinear is proved
impossible. Their midpoint relations would place `O`, `Mₐ`, and `Mᵇ` on one line.
Equidistance from each chord's endpoints then propagates along this common perpendicular-
bisector line. Consequently `A` and `B` have equal distances from both `O` and `Mₐ`.
Upper dimension says that they must coincide or lie on opposite sides of `OMₐ`; but the
two side-midpoint half-turns put both on the same side as each other and opposite `C`. Both
alternatives contradict nondegeneracy.

Applying the proved two-pair result to `ABC` and then independently to the cyclic relabelling
`BCA` gives midpoints for `A'A,B'B` and for `B'B,C'C`. Uniqueness of the midpoint of `B'B`
identifies them, producing the common point `N`.

## Altitudes and the distance identity

The half-turn about `N` sends `O` to `H` and sends `A'`, `B'`, and `C'` to `A`, `B`, and `C`.
It therefore preserves the cross-distances

`AH = OA'`, `BH = OB'`, and `CH = OC'`.

For each side, the squared-median identity in the corresponding isosceles radius triangle
proves the metric perpendicularity equation for the opposite altitude at `H`. These are the
three `MetricAltitude` fields in the formal conclusion, so all three altitude lines pass
through the constructed point `H`.

Since `A'` is the reflection of `O` in `Mₐ`, the points `O,Mₐ,A'` are collinear and
`OMₐ = MₐA'`. Therefore

`AH = OA' = OMₐ + MₐA' = 2 OMₐ`.

The same proof yields `BH = 2 OMᵇ` and `CH = 2 OMᶜ`. The formal result also proves the
metric perpendicularity equation showing that each side midpoint is the perpendicular foot
from `O` to that side. Thus these are exactly twice the three distances named in the problem.

## Formalization audit

`CircumscribedTriangle` contains only the source data: three noncollinear points on one circle.
All side midpoints, reflected centers, the common midpoint `N`, and `H` are constructed using
repository existence theorems. The final theorem `problem20` assumes no configuration package,
altitude equation, parallelism, common midpoint, or distance identity.

There are no problem-local axioms or `sorry` declarations, and no other problem solution is
imported. The only measurement convention is the repository's approved squared-distance
predicate `MetricAltitude`, used consistently both for the three vertex altitudes and for the
perpendicular distances from the circumcenter to the side lines.
