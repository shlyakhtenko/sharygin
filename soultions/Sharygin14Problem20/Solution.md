# Sharygin, PDF page 14, problem 20

## Problem

1. Prove that the three altitudes of a triangle are concurrent.
2. Prove that the distance from any vertex to their common point is twice the distance from
   the circumcenter to the opposite side.

## Natural-language proof represented by the current Lean files

Let `O` be the circumcenter of triangle `ABC`, and let `Mₐ`, `Mᵇ`, and `Mᶜ` be the
midpoints of `BC`, `CA`, and `AB`. Reflect `O` in these three midpoints, obtaining `A'`, `B'`,
and `C'`. The three segments `A'A`, `B'B`, and `C'C` have a common midpoint `N`. Reflect `O`
in `N`, obtaining `H`.

The half-turn about `N` sends `O` to `H` and sends `A'`, `B'`, and `C'` to `A`, `B`, and `C`,
respectively. Hence

`AH = OA'`, `BH = OB'`, and `CH = OC'`.

For each side, the squared-median identity in the corresponding isosceles radius triangle
shows that the metric perpendicularity equation for the opposite altitude holds at `H`. Thus
`AH`, `BH`, and `CH` are all altitudes, so the three altitudes meet at `H`.

Because `A'` is the reflection of `O` in `Mₐ`, the points `O, Mₐ, A'` are collinear and
`OMₐ = MₐA'`. Therefore

`AH = OA' = OMₐ + MₐA' = 2 OMₐ`.

The same argument gives `BH = 2 OMᵇ` and `CH = 2 OMᶜ`. Since the perpendicular from a
circumcenter to a chord bisects that chord, these midpoint distances are the distances from
the circumcenter to the corresponding opposite sides.

## Formalization audit and status

The Lean proof derives all three metric altitude equations and all three distance identities;
it does not assume any altitude or distance formula. `MetricAltitude` is the local
squared-distance characterization of perpendicularity.

The current `Orthocenter.Configuration` contains the original triangle and circumcircle, the
three side midpoints, their reflected points, the common midpoint `N`, and the reflected point
`H`. The midpoint and reflection fields describe the auxiliary construction used above, but
their simultaneous existence has not yet been derived from only a noncollinear triangle and
its circumcircle. Consequently the present final theorem is still conditional on an
unproved construction package and problem 20 is not yet complete. The next formal step is an
existence theorem for this package; only after that theorem is proved should the solution be
marked complete.

The local midpoint-development files now derive the midpoint connector theorem, Playfair
uniqueness for common parallels, the midpoint-triangle closure identity, and the theorem that
the diagonals of a nondegenerate parallelogram bisect one another.  They also now prove the
degenerate fact needed for a right triangle: if the circumcenter lies on a nondegenerate chord,
then it is the chord's midpoint.  This follows from equality of radii and uniqueness of the
midpoint, rather than from an added hypothesis.  The remaining lemma is the complete affine
closure producing one common midpoint for the three reflected pairs, with the ordinary and
diameter cases combined.

The current affine reduction now composes the two half-turns which take `O` first to `A'`
and then to `A`. Applying that composition to `C` gives a candidate for `B'`, and the formal
proof establishes the first required identifying distance from `A`. It also proves the full
common-midpoint conclusion in the ordinary affine case: the two side-reflection
parallelograms give two pairs of opposite parallel lines, whose diagonals have a common
midpoint. The conditions saying that the relevant radius lines are nondegenerate are now
derived from the assertion that the corresponding chords are not diameters. What remains is
to discharge the exceptional collinear cases (including a diameter side), followed cyclically
for `C'`; until those cases are proved, the final theorem remains conditional as stated above.
