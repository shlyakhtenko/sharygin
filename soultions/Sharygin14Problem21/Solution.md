# Sharygin, PDF page 14, problem 21

## Problem

Points `A` and `B` lie on one side of a right angle with vertex `O`, with `OA = a` and
`OB = b`. Find the radius of the circle through `A` and `B` which is tangent to the other
side of the angle.

The answer is

`r = (a + b) / 2`.

The Lean theorem states this without division as

`2r = OA + OB`.

## Geometric configuration

The configuration contains the vertex `O`, distinct points `A` and `B` on the same ray, a
second ray, a circle through `A` and `B`, and its point of tangency `T` on the second ray.
Tangency is the repository's incidence definition: `T` is the unique point of the tangent
line on the circle.

The assertion that the two rays form a right angle is represented synthetically. A point on
the second ray is reflected through `O`, and `A` is equidistant from the reflected pair. Thus
the second ray is the perpendicular bisector of that pair and the first ray is its baseline.
The noncollinearity field rules out a degenerate angle. This is a right-angle witness, not a
parallelism, radius formula, or part of the requested conclusion.

## Proof

Let `M` be the midpoint of `AB`, and let `C` be the center of the circle.

The formal proof first proves a local transport fact. Suppose a reflected pair has midpoint
`X` and an off-line point `Y` is equidistant from its endpoints. Translate the whole
configuration by composing two half-turns so that `X` moves to another point `X'` of the
baseline. The image line through `X'` and the image of `Y` is parallel to `XY`. Every other
reflected pair on the same baseline with midpoint `X'` has the same equidistant locus. Hence
any off-line point equidistant from such a pair lies on that translated line. Therefore the
two perpendicular-bisector lines are parallel. This argument uses only point reflections,
upper dimension, and Playfair uniqueness already derived locally.

Apply this transport twice:

- The right-angle witness at `O` and the tangent's reflected pair at `T` give `OA ∥ TC`.
  The required equidistance at `T` is derived from the incidence definition of tangency: if
  symmetric tangent-line points had unequal distances from `C`, line-circle continuity would
  produce a second point of the tangent line on the circle.
- Reflect `A` through `O`. The original right-angle witness also makes the second-side point
  equidistant from this new reflected pair. Since `C` is equidistant from `A` and `B` and `M`
  is their midpoint, the same transport gives `OT ∥ MC`.

Thus `OMCT` has both pairs of opposite sides parallel. A direct local half-turn proof shows
that its diagonals bisect one another. The half-turn about their common midpoint maps `OM` to
`CT`, so

`OM = CT = r`.

Finally, `M` is the midpoint of `AB`, and `A` and `B` lie on the same ray from `O`. In either
possible order of `A` and `B`, betweenness additivity gives

`2 OM = OA + OB`.

Substituting `OM = r` proves `2r = a + b`.

## Formalization audit

The final theorem is universal over every configuration described above. It assumes neither
of the two parallelisms, no perpendicular-foot assertion, no parallelogram, and no radius or
length equation. The midpoint `M`, all auxiliary reflected points, all translated lines, and
the diagonal midpoint are constructed in the proof.

The problem folder imports no other problem solution, contains no local axiom or `sorry`, and
uses only the repository's approved plane and length-measurement foundations.
