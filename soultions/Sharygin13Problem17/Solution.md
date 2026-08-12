# Sharygin, PDF page 13, problem 17

## Problem

If two sides of a triangle have lengths `a` and `b`, the angle between them is `α`, and the
internal bisector of that angle has length `l`, prove

`l = 2ab cos(α/2) / (a+b)`.

The Lean conclusion uses the division-free form

`l(a+b) = 2ab cos(α/2)`.

## Formalization audit

The earlier formalization assumed four facts that are substantial parts of the proof:

- the exterior side `BE` was assumed parallel to the bisector;
- the midpoint construction was assumed to be a right triangle;
- its base angle was assumed to be half of `α`; and
- a disconnected fourth-proportional diagram assumed the similarity product needed at the end.

The corrected final theorem takes only a nondegenerate triangle, a point where its internal
angle bisector meets the opposite side, and the geometric witness defining that ray as the
internal bisector.  It constructs every other point and derives all four facts above.

The angle-bisector witness uses equal-radius samples on the two sides of the angle and their
symmetry about a sample on the bisector ray.  This is the geometric meaning of the original
given “internal angle bisector,” rather than a metric consequence such as the angle-bisector
length formula.

Because the repository defines cosine from an explicit right-triangle realization, the theorem
constructs such a realization and returns it.  It also proves that the realized angle doubles
to the original angle `α`; thus the returned value is genuinely a cosine of `α/2`, not an
unrelated scalar parameter.

## Proof

Write the triangle as `ABC`, with the bisector `AM` meeting `BC` at `M`.

First interchange the names `B` and `C` in the problem-local bisector construction.  The
construction extends `CA` through `A` to a point `E` such that `AE = AB` and proves

`AM ∥ BE`.

Let `F` be the midpoint of `BE`.  Triangle `ABE` is isosceles.  The problem-local isosceles
midpoint theorem therefore proves that `AF` is perpendicular to `BE`, so `ABF` is a right
triangle.  Its cosine at `B` is

`BF / AB`.

The triangle angle-sum theorem and the straight line `C-A-E` show that twice the base angle
`∠ABE` equals `∠BAC = α`.  Consequently the right triangle `ABF` is an explicit realization
of `cos(α/2)`.

The geometric angle-bisector witness separately proves that

`∠MAC = α/2`.

The other base angle of isosceles triangle `ABE` is also `α/2`.  Hence triangles `CAM` and
`CEB` have two equal corresponding angles.  The problem-local AA construction, derived from
the Euclidean axioms and the geometric meaning of multiplication, gives

`AM · CE = BE · AC`.

Finally, betweenness and congruence give

`CE = AC + AE = b + a`

and

`BE = BF + FE = 2BF`.

Substitution into the similarity product yields

`l(a+b) = 2b·BF = 2ab(BF/AB) = 2ab cos(α/2)`,

which is the required division-free formula.
