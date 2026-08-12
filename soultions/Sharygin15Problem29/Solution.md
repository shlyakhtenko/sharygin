# Sharygin, PDF page 15, problem 29

## Problem

Find the area of the quadrilateral bounded by the internal angle bisectors of a parallelogram
whose adjacent side lengths are (a,b) and whose included angle is α.

## Answer

The area is

\[
  \frac{(a-b)^2\sin\alpha}{2}.
\]

The square makes the expression independent of which adjacent side is called (a).

## Synthetic proof

Let (ABCD) be the parallelogram and let (P,Q,R,S) be the consecutive intersections of
the internal bisectors at (A,B,C,D), respectively.

The adjacent angles of the parallelogram are supplementary.  In the formal proof this is not
assumed: apply the triangle-angle-sum theorem to triangle (ABD), then use the half-turn about
the parallelogram's diagonal center to identify angle (BDA) with the corresponding part of
angle (ABC).

Write the two adjacent half-angles at (A) and (B) as (x) and (y).  Their full angles
satisfy (2x+2y=180^°).  Applying the triangle-angle-sum theorem to (ABP) therefore shows
that the angle between the two bisectors at (P) is (90^°).  Cyclically relabelling the
same argument proves that all four angles at (P,Q,R,S) are right angles.

The half-turn about the center of (ABCD) interchanges opposite angle bisectors.  It therefore
interchanges (P,R) and (Q,S).  Thus the diagonals (PR) and (QS) have a common midpoint;
together with the right-angle result this proves that (PQRS) is a rectangle.

Lay off the shorter of (AB,AD) on the longer one.  The remaining segment has length
‎(|a-b|).  There are two cases, according as (AB\ge AD) or (AD\ge AB); the second is the
same direct argument with the adjacent sides transposed.

Suppose first that (AB\ge AD). Choose (E) on (AB) with (AE=AD), and translate it to a point
(F) on the opposite side. The angle-bisector reflection at (D), together with the resulting
congruent triangles, shows that (S) is the midpoint of (DE). Reflect (E) through the center of
the parallelogram. The midpoint-connector theorem then identifies (SQ) with (EB=|a-b|) and
also proves (SQ\parallel AB).

For the other inner diagonal, extend (AD) to (X) with (AX=AB). The corresponding
angle-bisector reflection at (B) shows that (P) is the midpoint of (BX). Reflect (X) through
the parallelogram center and apply the midpoint-connector theorem again. This gives
(PR=DX=|a-b|) and (PR\parallel AD). Thus, in either side-order case,

\[
  PR\cong |a-b|,
  \qquad QS\cong |a-b|.
\]

These are segment-congruence theorems derived from actual betweenness, reflection, translation,
and midpoint constructions—not scalar assumptions.

Drop perpendiculars from (Q) and (S) to (PR). Since (QS\parallel AB) and (PR\parallel AD),
the angle between the two inner diagonals has the same sine as angle (BAD=\alpha). The formal
proof does not assume this corresponding-angle claim. It takes a common half-turn carrying the
diagonal intersection to (A); the images of points on the two diagonals lie on (AB) and (AD)
by uniqueness of parallels. Half-turn invariance gives equality of the directed angles at the
image points. Replacing an image point by (B) or (D) may reverse a ray, so Lean compares doubled
angle measures; doubling removes precisely this supplementary-ray ambiguity.

Each perpendicular therefore supplies, by the right-triangle definition of sine,

\[
  h_Q=OQ\sin\alpha,\qquad h_S=OS\sin\alpha.
\]

Independence of the chosen right-triangle sine construction is proved locally from similarity,
not assumed. Splitting the quadrilateral along (PR), the locally derived base-times-height
theorem gives

\[
  2[PQRS] = PR\cdot QS\cdot\sin\alpha.
\]

Substituting the two segment congruences yields

\[
  2[PQRS]=(a-b)^2\sin\alpha,
\]

which is the division-free form of the answer.

## Formalization data and audit

`Synthetic.Configuration` contains only the actual parallelogram, its four actual internal
bisectors, their four intersections, nondegeneracy/order data for the bounded quadrilateral,
and the explicit half-turn witnesses (P\leftrightarrow R), (Q\leftrightarrow S).  The
right-angle and rectangle assertions are derived in `Synthetic.lean`.

`MetricConfiguration` adds only the following auxiliary construction data:

- an actual remainder point on the longer adjacent side and a congruence identifying the
  removed portion with the shorter side;
- actual perpendicular-altitude configurations;
- an arbitrary actual right-triangle construction defining (\sin\alpha).

The remainder construction merely chooses the geometric representative of (|a-b|); its two
possible constructors record which side is longer. The altitude witnesses merely choose
perpendicular feet. The sine construction is definitional data, and the local
construction-independence theorem proves that its numerical value equals the values obtained
from both actual diagonal altitudes.

From this data Lean derives, rather than assumes:

- both inner-diagonal congruences with the side-difference segment;
- both inner-diagonal parallels to the outer sides;
- equality of the relevant doubled angle measures;
- both sine-height equations;
- the rectangle assertion and the diagonal area formula.

No coordinates, problem-local axioms, `sorry`, imported problem solution, assumed diagonal
length, assumed angle identification, reflected-foot assumption, or precomputed scalar area
certificate occurs in the theorem. The Lean conclusion is the division-free identity

\[
  2[PQRS]=|a-b|^2\sin\alpha,
\]

which is equivalent to the book's answer.
