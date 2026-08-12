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
‎(|a-b|).  Reflecting the relevant endpoints in the internal bisectors gives congruences

\[
  PR\cong |a-b|,
  \qquad QS\cong |a-b|.
\]

These are represented in Lean by primitive segment-congruence witnesses, not by scalar
equalities.  The remainder itself is an actual point on (AB) or (AD), together with the
betweenness and congruence data saying that the removed part equals the shorter side.

Drop perpendiculars from (Q) and (S) to (PR).  The right triangle at (Q) is an actual
right-triangle realization of the original included angle α, so its opposite-leg to
hypotenuse ratio is, by definition, ‎(sin\alpha).  The central half-turn carries its foot to
the foot belonging to (S); consequently the two heights have the same ratio.  Splitting the
quadrilateral along (PR), the locally derived base-times-height theorem gives

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

`MetricConfiguration` adds the ruler-and-compass witnesses used in the metric part:

- an actual remainder point on the longer adjacent side and a congruence identifying the
  removed portion with the shorter side;
- primitive congruence witnesses identifying each inner diagonal with that remainder segment;
- actual perpendicular-altitude configurations;
- an actual right-triangle realization of angle (DAB=\alpha), with its vertices identified
  with the diagonal/altitude construction; and
- the point-reflection witness carrying one altitude foot to the other.

These fields are geometric construction certificates of the kind permitted by
`proof_rules.md`; none is an area equality or the requested formula.  From them Lean derives
the sine-height equations, the two triangle areas, the diagonal product, and the final area
identity.  No coordinates, problem-local axioms, `sorry`, imported problem solution, or
precomputed scalar area certificate occurs in the final theorem.
