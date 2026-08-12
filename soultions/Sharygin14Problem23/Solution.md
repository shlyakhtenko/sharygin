# Sharygin, PDF pages 14–15, problem 23

## Problem

The legs of a right triangle have lengths \(a\) and \(b\). Find the distance
from the vertex of the right angle to the nearest point of the inscribed
circle.

## Answer

Let \(c=\sqrt{a^2+b^2}\) be the hypotenuse and let \(r\) be the inradius.
The requested distance is

\[
  (\sqrt2-1)r
  =\frac{\sqrt2-1}{2}
     \left(a+b-\sqrt{a^2+b^2}\right).
\]

The repository's scalar language has no square-root operation. The Lean
theorem therefore states the answer by the following three exact equations.
If \(d\) is the requested distance, then

\[
  (d+r)^2=r^2+r^2,\qquad
  2r+c=a+b,\qquad
  c^2=a^2+b^2.
\]

For positive lengths these equations are equivalent to the displayed answer.

## Geometric proof

Write the triangle as \(OAB\), where \(O\) is the right-angle vertex. Let
the incircle have center \(I\), radius \(r\), and contact points \(P,Q,R\)
on \(OA,OB,AB\), respectively. Let \(N\) be the point of the incircle on
the segment \(OI\) nearest to \(O\), and put \(d=ON\).

The radii \(IP\) and \(IQ\) are perpendicular to the two legs. Since the
legs are perpendicular, \(OPIQ\) is a square. In particular

\[
  OP=PI=IQ=QO=r.
\]

The triangle \(OPI\) is right at \(P\), so the Pythagorean theorem gives

\[
  OI^2=OP^2+PI^2=r^2+r^2.
\]

Because \(O,N,I\) occur in that order and \(NI=r\), segment additivity gives
\(OI=d+r\). Hence

\[
  (d+r)^2=r^2+r^2.
\]

Tangent segments drawn from the same point to a circle are equal. Therefore

\[
  OP=OQ=r,qquad AP=AR,qquad BQ=BR.
\]

Splitting the three sides at their contact points now gives

\[
\begin{aligned}
  a+b
    &= (OP+PA)+(OQ+QB) \\
    &= 2r+AR+RB \\
    &= 2r+c.
\end{aligned}
\]

Finally, the locally proved Pythagorean theorem applied to \(OAB\) gives
\(c^2=a^2+b^2\). Solving the three positive-length equations yields the
answer above.

## Correspondence with the Lean formalization

`Configuration` contains the three vertices, the incircle, its three contact
points, and the nearest boundary point. The three `TangentAt` fields and the
three betweenness fields say that the circle touches the three actual side
segments, rather than merely their supporting lines. `nearest_on_circle` and
`nearest_between` say that \(N\) lies on the circle between \(O\) and \(I\).

The given right angle is represented synthetically: `reflectedA` is the
reflection of \(A\) in \(O\), while \(B\) is equidistant from \(A\) and
`reflectedA`. Thus \(OB\) is the perpendicular bisector of the straight
segment through \(A,O,\text{reflectedA}\), which is the repository's
reflection form of \(OA\perp OB\).

The four `cornerCenter` fields are raw betweenness and congruence witnesses
that the diagonals \(OI\) and \(PQ\) have a common midpoint. This is the
point-reflection description of the contact rectangle forced by the two
tangent radii and the right corner. The proof uses only these four primitive
facts; it no longer assumes the stronger `Rectangle` predicate (whose
noncollinearity and angle components were unused). Point-reflection
congruence then gives \(OP=IQ=r\).

`tangent_symmetric_equidistant` derives the perpendicular-bisector form of a
tangent directly from the repository's incidence definition of tangency.
`pythagorean_on_projection_line` uses it to prove the first square equation.
`equal_tangent_lengths` proves each equal-tangent assertion locally, and
segment additivity yields \(2r+c=a+b\). A second local Pythagorean argument,
using the reflection representation of the original right angle, yields the
last equation.

## Assumption audit

- No numerical radius, distance, inradius, or Pythagorean equation occurs in
  `Configuration`.
- The contact points are constrained to the actual sides by betweenness.
- The common-midpoint data are explicit incidence/congruence symmetry
  witnesses, not a precomputed length equality. They express the contact
  rectangle geometrically and are permitted construction data under
  `proof_rules.md`.
- The right-angle representation is geometric and contains no length formula.
- Equal tangent lengths and both Pythagorean equations are proved locally.
- The problem imports no other problem's local development and introduces no
  `axiom` or `sorry`.
