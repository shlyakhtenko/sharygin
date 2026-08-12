# Sharygin, PDF page 15, problem 28

## Problem

In an isosceles triangle \(ABC\) with base \(AC\), a point \(M\) on the
base satisfies

\[
  AM=a,\qquad MC=b.
\]

Circles are inscribed in triangles \(ABM\) and \(CBM\). Find the distance
between the points where these circles touch side \(BM\).

## Answer

The distance is

\[
  \frac{|a-b|}{2}.
\]

Because the repository's scalar language has no absolute-value operation,
Lean states the equivalent ordered disjunction. If the contact points on
\(BM\) are \(X\) and \(Y\), then either

\[
  AM=MC+2XY
\]

or

\[
  MC=AM+2XY.
\]

## Geometric proof

Let the incircle of \(ABM\) touch \(BM,AM,AB\) at \(X,U,V\), respectively.
Equal tangent segments from the same vertex give

\[
  MX=MU,\qquad AU=AV,\qquad BV=BX.
\]

Splitting the three sides at their contact points and adding shows

\[
  AM+BM=AB+2MX. \tag{1}
\]

Similarly, let the incircle of \(CBM\) touch \(BM,MC,BC\) at \(Y,W,Z\).
Equal tangent segments give

\[
  MY=MW,\qquad CW=CZ,\qquad BZ=BY,
\]

and hence

\[
  MC+BM=BC+2MY. \tag{2}
\]

The original triangle is isosceles with base \(AC\), so \(AB=BC\).
Subtracting the common terms in (1) and (2) yields

\[
  AM+2MY=MC+2MX. \tag{3}
\]

Both \(X\) and \(Y\) lie on segment \(BM\). If they occur in the order
\(B-X-Y-M\), then \(MX=MY+XY\). Substituting this into (3) and cancelling
\(2MY\) gives

\[
  AM=MC+2XY.
\]

If their order is \(B-Y-X-M\), then \(MY=MX+XY\), and the same argument
gives

\[
  MC=AM+2XY.
\]

Thus in both cases \(XY=|AM-MC|/2=|a-b|/2\).

## Correspondence with the Lean formalization

`Configuration` contains a nondegenerate triangle with \(AB=BC\), the
point \(M\) on the base segment \(AC\), the six side-contact points, and the
two contact points \(X,Y\) on segment \(BM\). Each `TangentAt` field says
that the relevant circle meets that side line only at its stated contact
point, and the accompanying betweenness field places the contact on the
actual side segment. Thus these data describe the two incircles geometrically
without assuming any tangent-length equation.

`equal_tangent_lengths` is proved locally from the repository's incidence
definition of tangency. It derives perpendicularity of the radius and then
uses the local right-triangle square identity and nonnegative-square
injectivity. `problem28` applies it three times to each incircle and uses
segment additivity to derive equations (1) and (2).

The local `bounded_connectivity` theorem determines which of \(X,Y\) comes
first on \(BM\). In each case, betweenness additivity expresses the longer
of \(MX,MY\) as the shorter plus \(XY\), after which scalar cancellation
produces the corresponding branch of the final disjunction.

## Assumption audit

- The source lengths \(a,b\) are represented by the actual segments
  \(AM,MC\); no unrelated scalar certificate is introduced.
- Isosceles means exactly the source congruence \(AB=BC\).
- Every contact point is on its actual triangle side, and tangency is the
  global incidence definition—not an assumed equal-tangent formula.
- Neither circle configuration contains the desired distance relation or a
  semiperimeter equation.
- Equal tangent lengths, contact-point ordering, and all segment equations
  are proved locally.
- The conclusion covers both possible orders of \(X,Y\), including \(X=Y\)
  when \(AM=MC\).
- The folder imports no other problem solution and contains no local `axiom`
  or `sorry`.
