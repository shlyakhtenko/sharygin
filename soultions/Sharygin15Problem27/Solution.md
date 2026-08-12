# Sharygin, PDF page 15, problem 27

## Problem

Prove that the sum of the distances from any point inside an equilateral
triangle to its three sides is equal to the altitude of the triangle.

Here “distance to a side” is the perpendicular distance to the line
containing that side.

## Geometric proof

Let \(ABC\) be equilateral, let \(P\) be an interior point, and denote the
perpendicular distances from \(P\) to the lines \(AB,BC,CA\) by
\(x,y,z\), respectively. Let \(h\) be the altitude from \(A\) to \(BC\),
and let the common side length be \(s\).

Joining \(P\) to the three vertices partitions the triangle into the three
triangles \(ABP\), \(BCP\), and \(CAP\). Hence

\[
  [ABC]=[ABP]+[BCP]+[CAP]. \tag{1}
\]

Using each side as the base of the corresponding small triangle gives

\[
  2[ABP]=AB\cdot x=sx,
\]

\[
  2[BCP]=BC\cdot y=sy,
\]

and

\[
  2[CAP]=CA\cdot z=sz.
\]

The whole triangle, with base \(BC\), satisfies

\[
  2[ABC]=BC\cdot h=sh.
\]

Doubling (1) and substituting these four formulas yields

\[
  sh=sx+sy+sz=s(x+y+z).
\]

The common side length is nonzero, so cancellation gives

\[
  x+y+z=h.
\]

## Correspondence with the Lean formalization

`Configuration` contains a nondegenerate triangle and the two congruences
\(AB=AC\) and \(AB=BC\), which state that it is equilateral. It also
contains an auxiliary point \(D\) strictly inside \(BC\), with \(P\)
strictly inside \(AD\). This is a ray-and-side certificate that \(P\) is
inside \(ABC\): geometrically, extend ray \(AP\) until it meets the opposite
side at \(D\).

The point \(D\) is not an extra restriction on the intended interior point;
it is an explicit incidence witness for the standard crossbar construction.
The formal region language has binary cut additivity, so the proof uses
\(D\) to derive the three-piece fan decomposition through four actual
triangle cuts. No area value or desired equality is stored in this witness.

`DistanceWitness` supplies a perpendicular foot on each side line and ties
its value to the actual foot-to-\(P\) segment. `AltitudePair` is the
reflection/equidistance certificate for perpendicularity used throughout the
repository. The theorem constructs all three distance witnesses and the
altitude from \(A\) to \(BC\) using `altitudePair_exists`.

After deriving the fan identity, `problem27` applies
`triangle_double_area_base_height_all` to the whole triangle and to each of
the three smaller triangles. That base-height formula is itself derived
locally from right-triangle area, finite additivity, congruence invariance,
and the approved rectangle-area normalization. The equilateral side
congruences turn all four bases into the same nonzero length, which is then
cancelled to produce the conclusion.

## Assumption audit

- The equilateral triangle is stated through actual segment congruences, not
  scalar side variables.
- The auxiliary point \(D\) records only the incidence construction needed
  to witness that \(P\) is interior and to perform binary region cuts.
- No fan-area identity, base-height formula, or distance sum is assumed in
  `Configuration`.
- Perpendicular feet and the altitude are constructed by the theorem.
- Every distance value is the length of a certified perpendicular segment.
- The three-triangle decomposition and all base-height identities are proved
  locally before cancellation.
- The folder imports no other problem solution and contains no local `axiom`
  or `sorry`.
