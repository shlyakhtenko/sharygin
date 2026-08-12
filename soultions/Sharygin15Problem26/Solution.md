# Sharygin, PDF page 15, problem 26

## Problem

Prove that the sum of the distances from any point of the base of an
isosceles triangle to its two equal sides is equal to the altitude drawn to
either of those sides.

Here, as in the formalization, “distance to a side” means perpendicular
distance to the line containing that side.

## Geometric proof

Let \(ABC\) be isosceles with base \(BC\), so \(AB=AC\), and let \(P\) be
any point of segment \(BC\). Write

\[
  x=\operatorname{dist}(P,AB),
  \qquad
  y=\operatorname{dist}(P,AC).
\]

Let \(h\) be the altitude from \(B\) to side \(AC\). The segment \(AP\)
divides the original triangle into triangles \(ABP\) and \(APC\), so finite
additivity of area gives

\[
  [ABC]=[ABP]+[APC]. \tag{1}
\]

Compute each area using one of the equal sides as base. Twice the area of
the whole triangle is

\[
  2[ABC]=AC\cdot h.
\]

For the two smaller triangles,

\[
  2[ABP]=AB\cdot x,
  \qquad
  2[APC]=AC\cdot y.
\]

Since \(AB=AC\), doubling (1) and substituting these formulas gives

\[
  AC\cdot h=AC\cdot x+AC\cdot y=AC(x+y).
\]

The side \(AC\) is nonzero, so cancellation yields

\[
  x+y=h.
\]

By interchanging \(B\) and \(C\), the same value is the altitude from
\(C\) to \(AB\). Thus it equals the altitude drawn to either equal side.

If \(P=B\) or \(P=C\), one of the two distances is zero and the same
argument reduces to equality of the two corresponding altitudes. These
endpoint cases are included explicitly in the formal proof.

## Correspondence with the Lean formalization

`Configuration` contains only the nondegenerate triangle, the congruence
\(AB=AC\), and the betweenness assertion placing \(P\) on the closed base
segment \(BC\).

`DistanceWitness` represents a perpendicular distance from a point to a
line. It supplies a foot on the line and either says that the point is itself
the foot (the zero-distance endpoint case), or supplies an `AltitudePair`
certifying perpendicularity. Its `value` is definitionally tied to the
actual segment from the point to the foot; it is not a freely chosen scalar.

`AltitudePair` is the repository's synthetic perpendicular certificate. Two
points on the base line are reflections through the foot, and the apex is
equidistant from them. Thus the apex-to-foot line is a perpendicular
bisector. `altitudePair_exists` constructs such a certificate from the
approved Tarski and continuity foundations; no altitude existence is assumed
in `Configuration`.

For an interior point \(P\), `problem26` constructs perpendicular witnesses
to both side lines and an altitude from \(B\) to \(AC\). It applies area
cut-additivity to the actual triangular regions and uses
`triangle_double_area_base_height_all` for the three base-height formulas.
That lemma derives the formula by splitting into right triangles and using
the approved rectangle-area normalization. The proof then substitutes
\(AB=AC\) and cancels the nonzero common side.

The theorem handles \(P=B\) and \(P=C\) separately. It represents the
distance to the incident side by the zero segment and proves the equality of
the remaining distance and altitude by comparing the two area formulas.

## Assumption audit

- `Configuration` is exactly the source data: a nondegenerate isosceles
  triangle and a point on its base.
- Perpendicular feet and the comparison altitude are constructed in the
  theorem; they are not assumed as fields.
- Each distance value is forced to be the length of its certified
  perpendicular segment.
- The area decomposition uses the actual triangle regions and the given
  betweenness of \(P\), not a precomputed scalar identity.
- The base-times-height formula is derived locally from finite additivity,
  congruence invariance, and rectangle area.
- The formal conclusion names the altitude from \(B\) to \(AC\). Swapping
  the two equal-side vertices gives the altitude from \(C\) to \(AB\), so
  this realizes the source phrase “either of the sides.”
- The folder imports no other problem solution and contains no local `axiom`
  or `sorry`.
