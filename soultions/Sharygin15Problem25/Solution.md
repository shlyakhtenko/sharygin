# Sharygin, PDF page 15, problem 25

## Problem

In triangle \(ABC\), the side lengths are

\[
  BC=a,\qquad CA=b,\qquad AB=c.
\]

Find the ratio in which the point of intersection of the angle bisectors
divides the bisector of angle \(B\).

## Answer

If the bisector from \(B\) meets \(AC\) at \(D\), and the intersection of
the angle bisectors is \(I\), then

\[
  BI:ID=(a+c):b.
\]

Lean states this without division as

\[
  BI\cdot CA=ID\cdot(BC+AB).
\]

## Geometric proof

Let \(BD\) be the internal bisector of angle \(B\), with \(D\) on
\(AC\). Apply the angle-bisector theorem in triangle \(ABC\):

\[
  \frac{AD}{DC}=\frac{AB}{BC}.
\]

In cross-multiplied form this is

\[
  AD\cdot BC=DC\cdot AB. \tag{1}
\]

The point \(I\) lies on \(BD\). Since \(AI\) is another internal angle
bisector, and ray \(AD\) is the same as ray \(AC\), \(AI\) bisects angle
\(BAD\). Apply the angle-bisector theorem again, now in triangle \(ABD\):

\[
  \frac{BI}{ID}=\frac{AB}{AD},
\]

or

\[
  BI\cdot AD=ID\cdot AB. \tag{2}
\]

From (1),

\[
  \frac{AB}{AD}
    =\frac{AB+BC}{AD+DC}
    =\frac{AB+BC}{AC}.
\]

Combining this with (2) gives

\[
  \frac{BI}{ID}=\frac{AB+BC}{AC}
    =\frac{a+c}{b},
\]

as required.

## The locally formalized angle-bisector theorem

The proof does not import or assume the angle-bisector theorem. For a
triangle with an internal bisector from a vertex \(A\), the local proof
extends \(BA\) beyond \(A\) to a point \(E\) with \(AE=AC\). The symmetry
that defines the angle bisector, together with a midpoint construction,
proves

\[
  AM\parallel CE,

\]

where \(M\) is the point where the bisector meets \(BC\). The resulting
parallel-line fourth-proportional relation gives

\[
  BM\cdot AC=MC\cdot AB.
\]

All parallelism and proportionality steps are derived in this problem's own
folder. Thus the two uses above are applications of a theorem proved locally,
not imported Euclidean knowledge.

## Correspondence with the Lean formalization

`Configuration` contains a nondegenerate triangle, the point \(D\) strictly
inside \(AC\), and the point \(I\) strictly inside \(BD\). `b_bisector`
states geometrically that ray \(BD\) is the internal bisector at \(B\), and
`a_bisector` states that ray \(AI\) bisects angle \(BAD\). Since \(D\) lies
on segment \(AC\), this is the same bisector ray as the one at \(A\) in the
original triangle.

An angle bisector is represented by `Bisector.Witness`: equal-radius sample
points on the two side rays are mirror-symmetric with respect to a point on
the proposed bisector ray. Its universal equal-radius clause is the
scale-independent synthetic definition of ray symmetry; it contains no
length ratio involving \(D\) or \(I\). The auxiliary sample points are
geometric witnesses for that definition.

`interior_ratio` proves the cross-multiplied angle-bisector theorem using the
extension-and-parallel construction described above. `problem25` invokes it
once in \(ABC\) and once in \(ABD\). It then uses
\(CA=AD+DC\), distributes the products, cancels the nonzero length \(AD\),
and obtains

\[
  BI\cdot CA=ID\cdot(BC+AB).
\]

## Assumption audit

- The triangle side lengths are represented by the actual segment lengths;
  no unrelated scalar certificate replaces the geometry.
- The only ratio-like conclusion in the theorem is derived. Neither
  `Configuration` nor `Bisector.Witness` contains it.
- Betweenness places \(D\) and \(I\) on the actual internal segments, not
  merely on supporting lines. The endpoint inequalities record the source's
  nondegenerate internal intersections.
- Only the bisectors at \(A\) and \(B\) are recorded. Their intersection is
  the point called the intersection of the angle bisectors in the source;
  proving separately that it lies on the third bisector is unnecessary for
  the requested division ratio.
- The angle-bisector theorem is proved locally from symmetry, midpoint,
  parallel, and fourth-proportional facts.
- The folder imports no other problem solution and contains no local `axiom`
  or `sorry`.
