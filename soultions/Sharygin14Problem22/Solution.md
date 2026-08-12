# Sharygin, PDF page 14, problem 22

## Problem

The hypotenuse of a right triangle has length \(c\), and one of its acute
angles is \(30^\circ\). A circle centered at the vertex of the
\(30^\circ\) angle divides the triangle into two regions of equal area. Find
the radius of the circle.

## Answer

If \(r\) is the radius and \(\ell\) is the longer leg adjacent to the
\(30^\circ\) angle, then the Lean theorem proves the two exact equations

\[
  4\ell^2=3c^2,
  \qquad
  2\pi r^2=3c\ell.
\]

Because lengths are positive, the first equation says
\(\ell=\sqrt3c/2\). Consequently

\[
  r^2=\frac{3\sqrt3}{8\pi}c^2,
  \qquad
  r=c\sqrt{\frac{3\sqrt3}{8\pi}}.
\]

The formal result uses the first pair of equations because the repository's
ordered scalar system does not introduce division or square-root operations.

## Geometric proof

Let the right triangle be \(ABC\), with the right angle at \(B\), the
\(30^\circ\) angle at \(A\), hypotenuse \(AC=c\), longer leg
\(AB=\ell\), and shorter leg \(BC=s\).

Reflect \(C\) through \(B\) to a point \(D\). The two right triangles
\(ABC\) and \(ABD\) are congruent by SAS, so \(AC=AD\). The doubled angle
\(CAD\) is \(60^\circ\); the local synthetic argument in
`ThirtyDegree.lean` compares it with an equilateral triangle and proves that
\(ACD\) is equilateral. Hence

\[
  c=AC=CD=CB+BD=2s.
\]

Applying the locally proved Pythagorean theorem gives

\[
  \ell^2+s^2=c^2.
\]

Together with \(c=2s\), this yields

\[
  4\ell^2=3c^2.
\]

Now consider the circle centered at \(A\) with radius \(r\). Its part inside
the triangle is a sector of angle \(30^\circ\). Twelve congruent copies of
that sector partition the whole disk. Since the circle divides the triangle
into two equal-area parts, the selected sector has half the area of the
triangle. Therefore

\[
  \pi r^2
    =12\left(\frac12\operatorname{area}(ABC)\right)
    =6\operatorname{area}(ABC).
\]

The right-triangle area formula, derived locally from finite additivity and
the rectangle-area normalization, is

\[
  2\operatorname{area}(ABC)=\ell s.
\]

Thus \(\pi r^2=3\ell s\). Substituting \(c=2s\) gives

\[
  2\pi r^2=3c\ell,
\]

which, together with \(4\ell^2=3c^2\), is the claimed answer.

## Correspondence with the Lean formalization

`ThirtyDegree.Configuration` records the given nondegenerate right triangle
and geometric witnesses that its angle at \(A\) is \(30^\circ\). It does not
assume either of the two equations in the answer. The theorem
`hypotenuse_eq_twice_opposite` derives \(c=2s\) from those witnesses.

`TwelveSectorPartition` records twelve actual pairwise-disjoint congruent
regions whose union is the disk. The field `selected_sector` identifies the
first of these regions with the intersection of the disk and the triangle.
These are exact region and construction witnesses, not numerical area
assumptions. The field `circle_bisects_triangle` is precisely the condition
from the problem that this intersection has half the triangle's area.
Finite additivity and invariance of area under the supplied congruences then
derive that the disk has six times the triangle's area.

Finally, `right_triangle_double_area` derives the triangle-area identity,
and the two private algebraic lemmas in `Solution.lean` rearrange the derived
equalities into the theorem's two conclusions.

## Assumption audit

- No axiom, `sorry`, or imported result from another problem is introduced in
  this problem folder.
- The equal-area condition is a given from the source problem, not the desired
  radius equation.
- The sector congruences, disjointness, and disk partition are geometric
  construction/decomposition witnesses. No sector-area formula is assumed.
- The area of a disk and the area of a rectangle use the globally approved
  area normalizations; the triangle-area formula is proved locally.
- The final theorem determines the positive radius by exact scalar equations
  without adding square roots or division to the global foundations.
