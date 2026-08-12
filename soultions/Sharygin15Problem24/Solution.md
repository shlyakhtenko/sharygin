# Sharygin, PDF page 15, problem 24

## Problem

One median of a right triangle has length \(m\) and divides the right angle
in the ratio \(1:2\). Find the area of the triangle.

## Answer

The area is

\[
  \frac{\sqrt3}{2}m^2.
\]

The repository's scalar language does not contain square roots or division.
Accordingly, the Lean theorem gives the following equivalent exact
relations. If \(M\) is the midpoint of the hypotenuse and \(AM=m\), then

\[
  AC=m,\qquad AB^2=3m^2,qquad
  2\operatorname{area}(ABC)=AB\cdot m.
\]

Positive lengths make these equations equivalent to the displayed answer.

## Geometric proof

Let \(ABC\) be right at \(A\), let \(M\) be the midpoint of the hypotenuse
\(BC\), and suppose that

\[
  \angle BAM : \angle MAC = 1:2.
\]

Reflect \(C\) through \(A\) to a point \(C'\). Since \(AB\perp AC\), the
point \(B\) lies on the perpendicular bisector of \(CC'\), and hence
\(BC=BC'\). The local midpoint construction then proves the familiar
right-triangle median fact

\[
  AM=BM=CM.
\]

Put \(x=\angle BAM\). The triangle \(ABM\) is isosceles because \(AM=BM\),
so

\[
  \angle ABM=x.
\]

Because \(B,M,C\) are collinear, this is also the angle \(ABC\). By the
given ratio, \(\angle MAC=2x\). The angle sum in triangle \(ABM\), together
with the straight angle \(BMC\), shows that

\[
  \angle CMA=2x.
\]

Thus triangle \(AMC\) has equal angles at \(A\) and \(M\), and therefore

\[
  AC=CM.
\]

Combining this with \(CM=AM\) gives \(AC=AM=m\). Since \(M\) is the
midpoint of \(BC\), we also have \(BC=2m\). Pythagoras in the original
right triangle now yields

\[
  AB^2+AC^2=BC^2,
\]

and hence

\[
  AB^2+m^2=4m^2,qquad AB^2=3m^2.
\]

Finally, the locally derived right-triangle area formula gives

\[
  2\operatorname{area}(ABC)=AB\cdot AC=AB\cdot m.
\]

Since \(AB=\sqrt3m\), the area is \(\sqrt3m^2/2\).

## Correspondence with the Lean formalization

`Configuration` records the nondegenerate triangle \(ABC\), the midpoint
\(M\) of \(BC\), a rotation sense, and the directed-angle equation saying
that the larger part \(\angle MAC\) is twice the smaller part
\(\angle BAM\). Choosing the opposite labeling of the two legs gives the
other possible order; it has the same area.

The given right angle is recorded in two compatible forms. `right_measure`
is its directed angle-measure statement. The chosen auxiliary point
`reflectedC` is the reflection of \(C\) through \(A\), and
`b_equidistant_c_reflectedC` records \(BC=BC'\). The latter follows from
the right angle because line \(AB\) is the perpendicular bisector of
\(CC'\); it is an explicit geometric symmetry witness, not a metric formula
from the desired conclusion.

`median_to_hypotenuse_midpoint_eq` proves \(AM=BM\) from this reflection
configuration. In `problem24`, the orientation needed to transfer the base
angle of isosceles triangle \(ABM\) is derived from the midpoint
betweenness; it is no longer a configuration field. Likewise, the
noncollinearity of \(B,C,C'\) is now derived from the original triangle's
noncollinearity and the reflection, rather than assumed.

The proof then uses the local triangle-angle-sum theorem and ASA to obtain
\(AC=CM=AM\), the local Pythagorean theorem to obtain \(AB^2=3m^2\), and
`right_triangle_double_area` to obtain the final area equation. That area
lemma itself completes the right triangle to a rectangle and applies only
the approved rectangle-area normalization and congruence invariance.

## Assumption audit

- The configuration contains no area value, side-square formula, or desired
  conclusion.
- The midpoint and the \(1:2\) angle equation are exactly the source givens.
- The reflection and equidistance fields are geometric witnesses for the
  source's right angle; they contain no precomputed scalar equality.
- Two formerly redundant fields—reflected-triangle noncollinearity and an
  orientation equality—are now proved locally.
- Pythagoras, the median metric facts, the angle comparison, and the triangle
  area formula are all derived in this problem's own folder.
- The folder imports no other problem solution and contains no local `axiom`
  or `sorry`.
