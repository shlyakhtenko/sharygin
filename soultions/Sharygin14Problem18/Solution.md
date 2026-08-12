# Sharygin, PDF page 14, problem 18

## Problem

The distances from a vertex `A` of a triangle to the two adjacent points where the incircle touches `AB` and `AC` are equal to `p - a`, where `p` is the semiperimeter and `a = BC`.

## Formalization audit

The configuration consists only of the data present in the problem:

- three noncollinear vertices `A`, `B`, and `C`;
- one circle;
- three contact points lying on the closed segments `AB`, `AC`, and `BC`; and
- tangency of the corresponding side line to that circle at each stated contact point.

Here tangency means that the contact point is on the circle and is the unique point where that side line meets the circle. Thus it is a definition in the repository's incidence language, not an assumed perpendicular-radius theorem. The noncollinearity field records the ordinary meaning of the word “triangle”; the algebraic proof does not exploit it as an extra shortcut.

No equality of tangent lengths, side-length identity, semiperimeter identity, or part of the desired conclusion is included in the configuration.

The conclusion states both equality of the two tangent segments from `A` and the division-free formula

`2 · AT = AB + AC - BC`.

This is exactly the statement `AT = p - a` with division cleared: since
`2p = AB + AC + BC` and `a = BC`, doubling `p - a` gives
`AB + AC - BC`. This avoids assuming that the abstract scalar system has a
preselected numeral `1/2`.

## Proof

First derive the equal-tangent fact used here: for two tangent lines from the same point, join the circle's center to the contact points. Each radius is perpendicular to its tangent line (itself derived from the definition of tangency), so the two resulting right triangles have the same hypotenuse and equal radius legs. Their remaining legs are equal by the problem-local Pythagorean theorem and nonnegativity of lengths. No equal-tangent theorem is assumed in the configuration.

Apply that derived fact at all three vertices. If the tangent lengths from `A`, `B`, and `C` are called `x`, `y`, and `z`, respectively, segment additivity along the three sides gives

`AB = x + y`, `AC = x + z`, and `BC = y + z`.

Therefore

`AB + AC = BC + 2x`.

Subtracting `BC` gives `2x = AB + AC - BC`. The two contact distances from `A` both equal `x`, completing the proof.
