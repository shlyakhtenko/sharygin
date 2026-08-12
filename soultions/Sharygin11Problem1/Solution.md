# Sharygin, PDF page 11, problem 1

## Problem

Prove that the three medians of a nondegenerate triangle meet at one point and that this point
divides every median in the ratio `1 : 2`.  The convention used in the Lean statement is

`(centroid-to-side-midpoint) : (vertex-to-centroid) = 1 : 2`.

## Proof represented in Lean

Let `M`, `N`, and `P` be the midpoints of `BC`, `CA`, and `AB`.  Inner Pasch applied to the
triangle produces a point `G` lying between `A` and `M` and also between `B` and `N`; thus the
first two medians meet inside the triangle.

Reflect `G` in `M`, obtaining `K`.  The half-turn about `M` sends `B` to `C` and `G` to `K`, so
`BG` and `CK` are congruent and parallel.  The problem-local midpoint and parallel-line lemmas
then show that `G` is the midpoint of `AK`.  A second midpoint-parallel construction, now using
the midpoint `P` of `AB`, proves that `C`, `G`, and `P` are collinear.  Hence the same point `G`
lies on all three medians.

Because `M` is the midpoint of `GK` and `G` is the midpoint of `AK`, the segment from `A` to
`G` consists of two consecutive copies of `GM`.  Cyclic repetitions of the same construction
give that `BG` consists of two copies of `GN`, and `CG` consists of two copies of `GP`.  These
are exactly the three `TwiceSegment` witnesses stored in `MedianPointData`, and they express the
required `1 : 2` division.

## Formalization audit

The final theorem is universal over the three vertices and assumes only that they are not
collinear, which is the intrinsic nondegeneracy condition for a triangle.  Midpoints,
intersections, reflections, parallel lines, concurrence, and all three ratio witnesses are
constructed in the proof from `Plane.Axioms`; none is supplied as a hypothesis or configuration
field.  The conclusion records one common point on all three median lines and the required ratio
on every median, so it matches both parts of the printed problem.
