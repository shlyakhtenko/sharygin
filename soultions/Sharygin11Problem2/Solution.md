# Sharygin, PDF page 11, problem 2

## Problem

Prove that the three medians divide a triangle into six equivalent parts.  Here “equivalent” is
interpreted in its classical geometric sense: the six parts have equal area.  They need not be
congruent.

## Proof represented in Lean

First construct the common median point `G` and the side midpoints `D`, `E`, and `F`, using the
problem-local median construction.  This gives the six triangles, in cyclic order,

`GAF`, `GFB`, `GBD`, `GDC`, `GCE`, and `GEA`.

The two triangles based on the two halves of any one side have equal area.  For example, `AF`
and `FB` are equal because `F` is the midpoint of `AB`, and the triangles `GAF` and `GFB` have
the same altitude from `G`.  Lean derives this fact from the rectangle-area normalization,
finite additivity, and the problem-local base-times-height theorem; it is not assumed as an area
axiom.  The same argument gives the equal pairs along `BC` and `CA`.

Each full median also divides the original triangle into two equal-area triangles.  Cutting those
halves at `G` expresses them as sums of three of the six small triangles.  Comparing the sums for
two medians, and cancelling the already equal paired terms, shows that the three paired area
values are equal.  Consequently all six small triangles have one common unsigned area.

## Formalization audit

The Lean theorem is universal over every nondegenerate triangle and constructs the centroid and
all three side midpoints.  Its conclusion explicitly compares the areas of the six triangular
regions.  It assumes only the approved plane, angle, length, and area axioms; neither concurrence,
the `1 : 2` median ratio, nor equal-area statements are supplied by the caller.  The interpretation
of “equivalent” as equal area is necessary and matches the standard meaning here, since the six
triangles are not generally congruent.
