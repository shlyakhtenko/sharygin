# Sharygin, PDF page 19, problem 51

## Problem

The six vertices of a regular hexagon of side `a` are the centers of six circles of radius
`a / sqrt(2)`.  Find the area `U` of the part of the hexagon lying outside all six circles.

The Lean conclusion is the division-free formula

`4U = (6 sqrt(3) - 6 - pi) a^2`.

## Proof represented in Lean

Divide the hexagon into the six congruent equilateral triangles joining the center to consecutive
vertices.  In one such cell, only the two circles centered at its endpoint vertices contribute.
Split the cell into four actual regions: uncovered, covered only by the left circle, covered only
by the right circle, and covered by both.  Finite additivity gives the local inclusion-exclusion
identity

`uncovered + left sector + right sector = cell + overlap`.

Each endpoint contribution is a `60`-degree sector.  An explicit partition of its disk into six
congruent sectors therefore computes the sector area from the disk-area axiom.  The overlap in
one cell is a half-lens.  Cut it into two circular segments.  Each segment is a `45`-degree sector
minus a right triangle, and an explicit eight-sector disk partition computes those sector areas.
Pythagoras and the rectangle-derived right-triangle area formula show that each small right
triangle has area `a^2 / 8`.

The altitude of the equilateral cell is derived by Pythagoras as `sqrt(3) a / 2`, so the cell area
is `sqrt(3) a^2 / 4`.  Substitution into local inclusion-exclusion and multiplication by the six
congruent cells yields

`U = ((6 sqrt(3) - 6 - pi) / 4) a^2`.

## Formalization audit

The uncovered region is definitionally the union of the six center triangles minus the union of
the six closed vertex disks.  The configuration supplies actual region partitions, rigid-motion
congruence witnesses, circle-intersection and midpoint construction data, and right-angle
certificates.  These are geometric witnesses, not scalar area formulas.  Disk fractions, triangle
areas, lens area, equilateral altitude, and the final inclusion-exclusion calculation are all
derived in Lean.  The configuration contains no precomputed hexagon, sector, overlap, covered, or
uncovered area, which corrects the earlier scalar-certificate formalization.
