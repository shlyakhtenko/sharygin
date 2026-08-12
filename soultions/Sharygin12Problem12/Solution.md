# Sharygin, PDF page 12, problem 12

## Problem

Two triangles have a common vertex `A`, and their other vertices lie on the same two rays through
`A`.  Prove that the ratio of their areas equals the ratio of the products of the two side lengths
emanating from `A`.

## Proof represented in Lean

The two triangles have the same included angle at `A`.  The problem-local area development first
derives the right-triangle base-times-height formula from rectangle area and finite additivity,
then derives how triangle area scales when either endpoint moves along one of the two rays.

Scale one side and then the other.  Multiplying the two scale identities and cancelling the
intermediate triangle gives the cross-multiplied formula

`area(T1) * (AB2 * AC2) = area(T2) * (AB1 * AC1)`.

This is exactly the equality of the two ratios without using division.

## Formalization audit

The configuration consists of the common vertex, two nondegenerate triangles, and collinearity
of corresponding vertices with the common vertex.  No angle equality needs to be added: it is
derived from the common rays/lines with the directed cases handled in the proof.  Both triangle
areas are actual `TriangleRegion` measures, and the area-ratio identity is proved rather than
assumed.
