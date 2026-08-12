# Sharygin, PDF page 12, problem 9

## Problem

If `AM` bisects the interior angle of triangle `ABC`, prove
`BM : MC = AB : AC`.  Prove the analogous statement for the exterior angle bisector, where `M`
lies on an extension of `BC`.

## Proof represented in Lean

For the interior case, use the equality of the two angles at `A` and the collinearity of
`B, M, C` to build the two similar-triangle configurations on either side of the bisector.
The problem-local proportionality theorem converts this similarity into the cross-multiplied
identity `BM * AC = MC * AB`.

For the exterior case, the same construction is carried out with the appropriate opposite ray
and directed angle.  The resulting similarity yields `BM * AC = CM * AB`, again avoiding
division.

## Formalization audit

Separate interior and exterior configuration structures record the nondegenerate triangle,
the relevant betweenness order on `BC` or its extension, and the synthetic angle-bisector
condition.  The ratio identities are conclusions, not fields.  Both clauses of the printed
problem are formalized, with ratios expressed safely by cross multiplication.
