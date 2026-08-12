# Sharygin, PDF page 12, problem 10

## Problem

Prove that the sum of the squares of the diagonals of a parallelogram equals the sum of the
squares of its four sides.

## Proof represented in Lean

Represent the parallelogram by the common midpoint of its diagonals: the half-turn about this
point exchanges `A` with `C` and `B` with `D`.  The two diagonals are therefore twice their
half-diagonals, while opposite sides are congruent.

Apply the problem-local Pythagorean/parallelogram calculation to the two triangles determined by
the diagonal midpoint.  Expanding the doubled diagonal squares and replacing opposite-side
lengths by their congruent partners gives

`AC^2 + BD^2 = AB^2 + BC^2 + CD^2 + DA^2`.

## Formalization audit

The configuration's two point-reflection witnesses are an exact synthetic characterization of a
nondegenerate parallelogram by bisecting diagonals.  They imply, rather than assume, the opposite
side congruences.  The diagonal-square equality is derived from the repository's multiplication
and Pythagorean layer and is not a configuration hypothesis.
