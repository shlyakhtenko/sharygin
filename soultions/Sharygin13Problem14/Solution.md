# Sharygin, PDF page 13, problem 14

## Problem

Prove that the area of a quadrilateral is half the product of its diagonals and the sine of the angle between them.

## Formalization audit

The quadrilateral has crossing diagonals `AC` and `BD`, meeting at `O`. Its area is the sum of the areas of triangles `ACB` and `ACD`. The feet of the perpendiculars from `B` and `D` to `AC` are independent points; importantly, the formalization does **not** identify either foot with `O`.

`DiagonalSine.value` records the common sine of the two vertical angles at `O` through its defining right-triangle equations: the two perpendicular heights are `OB · sin` and `OD · sin`. These fields do not assume the requested quadrilateral-area equation.

An earlier version incorrectly set both perpendicular feet equal to `O`, inadvertently restricting the theorem to perpendicular diagonals. The audited version removes that error.

**Remaining audit obligation:** the current theorem is conditional on a `DiagonalSine` realization. To make the result fully universal, the local development must construct that realization and derive that the two vertical-angle right triangles give the same value. Until that existence/compatibility theorem is added, problem 14 is corrected but not yet marked complete.

## Proof

Use `AC` as the base of both triangles. The derived base-times-height theorem gives

`2 area(ACB) = AC · OB · sin θ`

and

`2 area(ACD) = AC · OD · sin θ`.

Because `O` lies between `B` and `D`, segment additivity gives `BD = OB + OD`. Add the two area identities and factor:

`2 area(ABCD) = AC · (OB + OD) · sin θ = AC · BD · sin θ`.
