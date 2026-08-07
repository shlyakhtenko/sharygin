import Sharygin16Problem36.Scalar

/-!
# Tangent coordinates for Sharygin, PDF page 16, problem 36

After rotating the circle, the `3:4:5` arc division has tangent directions corresponding to
central turns `90°, 120°, 150°`.  In unit orthogonal coordinates the first two tangents are
`x = r`, `y = r`, and the third is `sqrtThree * x + y = -2r`.
-/

namespace Soultions.Sharygin.Page16.Problem36.Coordinates

open Euclid

variable (S : OrderedScalar) [S.Axioms]

abbrev Point := S.Carrier × S.Carrier
abbrev Direction := S.Carrier × S.Carrier

def two : S.Carrier := S.add S.one S.one
def three : S.Carrier := S.add (two S) S.one

def subPoint (p q : Point S) : Direction S :=
  (S.sub p.1 q.1, S.sub p.2 q.2)

def determinant (p q : Direction S) : S.Carrier :=
  S.sub (S.mul p.1 q.2) (S.mul p.2 q.1)

/-- Radius and the geometrically constructed positive length `sqrt 3`. -/
structure Data where
  radius : S.Carrier
  sqrtThree : S.Carrier
  radius_nonnegative : S.le S.zero radius
  radius_nonzero : radius ≠ S.zero
  sqrtThree_nonnegative : S.le S.zero sqrtThree
  sqrtThree_square : S.square sqrtThree = three S

def Data.firstSecondVertex (data : Data S) : Point S :=
  (data.radius, data.radius)

def Data.secondThirdVertex (data : Data S) : Point S :=
  (S.mul (S.neg data.sqrtThree) data.radius, data.radius)

def Data.thirdFirstVertex (data : Data S) : Point S :=
  (data.radius,
    S.mul (S.neg (S.add (two S) data.sqrtThree)) data.radius)

def OnFirstTangent (data : Data S) (p : Point S) : Prop :=
  p.1 = data.radius

def OnSecondTangent (data : Data S) (p : Point S) : Prop :=
  p.2 = data.radius

def OnThirdTangent (data : Data S) (p : Point S) : Prop :=
  S.add (S.mul data.sqrtThree p.1) p.2 =
    S.neg (S.mul (two S) data.radius)

/-- Determinant of the two sides based at the first/second tangent intersection. -/
def Data.triangleDoubleArea (data : Data S) : S.Carrier :=
  determinant S
    (subPoint S data.secondThirdVertex data.firstSecondVertex)
    (subPoint S data.thirdFirstVertex data.firstSecondVertex)

/-- The scalar coefficient `3 + 2 sqrt(3)`. -/
def Data.areaCoefficient (data : Data S) : S.Carrier :=
  S.add (three S) (S.mul (two S) data.sqrtThree)

end Soultions.Sharygin.Page16.Problem36.Coordinates
