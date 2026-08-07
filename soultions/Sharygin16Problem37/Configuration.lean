import Sharygin16Problem37.Scalar

/-!
# Tangential isosceles trapezoid data for Sharygin, PDF page 16, problem 37

The four equal-tangent facts are recorded at their elementary segment level.  Symmetry makes
the two lower tangent segments equal to `x` and the two upper ones equal to `y`.
-/

namespace Soultions.Sharygin.Page16.Problem37.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def two : S.Carrier := S.add S.one S.one

structure Data where
  lowerTangent : S.Carrier
  upperTangent : S.Carrier
  lateralSide : S.Carrier
  knownBase : S.Carrier
  height : S.Carrier
  lower_nonnegative : S.le S.zero lowerTangent
  upper_nonnegative : S.le S.zero upperTangent
  height_nonnegative : S.le S.zero height
  lateral_from_tangents :
    lateralSide = S.add lowerTangent upperTangent
  known_base_from_tangents :
    knownBase = S.add lowerTangent lowerTangent
  side_pythagorean :
    S.square lateralSide =
      S.add
        (S.square (S.sub upperTangent lowerTangent))
        (S.square height)

def Data.otherBase (data : Data S) : S.Carrier :=
  S.add data.upperTangent data.upperTangent

def Data.doubleArea (data : Data S) : S.Carrier :=
  S.mul (S.add data.knownBase data.otherBase) data.height

end Soultions.Sharygin.Page16.Problem37.Configuration
