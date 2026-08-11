import Sharygin25Problem88.Scalar

/-! Inradius/circumradius data for Sharygin, PDF page 25, problem 88. -/

namespace Soultions.Sharygin.Page25.Problem88.Configuration

open Euclid
variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x

structure Data where
  ratio : S.Carrier
  cosBaseAngle : S.Carrier
  discriminantRoot : S.Carrier
  radius_ratio_relation :
    ratio = twice S (S.mul cosBaseAngle (S.sub S.one cosBaseAngle))
  discriminant_square :
    S.square discriminantRoot = S.sub S.one (twice S ratio)

end Soultions.Sharygin.Page25.Problem88.Configuration
