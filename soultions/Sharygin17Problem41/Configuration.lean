import Sharygin17Problem41.Scalar

/-!
# Tangential isosceles trapezoid data for Sharygin, PDF page 17, problem 41

Equal tangent segments give twice the lateral side as the sum of the bases.  Isosceles
symmetry gives twice the horizontal projection of a lateral side as their difference.
-/

namespace Soultions.Sharygin.Page17.Problem41.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def two : S.Carrier := S.add S.one S.one

structure Data where
  largeBase : S.Carrier
  smallBase : S.Carrier
  ratio : S.Carrier
  lateralSide : S.Carrier
  horizontalProjection : S.Carrier
  base_ratio : largeBase = S.mul ratio smallBase
  tangent_sum :
    S.mul (two S) lateralSide = S.add largeBase smallBase
  symmetric_difference :
    S.mul (two S) horizontalProjection = S.sub largeBase smallBase

/-- The division-free cosine characterization of the base angle. -/
def Data.BaseAngleRelation (data : Data S) : Prop :=
  S.mul (S.add data.largeBase data.smallBase) data.horizontalProjection =
    S.mul (S.sub data.largeBase data.smallBase) data.lateralSide

end Soultions.Sharygin.Page17.Problem41.Configuration
