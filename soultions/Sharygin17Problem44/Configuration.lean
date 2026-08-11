import Sharygin17Problem44.Scalar

/-!
# Tangential trapezoid data for Sharygin, PDF page 17, problem 44

The distance between two parallel tangent bases is the diameter.  Equal tangent segments give
the sum of the bases as twice the lateral side, and the trapezoid area formula is recorded in
doubled form.
-/

namespace Soultions.Sharygin.Page17.Problem44.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) : S.Carrier := S.add x x
def eightTimes (x : S.Carrier) : S.Carrier := twice S (twice S (twice S x))

structure Data where
  area : S.Carrier
  radius : S.Carrier
  height : S.Carrier
  lateralSide : S.Carrier
  baseSum : S.Carrier
  diameter_is_height : twice S radius = height
  altitude_is_half_side : lateralSide = twice S height
  tangent_base_sum : baseSum = twice S lateralSide
  trapezoid_double_area : twice S area = S.mul baseSum height

end Soultions.Sharygin.Page17.Problem44.Configuration
