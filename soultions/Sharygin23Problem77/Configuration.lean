import Sharygin23Problem77.Scalar

/-!
# Regular-hexagon perimeter data for Sharygin, PDF page 23, problem 77

A regular hexagon inscribed in a radius-`R` circle has perimeter `6R`.  The circumscribed
regular hexagon has apothem `R`, side `2R/√3`, and perimeter `4√3 R`.
-/

namespace Soultions.Sharygin.Page23.Problem77.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def sixTimes (x : S.Carrier) := S.add (fourTimes S x) (twice S x)

structure Data where
  radius : S.Carrier
  rootThree : S.Carrier
  inscribedPerimeter : S.Carrier
  circumscribedPerimeter : S.Carrier
  givenDifference : S.Carrier
  root_three_square :
    S.square rootThree = S.add (twice S S.one) S.one
  inscribed_value :
    inscribedPerimeter = S.mul (sixTimes S S.one) radius
  circumscribed_value :
    circumscribedPerimeter = S.mul (fourTimes S rootThree) radius
  perimeter_difference :
    S.sub circumscribedPerimeter inscribedPerimeter = givenDifference

end Soultions.Sharygin.Page23.Problem77.Configuration
