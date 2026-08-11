import Sharygin22Problem70.Scalar

/-!
# Midpoint-distance data for Sharygin, PDF page 22, problem 70

The coordinate displacement is `(a/4,3a/4)`, hence `(4d)²=10a²`.
-/

namespace Soultions.Sharygin.Page22.Problem70.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def fiveTimes (x : S.Carrier) := S.add (fourTimes S x) x
def tenTimes (x : S.Carrier) := twice S (fiveTimes S x)

structure Data where
  side : S.Carrier
  distance : S.Carrier
  rootTen : S.Carrier
  root_ten_square : S.square rootTen = tenTimes S S.one
  distance_square : S.square (fourTimes S distance) = tenTimes S (S.square side)
  geometric_root :
    S.add (fourTimes S distance) (S.mul rootTen side) ≠ S.zero

end Soultions.Sharygin.Page22.Problem70.Configuration
