import Euclid

/-! Pentagon triangulation data for Sharygin, PDF page 25, problem 90. -/

namespace Soultions.Sharygin.Page25.Problem90.Configuration

open Euclid
variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def fiveTimes (x : S.Carrier) := S.add (fourTimes S x) x
def eightTimes (x : S.Carrier) := twice S (fourTimes S x)
def nineTimes (x : S.Carrier) := S.add (eightTimes S x) x
def twentyFourTimes (x : S.Carrier) := threeTimes S (eightTimes S x)

structure Data where
  side : S.Carrier
  pentagonArea : S.Carrier
  firstTriangleArea : S.Carrier
  middleTriangleArea : S.Carrier
  thirdTriangleArea : S.Carrier
  area_partition :
    pentagonArea =
      S.add firstTriangleArea (S.add middleTriangleArea thirdTriangleArea)
  first_triangle :
    twentyFourTimes S firstTriangleArea = twice S (S.square side)
  middle_triangle :
    twentyFourTimes S middleTriangleArea = fiveTimes S (S.square side)
  third_triangle :
    twentyFourTimes S thirdTriangleArea = twice S (S.square side)

end Soultions.Sharygin.Page25.Problem90.Configuration
