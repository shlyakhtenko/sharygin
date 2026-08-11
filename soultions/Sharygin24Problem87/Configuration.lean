import Sharygin24Problem87.Scalar

/-! Trisected-altitude data for Sharygin, PDF page 24, problem 87. -/

namespace Soultions.Sharygin.Page24.Problem87.Configuration

open Euclid
variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def twelveTimes (x : S.Carrier) := S.nsmul 12 x
def thirteenTimes (x : S.Carrier) := S.add (twelveTimes S x) x

structure Data where
  sideAB : S.Carrier
  sideAC : S.Carrier
  bd : S.Carrier
  dc : S.Carrier
  altitude : S.Carrier
  rootThirteen : S.Carrier
  side_ab_value : sideAB = fourTimes S S.one
  bisector_trisection : bd = twice S S.one
  median_trisection : dc = S.one
  ab_pythagorean : S.square sideAB = S.add (S.square bd) (S.square altitude)
  ac_pythagorean :
    S.square sideAC = S.add (S.square (S.sub bd dc)) (S.square altitude)
  root_thirteen_square : S.square rootThirteen = thirteenTimes S S.one
  positive_sum : S.add sideAC rootThirteen ≠ S.zero

end Soultions.Sharygin.Page24.Problem87.Configuration
