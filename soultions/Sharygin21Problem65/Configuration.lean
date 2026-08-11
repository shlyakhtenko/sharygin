import Sharygin21Problem65.Scalar

/-!
# Coordinate configuration for Sharygin, PDF page 21, problem 65

Take `A` as the origin and the two sides of the square as coordinate axes.  Coordinates are
scaled by four.  The circle center lies on the perpendicular bisector of the segment joining
the midpoint of `AB` to the square center, and on the perpendicular bisector of the segment
joining the square center to `C`.  The two displayed equations are precisely those bisector
equations after clearing the common factor four.
-/

namespace Soultions.Sharygin.Page21.Problem65.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) : S.Carrier := S.add x x
def fourTimes (x : S.Carrier) : S.Carrier := twice S (twice S x)
def fiveTimes (x : S.Carrier) : S.Carrier := S.add (fourTimes S x) x
def sixTimes (x : S.Carrier) : S.Carrier := S.add (fiveTimes S x) x

structure Data where
  side : S.Carrier
  centerX4 : S.Carrier
  centerY4 : S.Carrier
  four_side_ne_zero : fourTimes S side ≠ S.zero
  midpoint_squareCenter_bisector :
    S.mul (fourTimes S side) centerY4 =
      S.mul (fourTimes S side) side
  squareCenter_vertex_bisector :
    S.mul (fourTimes S side) (S.add centerX4 centerY4) =
      S.mul (fourTimes S side) (sixTimes S side)

end Soultions.Sharygin.Page21.Problem65.Configuration
