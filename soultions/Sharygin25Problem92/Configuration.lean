import Euclid

/-! Equilateral triangle in a square, Sharygin, PDF page 25, problem 92. -/

namespace Soultions.Sharygin.Page25.Problem92.Configuration

open Euclid
variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def sixteenTimes (x : S.Carrier) := fourTimes S (fourTimes S x)

structure Data where
  squareSide : S.Carrier
  triangleSide : S.Carrier
  rootThree : S.Carrier
  triangleArea : S.Carrier
  root_three_square : S.square rootThree = threeTimes S S.one
  diagonal_intersection :
    twice S triangleSide = S.mul (S.sub rootThree S.one) squareSide
  equilateral_area :
    fourTimes S triangleArea = S.mul rootThree (S.square triangleSide)

end Soultions.Sharygin.Page25.Problem92.Configuration
