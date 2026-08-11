import Sharygin18Problem50.Scalar

/-!
# Lens-area data for Sharygin, PDF page 18, problem 50

The diagonal tangency makes the two intersection angles `45°` and `135°`.
Finite additivity therefore expresses the lens as those two sectors minus
their two centre triangles.  All displayed identities are multiplied by
eight, so no division operation is needed.
-/

namespace Soultions.Sharygin.Page18.Problem50.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def fiveTimes (x : S.Carrier) := S.add (fourTimes S x) x
def eightTimes (x : S.Carrier) := twice S (fourTimes S x)

structure Data where
  side : S.Carrier
  rootTwo : S.Carrier
  pi : S.Carrier
  commonArea : S.Carrier
  sectorSum : S.Carrier
  triangleSum : S.Carrier
  root_two_square : S.square rootTwo = twice S S.one
  lens_decomposition :
    S.add commonArea triangleSum = sectorSum
  sector_computation :
    eightTimes S sectorSum =
      S.mul
        (S.mul
          (S.sub (fiveTimes S S.one) (threeTimes S rootTwo)) pi)
        (S.square side)
  triangle_computation :
    eightTimes S triangleSum =
      S.mul (fourTimes S (S.sub rootTwo S.one)) (S.square side)

end Soultions.Sharygin.Page18.Problem50.Configuration
