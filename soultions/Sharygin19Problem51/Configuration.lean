import Sharygin19Problem51.Scalar

/-!
# Area partition for Sharygin, PDF page 19, problem 51

The hexagon is split into six equilateral triangles.  In each one, the two
neighboring vertex discs overlap in a lens whose bounding radii make `45°`
angles.  The scaled area identities below record those direct partitions.
-/

namespace Soultions.Sharygin.Page19.Problem51.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def sixTimes (x : S.Carrier) := twice S (threeTimes S x)

structure Data where
  side : S.Carrier
  rootThree : S.Carrier
  pi : S.Carrier
  hexagonArea : S.Carrier
  sectorSum : S.Carrier
  overlapSum : S.Carrier
  coveredArea : S.Carrier
  uncoveredArea : S.Carrier
  root_three_square : S.square rootThree = threeTimes S S.one
  uncovered_partition :
    S.add uncoveredArea coveredArea = hexagonArea
  covered_partition :
    S.add coveredArea overlapSum = sectorSum
  hexagon_computation :
    fourTimes S hexagonArea =
      S.mul (sixTimes S rootThree) (S.square side)
  sector_computation :
    fourTimes S sectorSum =
      S.mul (fourTimes S pi) (S.square side)
  overlap_computation :
    fourTimes S overlapSum =
      S.mul
        (S.sub (threeTimes S pi) (sixTimes S S.one))
        (S.square side)

end Soultions.Sharygin.Page19.Problem51.Configuration
