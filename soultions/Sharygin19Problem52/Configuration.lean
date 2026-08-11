import Sharygin19Problem52.Scalar

/-!
# Area data for Sharygin, PDF page 19, problem 52

The noncentral secant cuts off a `120°` minor segment: its sector is one
third of the disc and its centre triangle has altitude `R/2`.  The region
between the two nonintersecting chords is the half-disc minus that segment.
-/

namespace Soultions.Sharygin.Page19.Problem52.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def sixTimes (x : S.Carrier) := twice S (threeTimes S x)
def twelveTimes (x : S.Carrier) := twice S (sixTimes S x)

structure Data where
  radius : S.Carrier
  rootThree : S.Carrier
  pi : S.Carrier
  diskArea : S.Carrier
  halfArea : S.Carrier
  sectorArea : S.Carrier
  centerTriangleArea : S.Carrier
  segmentArea : S.Carrier
  betweenArea : S.Carrier
  root_three_square : S.square rootThree = threeTimes S S.one
  disk_computation : diskArea = S.mul pi (S.square radius)
  half_partition : twice S halfArea = diskArea
  sector_partition : threeTimes S sectorArea = diskArea
  triangle_computation :
    fourTimes S centerTriangleArea =
      S.mul rootThree (S.square radius)
  segment_decomposition :
    S.add segmentArea centerTriangleArea = sectorArea
  between_decomposition :
    S.add betweenArea segmentArea = halfArea

end Soultions.Sharygin.Page19.Problem52.Configuration
