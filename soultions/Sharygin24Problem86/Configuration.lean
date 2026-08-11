import Euclid

/-! Segment-partition data for Sharygin, PDF page 24, problem 86. -/

namespace Soultions.Sharygin.Page24.Problem86.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x
def fourTimes (x : S.Carrier) := twice S (twice S x)

structure Data where
  radius : S.Carrier
  rootSeven : S.Carrier
  segmentLength : S.Carrier
  insideSmall : S.Carrier
  insideLarge : S.Carrier
  outside : S.Carrier
  root_seven_square : S.square rootSeven = S.nsmul 7 S.one
  segment_value : segmentLength = twice S radius
  small_intersection : twice S insideSmall = radius
  large_intersection : twice S insideLarge = S.mul rootSeven radius
  segment_partition :
    segmentLength = S.add insideSmall (S.add insideLarge outside)

end Soultions.Sharygin.Page24.Problem86.Configuration
