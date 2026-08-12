import Sharygin26Problem96.Scalar

/-!
# Regular-hexagon data for Sharygin, PDF page 26, problem 96

In the regular hexagon, `CD = R`, `AC = √3 R`, and the opposite vertices give the diameter
`AD = 2R`.  Equal tangent segments from the three vertices of triangle `ACD` give
`AC + CD = AD + 2r` for its inradius `r`.
-/

namespace Soultions.Sharygin.Page26.Problem96.Configuration

open Euclid
variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x

structure Data where
  radius : S.Carrier
  inradius : S.Carrier
  rootThree : S.Carrier
  sideAC : S.Carrier
  sideCD : S.Carrier
  sideAD : S.Carrier
  root_three_square : S.square rootThree = threeTimes S S.one
  short_chord : sideCD = radius
  long_chord : sideAC = S.mul rootThree radius
  diameter : sideAD = twice S radius
  tangent_length_decomposition :
    S.add sideAC sideCD = S.add sideAD (twice S inradius)

end Soultions.Sharygin.Page26.Problem96.Configuration
