import Sharygin24Problem84.Scalar

/-!
# Common-chord data for Sharygin, PDF page 24, problem 84

The chord subtending `90°` has length `sqrt(2) * r90`; the same chord subtending `60°`
has length `r60`.  Adding the two center-to-chord perpendiculars gives the second displayed
relation.  These are the two direct right-triangle computations for this configuration.
-/

namespace Soultions.Sharygin.Page24.Problem84.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def threeTimes (x : S.Carrier) := S.add (twice S x) x
def fourTimes (x : S.Carrier) := twice S (twice S x)

structure Data where
  distance : S.Carrier
  radius90 : S.Carrier
  radius60 : S.Carrier
  rootTwo : S.Carrier
  rootThree : S.Carrier
  rootSix : S.Carrier
  root_two_square : S.square rootTwo = twice S S.one
  root_three_square : S.square rootThree = threeTimes S S.one
  root_six_value : rootSix = S.mul rootTwo rootThree
  common_chord : radius60 = S.mul rootTwo radius90
  center_distance :
    twice S distance =
      S.add (S.mul rootTwo radius90) (S.mul rootThree radius60)

end Soultions.Sharygin.Page24.Problem84.Configuration
