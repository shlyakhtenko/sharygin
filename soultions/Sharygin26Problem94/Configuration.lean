import Euclid

/-!
# Intersecting-circle data for Sharygin, PDF page 26, problem 94

The angle `ADB` and its supplement `ADC` have the same sine because `B`, `D`, and `C` lie
on one straight line.  Applying the chord-circumdiameter calculation separately in the two
circles gives `s * 2r = c` and `s * 2R = b`.  These two local equations are recorded without
division so the requested radius relation can be obtained by direct multiplication.
-/

namespace Soultions.Sharygin.Page26.Problem94.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) : S.Carrier :=
  S.add x x

structure Data where
  firstRadius : S.Carrier
  secondRadius : S.Carrier
  sideAB : S.Carrier
  sideAC : S.Carrier
  commonSine : S.Carrier
  first_chord_circumdiameter :
    S.mul commonSine (twice S firstRadius) = sideAB
  second_chord_circumdiameter :
    S.mul commonSine (twice S secondRadius) = sideAC

end Soultions.Sharygin.Page26.Problem94.Configuration
