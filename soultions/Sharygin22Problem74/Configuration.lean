import Euclid

/-!
# Circumcircle angle-bisector data for Sharygin, PDF page 22, problem 74

The bisector endpoint `K` is the midpoint of the arc `BC` not containing `A`.  The two chord
computations are `a=2R sin(α+β)` and `AK=2R cos((α-β)/2)`.
-/

namespace Soultions.Sharygin.Page22.Problem74.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x

structure Data where
  sideBC : S.Carrier
  circumradius : S.Carrier
  sinAngleSum : S.Carrier
  cosHalfDifference : S.Carrier
  ak : S.Carrier
  base_chord :
    S.mul (twice S circumradius) sinAngleSum = sideBC
  bisector_chord :
    ak = S.mul (twice S circumradius) cosHalfDifference

end Soultions.Sharygin.Page22.Problem74.Configuration
