import Sharygin21Problem66.Scalar

/-!
# Rhombus and tangent-circle data for Sharygin, PDF page 21, problem 66

The altitude of the rhombus is `a sin(α)`.  If `k` is the signed displacement of the circle
center from the chord through the two neighboring vertices, tangency gives `R + k = h`.
Eliminating `k` from that relation and the chord equation gives
`4h(2R-h)=a²`, recorded below in its direct geometric form.
-/

namespace Soultions.Sharygin.Page21.Problem66.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) : S.Carrier := S.add x x
def fourTimes (x : S.Carrier) : S.Carrier := twice S (twice S x)
def eightTimes (x : S.Carrier) : S.Carrier := twice S (fourTimes S x)

structure Data where
  side : S.Carrier
  sinAlpha : S.Carrier
  altitude : S.Carrier
  radius : S.Carrier
  side_ne_zero : side ≠ S.zero
  altitude_value : altitude = S.mul side sinAlpha
  tangent_chord_relation :
    S.mul (fourTimes S altitude) (S.sub (twice S radius) altitude) =
      S.square side

end Soultions.Sharygin.Page21.Problem66.Configuration
