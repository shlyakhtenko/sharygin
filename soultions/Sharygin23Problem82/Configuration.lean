import Euclid

/-!
# Isosceles-trapezoid data for Sharygin, PDF page 23, problem 82

Writing `delta = AD - BC`, the midpoint construction on `AC` gives `DK = delta`.
Dropping the altitude from `B` and applying the local Pythagorean calculation gives
`2 * height = sqrt(4 d^2 - delta^2)`.  The triangle-area relation is kept as a separate
finite-additivity consequence.
-/

namespace Soultions.Sharygin.Page23.Problem82.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def fourTimes (x : S.Carrier) := twice S (twice S x)

structure Data where
  lowerBase : S.Carrier
  upperBase : S.Carrier
  leg : S.Carrier
  dk : S.Carrier
  height : S.Carrier
  root : S.Carrier
  areaBDK : S.Carrier
  midpoint_line_location : dk = S.sub lowerBase upperBase
  altitude_value : twice S height = root
  root_square :
    S.square root =
      S.sub (fourTimes S (S.square leg))
        (S.square (S.sub lowerBase upperBase))
  triangle_area : twice S areaBDK = S.mul dk height

end Soultions.Sharygin.Page23.Problem82.Configuration
