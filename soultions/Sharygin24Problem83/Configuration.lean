import Sharygin24Problem83.Scalar

/-!
# Parallel-chord data for Sharygin, PDF page 24, problem 83

Resolve each endpoint relative to the diameter into the common perpendicular offset `y` and
opposite signed parallel offsets `x`.  The circle and the two endpoint distances then give the
three Pythagorean relations below.
-/

namespace Soultions.Sharygin.Page24.Problem83.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x

structure Data where
  radius : S.Carrier
  centerDistance : S.Carrier
  x : S.Carrier
  y : S.Carrier
  firstDistance : S.Carrier
  secondDistance : S.Carrier
  chord_on_circle : S.add (S.square x) (S.square y) = S.square radius
  first_pythagorean :
    S.square firstDistance =
      S.add (S.square (S.sub x centerDistance)) (S.square y)
  second_pythagorean :
    S.square secondDistance =
      S.add (S.square (S.add x centerDistance)) (S.square y)

end Soultions.Sharygin.Page24.Problem83.Configuration
