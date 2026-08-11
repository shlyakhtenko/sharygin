import Sharygin22Problem75.Scalar

/-!
# Internally tangent circle data for Sharygin, PDF page 22, problem 75

The new center is at perpendicular distance `ρ` from the diameter at `A`, while its horizontal
offset from the given center is `a`.  Squaring the internal-tangency relation and cancelling
`ρ²` gives `a²+2Rρ=R²`.
-/

namespace Soultions.Sharygin.Page22.Problem75.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x

structure Data where
  givenRadius : S.Carrier
  centerToA : S.Carrier
  soughtRadius : S.Carrier
  tangent_pythagorean :
    S.add (S.square centerToA)
        (twice S (S.mul givenRadius soughtRadius)) =
      S.square givenRadius

end Soultions.Sharygin.Page22.Problem75.Configuration
