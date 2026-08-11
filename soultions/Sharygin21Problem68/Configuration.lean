import Sharygin21Problem68.Scalar

/-!
# Tangent-circle data for Sharygin, PDF page 21, problem 68

Put the original tangency point at the origin and the original center on the perpendicular axis.
The new circle center lies on the same axis.  Internal tangency puts its signed center coordinate
at `2r-ρ`; Pythagoras for either half-chord of length `a` gives the displayed equation.
-/

namespace Soultions.Sharygin.Page21.Problem68.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) : S.Carrier := S.add x x
def fourTimes (x : S.Carrier) : S.Carrier := twice S (twice S x)

structure Data where
  givenRadius : S.Carrier
  halfChord : S.Carrier
  soughtRadius : S.Carrier
  tangent_circle_equation :
    S.square soughtRadius =
      S.add (S.square halfChord)
        (S.square (S.sub (twice S givenRadius) soughtRadius))

end Soultions.Sharygin.Page21.Problem68.Configuration
