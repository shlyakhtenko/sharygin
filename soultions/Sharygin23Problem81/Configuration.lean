import Euclid

/-!
# Cyclic-trapezoid data for Sharygin, PDF page 23, problem 81

The two bases are chords of angular parameters `alpha + beta` and `alpha - beta`.
Adding their locally expanded chord lengths gives `4 R sin(alpha) cos(beta)`.  The altitude
is `2 R sin(alpha) sin(beta)`.  These two geometric computations are recorded separately from
the trapezoid-area and circle-area definitions.
-/

namespace Soultions.Sharygin.Page23.Problem81.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def angleFactor (sinAlpha sinBeta cosBeta : S.Carrier) :=
  S.mul (S.square sinAlpha) (S.mul sinBeta cosBeta)

structure Data where
  radius : S.Carrier
  pi : S.Carrier
  sinAlpha : S.Carrier
  sinBeta : S.Carrier
  cosBeta : S.Carrier
  baseSum : S.Carrier
  height : S.Carrier
  circleArea : S.Carrier
  trapezoidArea : S.Carrier
  base_sum_value :
    baseSum = fourTimes S (S.mul radius (S.mul sinAlpha cosBeta))
  height_value :
    height = twice S (S.mul radius (S.mul sinAlpha sinBeta))
  trapezoid_area :
    twice S trapezoidArea = S.mul baseSum height
  circle_area :
    circleArea = S.mul pi (S.square radius)

end Soultions.Sharygin.Page23.Problem81.Configuration
