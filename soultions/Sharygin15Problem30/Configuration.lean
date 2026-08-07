import Sharygin15Problem30.Scalar

/-!
# Tangency-distance configuration for Sharygin, page 15, problem 30

A circle tangent to the two rays of an angle has `radius = centerDistance * halfAngleSine`.
Two such circles on the same bisector are externally tangent when the difference of their
center distances is the sum of their radii.  These are geometric meanings of the fields below,
not the requested radius formula.
-/

namespace Soultions.Sharygin.Page15.Problem30.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

/-- One of the two corner circles, paired with the given incircle. -/
structure Candidate (incircleRadius : S.Carrier) where
  halfAngleSine : S.Carrier
  halfAngleSine_nonnegative : S.le S.zero halfAngleSine
  halfAngleSine_le_one : S.le halfAngleSine S.one
  radius : S.Carrier
  incircleCenterDistance : S.Carrier
  candidateCenterDistance : S.Carrier
  incircle_touches_sides :
    S.mul incircleCenterDistance halfAngleSine = incircleRadius
  candidate_touches_sides :
    S.mul candidateCenterDistance halfAngleSine = radius
  external_tangency :
    incircleCenterDistance =
      S.add candidateCenterDistance
        (S.add incircleRadius radius)

/-- The rhombus altitude and the candidates at its acute and obtuse vertices. -/
structure Data where
  altitude : S.Carrier
  incircleRadius : S.Carrier
  incircleRadius_nonnegative : S.le S.zero incircleRadius
  altitude_is_diameter :
    altitude = S.add incircleRadius incircleRadius
  acute : Candidate S incircleRadius
  obtuse : Candidate S incircleRadius
  /-- For an acute angle, `sin(α/2) ≤ cos(α/2)`. -/
  acute_half_sine_le_obtuse_half_sine :
    S.le acute.halfAngleSine obtuse.halfAngleSine

end Soultions.Sharygin.Page15.Problem30.Configuration
