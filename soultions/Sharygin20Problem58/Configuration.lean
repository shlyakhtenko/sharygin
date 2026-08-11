import Sharygin20Problem58.Scalar

/-!
# Angle data for Sharygin, PDF page 20, problem 58

Because `AH ⟂ BC` and `BH ⟂ AC`, the two given angles are complements
of `B` and `A`, respectively.  The usual triangle angle sum is recorded in
the same undirected angle measure.
-/

namespace Soultions.Sharygin.Page20.Problem58.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

structure Data where
  angleA : S.Carrier
  angleB : S.Carrier
  angleC : S.Carrier
  alpha : S.Carrier
  beta : S.Carrier
  rightAngle : S.Carrier
  straightAngle : S.Carrier
  two_right_angles : S.add rightAngle rightAngle = straightAngle
  triangle_angle_sum :
    S.add angleA (S.add angleB angleC) = straightAngle
  altitude_at_a : S.add alpha angleB = rightAngle
  altitude_at_b : S.add beta angleA = rightAngle

end Soultions.Sharygin.Page20.Problem58.Configuration
