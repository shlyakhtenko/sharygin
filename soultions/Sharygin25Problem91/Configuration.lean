import Euclid

/-!
# Circle-angle data for Sharygin, PDF page 25, problem 91

The two intersections of the line `BC` with the circle centered at `B` are endpoints of a
diameter.  The equal radii `BA` and `BK` give the central arc cut off by the original angles;
the two remaining triangle angles are half of the complementary central arcs.
-/

namespace Soultions.Sharygin.Page25.Problem91.Configuration

open Euclid
variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x

structure Data where
  alpha : S.Carrier
  beta : S.Carrier
  halfTurn : S.Carrier
  angleE : S.Carrier
  angleK : S.Carrier
  angleF : S.Carrier
  centralKE : S.Carrier
  centralKF : S.Carrier
  diameter_arcs : S.add centralKE centralKF = halfTurn
  isosceles_central_arc : centralKF = S.add (twice S alpha) beta
  inscribed_at_E : twice S angleE = centralKF
  inscribed_at_F : twice S angleF = centralKE
  diameter_inscribed_angle : twice S angleK = halfTurn

end Soultions.Sharygin.Page25.Problem91.Configuration
