import Euclid

/-!
# Half-arc data for Sharygin, PDF page 23, problem 79

For the cyclic quadrilateral `ABCD`, record only the three half-arc
contributions used by the two given inscribed angles, the angle between
the diagonals, and the requested inscribed angle.  These relations are
kept local to this problem.
-/

namespace Soultions.Sharygin.Page23.Problem79.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x

structure Data where
  alpha : S.Carrier
  beta : S.Carrier
  gamma : S.Carrier
  acd : S.Carrier
  halfArcBC : S.Carrier
  halfArcCD : S.Carrier
  halfArcDA : S.Carrier
  alpha_value : alpha = S.add halfArcCD halfArcBC
  beta_value : beta = S.add halfArcDA halfArcCD
  gamma_value : gamma = S.add halfArcBC halfArcDA
  acd_value : acd = halfArcDA

end Soultions.Sharygin.Page23.Problem79.Configuration
