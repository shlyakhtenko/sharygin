import Euclid

/-!
# Equilateral-triangle division data for Sharygin, PDF page 24, problem 85

Resolving the `2:1` point on `AC` and the `1:2` point on `AB` in the `60°` triangle gives
`KM² = side²/3`.  The center-to-vertex right triangle gives the same squared value for the
circumradius.  The common value is recorded explicitly so the two computations remain distinct.
-/

namespace Soultions.Sharygin.Page24.Problem85.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

structure Data where
  side : S.Carrier
  km : S.Carrier
  circumradius : S.Carrier
  thirdSideSquare : S.Carrier
  division_point_calculation : S.square km = thirdSideSquare
  circumcenter_calculation : S.square circumradius = thirdSideSquare
  positive_sum : S.add km circumradius ≠ S.zero

end Soultions.Sharygin.Page24.Problem85.Configuration
