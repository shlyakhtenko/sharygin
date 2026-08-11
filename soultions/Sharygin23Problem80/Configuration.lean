import Euclid

/-!
# Diagonal data for Sharygin, PDF page 23, problem 80

The opposite triangles `ABK` and `DCK` have equal corresponding inscribed angles and equal
vertical angles.  Applying the repository's geometric multiplication construction to that
local similarity gives `AB * KC = BK * CD`.  The diagonal `AC` is the consecutive sum of
`AK` and `KC`.
-/

namespace Soultions.Sharygin.Page23.Problem80.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

structure Data where
  ab : S.Carrier
  bk : S.Carrier
  ak : S.Carrier
  cd : S.Carrier
  kc : S.Carrier
  ac : S.Carrier
  diagonal_additive : ac = S.add ak kc
  opposite_triangle_proportion : S.mul ab kc = S.mul bk cd

end Soultions.Sharygin.Page23.Problem80.Configuration
