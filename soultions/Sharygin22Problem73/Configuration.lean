import Euclid

/-!
# Isosceles-triangle data for Sharygin, PDF page 22, problem 73

For the selected right-triangle realizations of the obtuse apex angle, the extended sine rule
gives `a=2R sin(α)`.  Computing the orthocenter and circumcenter on the symmetry axis gives
`OH=R(1-2 cos(α))`; the sign is fixed by `α>90°`.
-/

namespace Soultions.Sharygin.Page22.Problem73.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x

structure Data where
  base : S.Carrier
  sinAlpha : S.Carrier
  cosAlpha : S.Carrier
  circumradius : S.Carrier
  centerDistance : S.Carrier
  base_circumradius :
    S.mul (twice S sinAlpha) circumradius = base
  axis_center_distance :
    centerDistance =
      S.mul circumradius (S.sub S.one (twice S cosAlpha))

end Soultions.Sharygin.Page22.Problem73.Configuration
