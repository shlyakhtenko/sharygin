import Sharygin19Problem56.Scalar

/-!
# Axis data for Sharygin, PDF page 19, problem 56

The tangent triangle is symmetric about `AO`.  The chord-of-contact offset
comes from the similar tangent right triangles; the inradius equation comes
from writing the triangle area as inradius times semiperimeter.
-/

namespace Soultions.Sharygin.Page19.Problem56.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

structure Data where
  radius : S.Carrier
  ao : S.Carrier
  contactOffset : S.Carrier
  triangleInradius : S.Carrier
  oi : S.Carrier
  ao_ne_zero : ao ≠ S.zero
  contact_similarity :
    S.mul ao contactOffset = S.square radius
  inradius_from_area :
    S.mul ao triangleInradius =
      S.mul radius (S.sub ao radius)
  axis_addition : oi = S.add contactOffset triangleInradius

end Soultions.Sharygin.Page19.Problem56.Configuration
