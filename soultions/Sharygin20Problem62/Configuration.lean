import Sharygin20Problem62.Scalar

/-!
# Annulus data for Sharygin, PDF page 20, problem 62

The two radius points lie on concentric circles.  The larger radius is the
newly defined circumference of the smaller circle, and finite additivity
expresses the larger disk as annulus plus smaller disk.
-/

namespace Soultions.Sharygin.Page20.Problem62.Configuration

open Euclid Plane

universe u v

variable
  (G : Plane)
  (L : LengthMeasurement G)
  (A : AreaMeasurement G L)

structure Data where
  center : G.Point
  smallRadiusPoint : G.Point
  largeRadiusPoint : G.Point
  annulusArea : L.scalar.Carrier
  larger_radius_is_circumference :
    L.length center largeRadiusPoint =
      A.circumference center smallRadiusPoint
  annulus_partition :
    L.scalar.add annulusArea
        (L.scalar.mul A.pi
          (L.scalar.square (L.length center smallRadiusPoint))) =
      L.scalar.mul A.pi
        (L.scalar.square (L.length center largeRadiusPoint))

end Soultions.Sharygin.Page20.Problem62.Configuration
