import Sharygin13Problem17.Bisector

/-!
# Trigonometric output data for Sharygin, PDF page 13, problem 17

The repository defines cosine from an explicit right-triangle realization.  Accordingly, the
solution constructs such a realization and proves that its angle doubles to the angle of the
given triangle.  No auxiliary parallel, similarity, or scalar identity is stored here.
-/

namespace Soultions.Sharygin.Page13.Problem17.Construction

open Euclid Plane
open Soultions.Sharygin.Page13.Problem17.Bisector

variable (G : Plane)

/-- A right-triangle realization of half of the angle at `triangle.a`. -/
structure HalfAngleCosineData
    (M : AngleMeasurement G)
    (triangle : InteriorConfiguration G)
    (sense : RotationSense) where
  angle : DirectedAngle G
  realization : Trigonometry.RightTriangleRealization G M angle
  doubles_to_source :
    M.twice (M.measure angle) =
      M.measure ⟨triangle.b, triangle.a, triangle.c, sense⟩

/-- The cosine supplied by the constructed half-angle right triangle. -/
def HalfAngleCosineData.cosine
    (L : LengthMeasurement G)
    {M : AngleMeasurement G}
    {triangle : InteriorConfiguration G}
    {sense : RotationSense}
    (data : HalfAngleCosineData G M triangle sense) :
    L.scalar.Carrier :=
  Trigonometry.cos G L data.realization

end Soultions.Sharygin.Page13.Problem17.Construction
