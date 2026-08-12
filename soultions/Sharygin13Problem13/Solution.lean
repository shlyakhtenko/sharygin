import Euclid
import Sharygin13Problem13.Polygon

/-!
# Sharygin, PDF page 13, problem 13

> Prove that the area of a polygon circumscribed about a circle is equal to the product of
> the radius of the circle and the semiperimeter of the polygon.

The conclusion is stated without division as `2 · area = radius · perimeter`.  Rectangle area
is the primitive normalization; the right-triangle area formula used for each side triangle is
derived in this problem's local `Area` file.
-/

namespace Soultions.Sharygin.Page13.Problem13

open Euclid Plane
open Soultions.Sharygin.Page13.Problem13.Polygon

def Statement
    (G : Plane)
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L) : Prop :=
  ∀ {circle : Circle G}
      (polygon : CircumscribedPolygon G circle)
      (disjoint : FanDisjoint (G := G) A polygon.sides)
      (sense : RotationSense),
    L.scalar.add
        (A.area (fanRegion (G := G) polygon.sides))
        (A.area (fanRegion (G := G) polygon.sides)) =
      L.scalar.mul
        (L.length circle.center circle.radiusPoint)
        (perimeter (G := G) L polygon.sides)

theorem problem13
    (G : Plane)
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    (A : AreaMeasurement G L)
    [G.Axioms] [M.Axioms] [L.Axioms]
    [AreaMeasurement.Axioms (G := G) A M] :
    Statement G M L A := by
  intro circle polygon disjoint sense
  exact circumscribed_polygon_double_area
    G M L A polygon disjoint sense

end Soultions.Sharygin.Page13.Problem13
