import Euclid
import Sharygin12Problem8.Tarski
import Sharygin12Problem8.Scalar
import Sharygin12Problem8.Power

/-!
# Sharygin, PDF page 12, problem 8

> A chord `AB` is drawn through a point `M` situated at distance `a` from the center of a circle
> of radius `R`, where `a < R`. Prove that `|AM| · |MB|` is constant for all such chords and is
> equal to `R² - a²`.
-/

namespace Soultions.Sharygin.Page12.Problem8

open Euclid Plane
open Soultions.Sharygin.Page12.Problem8.Tarski
open Soultions.Sharygin.Page12.Problem8.Power

/-- The intrinsic data of a nondegenerate chord through an interior point. -/
structure Configuration (G : Plane) (circle : Circle G) where
  vertex : G.Point
  firstPoint : G.Point
  secondPoint : G.Point
  vertex_inside : G.InsideCircle circle vertex
  chord_order : G.Bet firstPoint vertex secondPoint
  first_onCircle : G.OnCircle circle firstPoint
  second_onCircle : G.OnCircle circle secondPoint
  intersections_ne : firstPoint ≠ secondPoint

/-- The scalar identity in the wording of problem 8. -/
def Statement (G : Plane) (L : LengthMeasurement G) : Prop :=
  ∀ (circle : Circle G) (config : Configuration G circle),
    L.scalar.mul
        (L.length config.vertex config.firstPoint)
        (L.length config.vertex config.secondPoint) =
      L.scalar.sub
        (L.scalar.square
          (L.length circle.center circle.radiusPoint))
        (L.scalar.square (L.length circle.center config.vertex))

theorem problem8 (G : Plane) (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    [G.Axioms] [M.Axioms] [L.Axioms] :
    Statement G L := by
  intro circle config
  obtain
    ⟨radialLeft, radialRight, hradialLeft, hradialRight,
      hradial_ne, hradial_order, hradial_power⟩ :=
    radial_chord_power_identity G L config.vertex_inside
  calc
    L.scalar.mul
          (L.length config.vertex config.firstPoint)
          (L.length config.vertex config.secondPoint) =
        L.scalar.mul
          (L.length config.vertex radialLeft)
          (L.length config.vertex radialRight) :=
      chord_product_invariant G M L
        config.vertex_inside config.chord_order hradial_order
        config.first_onCircle config.second_onCircle
        hradialLeft hradialRight
        config.intersections_ne hradial_ne
    _ = L.scalar.sub
          (L.scalar.square
            (L.length circle.center circle.radiusPoint))
          (L.scalar.square (L.length circle.center config.vertex)) :=
      hradial_power

end Soultions.Sharygin.Page12.Problem8
