import Sharygin13Problem13.Area
import Sharygin13Problem13.Tangent

/-!
# Circumscribed-polygon area for Sharygin, page 13, problem 13

The polygon is triangulated from the circle center.  Every side triangle has the common radius
as its altitude because the side is tangent.
-/

namespace Soultions.Sharygin.Page13.Problem13.Polygon

open Euclid Plane
open Soultions.Sharygin.Page13.Problem13.Tarski
open Soultions.Sharygin.Page13.Problem13.Affine
open Soultions.Sharygin.Page13.Problem13.Area
open Soultions.Sharygin.Page13.Problem13.Tangent

variable (G : Plane) [G.Axioms]

/-- One side of a polygon circumscribed about `circle`, with its contact point recorded. -/
structure TangentialSide (circle : Circle G) where
  start : G.Point
  finish : G.Point
  contact : G.Point
  through : G.Point
  start_ne_finish : start ≠ finish
  tangent : G.TangentAt circle contact through
  start_on_tangent : G.Collinear contact through start
  finish_on_tangent : G.Collinear contact through finish

/-- A tangential side and the circle center form a nondegenerate triangle. -/
theorem TangentialSide.center_start_finish_nondegenerate
    {circle : Circle G}
    (side : TangentialSide G circle) :
    ¬G.Collinear circle.center side.start side.finish := by
  intro hcenter
  have hstartFinishContact :
      G.Collinear side.start side.finish side.contact :=
    collinear_three_on_line G side.tangent.1
      side.start_on_tangent
      side.finish_on_tangent
      (collinear_cyclic G
        (collinear_refl_left G side.contact side.through))
  have hstartFinishThrough :
      G.Collinear side.start side.finish side.through :=
    collinear_three_on_line G side.tangent.1
      side.start_on_tangent
      side.finish_on_tangent
      (collinear_refl_right G side.contact side.through)
  have hstartFinishCenter :
      G.Collinear side.start side.finish circle.center :=
    collinear_cyclic G hcenter
  have hcontactThroughCenter :
      G.Collinear side.contact side.through circle.center :=
    collinear_three_on_line G side.start_ne_finish
      hstartFinishContact
      hstartFinishThrough
      hstartFinishCenter
  exact tangent_center_off_line G side.tangent
    (collinear_swap_last G hcontactThroughCenter)

/-- The double area of one tangential side triangle is side length times radius. -/
theorem tangential_side_double_area
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {circle : Circle G}
    (side : TangentialSide G circle)
    (sense : RotationSense) :
    L.scalar.add
        (A.triangleArea circle.center side.start side.finish)
        (A.triangleArea circle.center side.start side.finish) =
      L.scalar.mul
        (L.length side.start side.finish)
        (L.length circle.center circle.radiusPoint) := by
  obtain ⟨opposite, hreflection⟩ :=
    pointReflection_exists G side.contact side.through
  have hequidistant :
      G.Congruent circle.center side.through
        circle.center opposite :=
    tangent_symmetric_equidistant G
      side.tangent hreflection
  have hoff :
      ¬G.Collinear side.through side.contact circle.center := by
    intro h
    exact tangent_center_off_line G side.tangent
      (collinear_cyclic G h)
  let altitude :
      AltitudePair G side.start side.finish circle.center := {
    foot := side.contact
    left := side.through
    right := opposite
    reflected := hreflection
    apex_equidistant := hequidistant
    apex_off_base := hoff
    a_on_base := collinear_swap G side.start_on_tangent
    b_on_base := collinear_swap G side.finish_on_tangent
  }
  have hnoncollinear :
      ¬G.Collinear side.start side.finish circle.center := by
    intro h
    exact TangentialSide.center_start_finish_nondegenerate
      (G := G) side (collinear_rotate_left G h)
  have harea :=
    triangle_double_area_base_height_all
      G M L A altitude
      hnoncollinear
      sense
  have hheight :
      L.length side.contact circle.center =
        L.length circle.center circle.radiusPoint := by
    calc
      L.length side.contact circle.center =
          L.length circle.center side.contact :=
        LengthMeasurement.Axioms.length_symm
          side.contact circle.center
      _ = L.length circle.center circle.radiusPoint :=
        (LengthMeasurement.Axioms.congruent_iff
          circle.center side.contact
          circle.center circle.radiusPoint).mp
          side.tangent.2.1
  rw [hheight] at harea
  rw [AreaMeasurement.Axioms.cyclic
    M circle.center side.start side.finish]
  exact harea

/-- Area of the polygon as the sum of the center-to-side fan triangles. -/
def fanArea
    (A : AreaMeasurement G L)
    {circle : Circle G} :
    List (TangentialSide G circle) →
      L.scalar.Carrier
  | [] => L.scalar.zero
  | side :: sides =>
      L.scalar.add
        (A.triangleArea circle.center side.start side.finish)
        (fanArea A sides)

/-- Perimeter as the sum of side lengths. -/
def perimeter
    (L : LengthMeasurement G)
    {circle : Circle G} :
    List (TangentialSide G circle) →
      L.scalar.Carrier
  | [] => L.scalar.zero
  | side :: sides =>
      L.scalar.add
        (L.length side.start side.finish)
        (perimeter L sides)

/--
Twice the area of a circumscribed polygon equals radius times perimeter, equivalently
`area = radius * semiperimeter`.
-/
theorem circumscribed_polygon_double_area
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {circle : Circle G}
    (sides : List (TangentialSide G circle))
    (sense : RotationSense) :
    L.scalar.add
        (fanArea (G := G) A sides)
        (fanArea (G := G) A sides) =
      L.scalar.mul
        (L.length circle.center circle.radiusPoint)
        (perimeter (G := G) L sides) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  induction sides with
  | nil =>
      change
        L.scalar.add L.scalar.zero L.scalar.zero =
          L.scalar.mul
            (L.length circle.center circle.radiusPoint)
            L.scalar.zero
      rw [OrderedScalar.Axioms.add_zero,
        Soultions.Sharygin.Page13.Problem13.Scalar.mul_zero]
  | cons side sides ih =>
      change
        L.scalar.add
            (L.scalar.add
              (A.triangleArea
                circle.center side.start side.finish)
              (fanArea (G := G) A sides))
            (L.scalar.add
              (A.triangleArea
                circle.center side.start side.finish)
              (fanArea (G := G) A sides)) =
          L.scalar.mul
            (L.length circle.center circle.radiusPoint)
            (L.scalar.add
              (L.length side.start side.finish)
              (perimeter (G := G) L sides))
      have hside :=
        tangential_side_double_area
          G M L A side sense
      calc
        L.scalar.add
              (L.scalar.add
                (A.triangleArea
                  circle.center side.start side.finish)
                (fanArea (G := G) A sides))
              (L.scalar.add
                (A.triangleArea
                  circle.center side.start side.finish)
                (fanArea (G := G) A sides)) =
            L.scalar.add
              (L.scalar.add
                (A.triangleArea
                  circle.center side.start side.finish)
                (A.triangleArea
                  circle.center side.start side.finish))
              (L.scalar.add
                (fanArea (G := G) A sides)
                (fanArea (G := G) A sides)) := by
          simp only [OrderedScalar.Axioms.add_assoc,
            OrderedScalar.Axioms.add_comm,
            Soultions.Sharygin.Page13.Problem13.Scalar.add_left_comm
              L.scalar]
        _ = L.scalar.add
              (L.scalar.mul
                (L.length side.start side.finish)
                (L.length circle.center circle.radiusPoint))
              (L.scalar.mul
                (L.length circle.center circle.radiusPoint)
                (perimeter (G := G) L sides)) := by
          rw [hside, ih]
        _ = L.scalar.add
              (L.scalar.mul
                (L.length circle.center circle.radiusPoint)
                (L.length side.start side.finish))
              (L.scalar.mul
                (L.length circle.center circle.radiusPoint)
                (perimeter (G := G) L sides)) := by
          rw [OrderedScalar.Axioms.mul_comm
            (L.length side.start side.finish)
            (L.length circle.center circle.radiusPoint)]
        _ = L.scalar.mul
              (L.length circle.center circle.radiusPoint)
              (L.scalar.add
                (L.length side.start side.finish)
                (perimeter (G := G) L sides)) :=
          (OrderedScalar.Axioms.left_distrib _ _ _).symm

end Soultions.Sharygin.Page13.Problem13.Polygon
