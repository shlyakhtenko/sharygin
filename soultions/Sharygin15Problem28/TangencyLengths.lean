import Sharygin15Problem28.RightTriangle
import Sharygin15Problem28.Tangent

/-!
# Tangency lengths for problem 28

Equal tangent segments are derived by applying the already proved right-triangle square
identity to the two radius/contact triangles and then using nonnegative square injectivity.
-/

namespace Soultions.Sharygin.Page15.Problem28.TangencyLengths

open Euclid Plane
open Soultions.Sharygin.Page15.Problem28.Tarski
open Soultions.Sharygin.Page15.Problem28.Midpoint
open Soultions.Sharygin.Page15.Problem28.Affine
open Soultions.Sharygin.Page15.Problem28.Scalar
open Soultions.Sharygin.Page15.Problem28.RightTriangle
open Soultions.Sharygin.Page15.Problem28.Tangent

variable (G : Plane) [G.Axioms]

/-- Tangent segments from one point to one circle have equal scalar lengths. -/
theorem equal_tangent_lengths
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {circle : Circle G}
    {u uThrough w wThrough x : G.Point}
    (hu : G.TangentAt circle u uThrough)
    (hw : G.TangentAt circle w wThrough)
    (hxu : G.Collinear u uThrough x)
    (hxw : G.Collinear w wThrough x) :
    L.length x u = L.length x w := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  obtain ⟨uOpp, huuOpp⟩ :=
    pointReflection_exists G u uThrough
  obtain ⟨wOpp, hwwOpp⟩ :=
    pointReflection_exists G w wThrough
  have huEqual :
      G.Congruent circle.center uThrough
        circle.center uOpp :=
    tangent_symmetric_equidistant G hu huuOpp
  have hwEqual :
      G.Congruent circle.center wThrough
        circle.center wOpp :=
    tangent_symmetric_equidistant G hw hwwOpp
  have huOff :
      ¬G.Collinear uThrough u circle.center := by
    intro h
    exact tangent_center_off_line G hu
      (collinear_cyclic G h)
  have hwOff :
      ¬G.Collinear wThrough w circle.center := by
    intro h
    exact tangent_center_off_line G hw
      (collinear_cyclic G h)
  have hxuLine :
      G.Collinear uThrough u x :=
    collinear_swap G hxu
  have hxwLine :
      G.Collinear wThrough w x :=
    collinear_swap G hxw
  have hpythU :=
    pythagorean_on_projection_line
      G M L huuOpp huEqual huOff hxuLine
  have hpythW :=
    pythagorean_on_projection_line
      G M L hwwOpp hwEqual hwOff hxwLine
  have hcenterRadius :
      L.length u circle.center =
        L.length w circle.center := by
    calc
      L.length u circle.center =
          L.length circle.center u :=
        LengthMeasurement.Axioms.length_symm _ _
      _ = L.length circle.center circle.radiusPoint :=
        (LengthMeasurement.Axioms.congruent_iff
          circle.center u
          circle.center circle.radiusPoint).mp
          hu.2.1
      _ = L.length circle.center w :=
        ((LengthMeasurement.Axioms.congruent_iff
          circle.center w
          circle.center circle.radiusPoint).mp
          hw.2.1).symm
      _ = L.length w circle.center :=
        LengthMeasurement.Axioms.length_symm _ _
  have hhypotenuse :
      L.length x circle.center =
        L.length x circle.center := rfl
  have hsquares :
      L.scalar.square (L.length u x) =
        L.scalar.square (L.length w x) := by
    apply add_right_cancel L.scalar
      (x := L.scalar.square
        (L.length u circle.center))
    calc
      L.scalar.add
          (L.scalar.square (L.length u x))
          (L.scalar.square (L.length u circle.center)) =
        L.scalar.square (L.length x circle.center) :=
          hpythU
      _ = L.scalar.square (L.length x circle.center) :=
          congrArg L.scalar.square hhypotenuse
      _ =
        L.scalar.add
          (L.scalar.square (L.length w x))
          (L.scalar.square (L.length w circle.center)) :=
          hpythW.symm
      _ =
        L.scalar.add
          (L.scalar.square (L.length w x))
          (L.scalar.square (L.length u circle.center)) := by
          rw [hcenterRadius]
  have hlength :
      L.length u x = L.length w x :=
    square_injective_nonnegative L.scalar
      (LengthMeasurement.Axioms.length_nonnegative u x)
      (LengthMeasurement.Axioms.length_nonnegative w x)
      hsquares
  calc
    L.length x u = L.length u x :=
      LengthMeasurement.Axioms.length_symm _ _
    _ = L.length w x := hlength
    _ = L.length x w :=
      LengthMeasurement.Axioms.length_symm _ _

end Soultions.Sharygin.Page15.Problem28.TangencyLengths
