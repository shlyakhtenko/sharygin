import Sharygin14Problem22.Area
import Sharygin14Problem22.TriangleArea
import Sharygin14Problem22.ThirtyDegree
import Sharygin14Problem22.RightTriangle

/-!
# Solution of Sharygin, PDF page 14, problem 22

The answer is given without square-root primitives by the exact pair
`4 * leg² = 3 * c²` and `2 * pi * r² = 3 * c * leg`.  These equations determine the
positive radius and are equivalent to the usual nested-radical expression.
-/

namespace Soultions.Sharygin.Page14.Problem22.Solution

open Euclid Plane
open Soultions.Sharygin.Page14.Problem22.Tarski
open Soultions.Sharygin.Page14.Problem22.Scalar
open Soultions.Sharygin.Page14.Problem22.Similarity
open Soultions.Sharygin.Page14.Problem22.Pythagorean
open Soultions.Sharygin.Page14.Problem22.RightTriangle
open Soultions.Sharygin.Page14.Problem22.Area
open Soultions.Sharygin.Page14.Problem22.TriangleArea
open Soultions.Sharygin.Page14.Problem22.ThirtyDegree

variable {G : Plane} {L : LengthMeasurement G}

private theorem four_long_leg_squares_eq_three_hypotenuse_squares
    (S : OrderedScalar) [S.Axioms]
    {long short hypotenuse : S.Carrier}
    (hdouble : hypotenuse = S.add short short)
    (hpythagorean :
      S.add (S.square long) (S.square short) = S.square hypotenuse) :
    S.nsmul 4 (S.square long) = S.nsmul 3 (S.square hypotenuse) := by
  have hhypotenuse :
      S.square hypotenuse = S.nsmul 4 (S.square short) := by
    rw [hdouble, square_double S]
    simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add,
      OrderedScalar.Axioms.add_assoc]
  have hlong :
      S.square long = S.nsmul 3 (S.square short) := by
    apply add_right_cancel S (x := S.square short)
    calc
      S.add (S.square long) (S.square short) = S.square hypotenuse := hpythagorean
      _ = S.nsmul 4 (S.square short) := hhypotenuse
      _ = S.add (S.nsmul 3 (S.square short)) (S.square short) := by rfl
  rw [hlong, hhypotenuse]
  simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add,
    OrderedScalar.Axioms.add_comm, add_left_comm S]

private theorem doubled_disk_area_eq_three_hypotenuse_long_leg_products
    (S : OrderedScalar) [S.Axioms]
    {diskArea triangleArea hypotenuse long short : S.Carrier}
    (hdisk : diskArea = S.nsmul 6 triangleArea)
    (htriangle : S.add triangleArea triangleArea = S.mul long short)
    (hdouble : hypotenuse = S.add short short) :
    S.nsmul 2 diskArea = S.nsmul 3 (S.mul hypotenuse long) := by
  rw [hdisk]
  have hshortLong : S.mul short long = S.add triangleArea triangleArea := by
    rw [OrderedScalar.Axioms.mul_comm]
    exact htriangle.symm
  have hproduct :
      S.mul hypotenuse long =
        S.add (S.add triangleArea triangleArea)
          (S.add triangleArea triangleArea) := by
    rw [hdouble, right_distrib S, hshortLong]
  rw [hproduct]
  simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.zero_add,
    OrderedScalar.Axioms.add_comm, add_left_comm S]

/-- Complete geometric data for the circle which bisects the given triangle. -/
structure Configuration
    (M : AngleMeasurement G)
    (A : AreaMeasurement G L) where
  triangle : ThirtyDegree.Configuration G M
  radiusPoint : G.Point
  sectors : TwelveSectorPartition A triangle.a radiusPoint
  selected_sector :
    sectors.s0 =
      Plane.Region.inter (G := G)
        (G.TriangleRegion triangle.a triangle.b triangle.c)
        (L.ClosedDisk triangle.a radiusPoint)
  circle_bisects_triangle :
    L.scalar.add (A.area sectors.s0) (A.area sectors.s0) =
      A.triangleArea triangle.a triangle.b triangle.c

/--
Sharygin, PDF page 14, problem 22.

The first equality is the 30-60-90 metric relation.  The second is the requested radius
equation, stated without square roots or division.
-/
theorem problem22
    (G : Plane) [G.Axioms]
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L) [AreaMeasurement.Axioms A M]
    (config : Configuration M A) :
    L.scalar.nsmul 4
        (L.scalar.square (L.length config.triangle.a config.triangle.b)) =
      L.scalar.nsmul 3
        (L.scalar.square (L.length config.triangle.a config.triangle.c)) ∧
    L.scalar.nsmul 2
        (L.scalar.mul A.pi
          (L.scalar.square
            (L.length config.triangle.a config.radiusPoint))) =
      L.scalar.nsmul 3
        (L.scalar.mul
          (L.length config.triangle.a config.triangle.c)
          (L.length config.triangle.a config.triangle.b)) := by
  letI : OrderedScalar.Axioms L.scalar := LengthMeasurement.Axioms.scalar_axioms
  have hdouble :
      L.length config.triangle.a config.triangle.c =
        L.scalar.add
          (L.length config.triangle.b config.triangle.c)
          (L.length config.triangle.b config.triangle.c) :=
    hypotenuse_eq_twice_opposite G M L config.triangle
  have hab : config.triangle.a ≠ config.triangle.b := by
    intro h
    apply config.triangle.abc_noncollinear
    rw [h]
    exact collinear_refl_left G config.triangle.b config.triangle.c
  have hcb : config.triangle.c ≠ config.triangle.b := by
    intro h
    apply config.triangle.abc_noncollinear
    rw [h]
    exact collinear_refl_right G config.triangle.a config.triangle.b
  have hac_ad :
      G.Congruent config.triangle.a config.triangle.c
        config.triangle.a config.triangle.reflectedC := by
    exact triangle_sas_third_side G hab hcb
      (congruent_refl G config.triangle.b config.triangle.a)
      (congruent_symm G config.triangle.c_reflects_in_b.radius)
      config.triangle.right_symmetric
  have hpythagorean :
      L.scalar.add
          (L.scalar.square (L.length config.triangle.b config.triangle.c))
          (L.scalar.square (L.length config.triangle.b config.triangle.a)) =
        L.scalar.square (L.length config.triangle.c config.triangle.a) :=
    pythagorean_of_isosceles_midpoint_right G M L
      config.triangle.c_reflects_in_b hac_ad
      (fun h =>
        config.triangle.abc_noncollinear
          (collinear_rotate_left G (collinear_swap G h)))
  have hpythagorean' :
      L.scalar.add
          (L.scalar.square (L.length config.triangle.a config.triangle.b))
          (L.scalar.square (L.length config.triangle.b config.triangle.c)) =
        L.scalar.square (L.length config.triangle.a config.triangle.c) := by
    rw [← LengthMeasurement.Axioms.length_symm config.triangle.b config.triangle.a,
      ← LengthMeasurement.Axioms.length_symm config.triangle.c config.triangle.a,
      OrderedScalar.Axioms.add_comm]
    exact hpythagorean
  have hleg :=
    four_long_leg_squares_eq_three_hypotenuse_squares L.scalar
      hdouble hpythagorean'
  refine ⟨hleg, ?_⟩
  have hdiskSix :
      A.area (L.ClosedDisk config.triangle.a config.radiusPoint) =
        L.scalar.nsmul 6
          (A.triangleArea config.triangle.a config.triangle.b config.triangle.c) :=
    disk_area_eq_six_triangle_areas M A config.sectors config.circle_bisects_triangle
  have hdiskFormula :
      A.area (L.ClosedDisk config.triangle.a config.radiusPoint) =
        L.scalar.mul A.pi
          (L.scalar.square (L.length config.triangle.a config.radiusPoint)) :=
    AreaMeasurement.Axioms.disk_area M config.triangle.a config.radiusPoint
  have hdoubleTriangle :
      L.scalar.add
          (A.triangleArea config.triangle.a config.triangle.b config.triangle.c)
          (A.triangleArea config.triangle.a config.triangle.b config.triangle.c) =
        L.scalar.mul
          (L.length config.triangle.a config.triangle.b)
          (L.length config.triangle.b config.triangle.c) :=
    right_triangle_double_area G M L A config.triangle.abc_noncollinear
      config.triangle.sense config.triangle.right_measure
  apply doubled_disk_area_eq_three_hypotenuse_long_leg_products L.scalar
    (diskArea := L.scalar.mul A.pi
      (L.scalar.square (L.length config.triangle.a config.radiusPoint)))
    (triangleArea := A.triangleArea config.triangle.a config.triangle.b config.triangle.c)
    (hypotenuse := L.length config.triangle.a config.triangle.c)
    (long := L.length config.triangle.a config.triangle.b)
    (short := L.length config.triangle.b config.triangle.c)
  · exact hdiskFormula.symm.trans hdiskSix
  · exact hdoubleTriangle
  · exact hdouble

end Soultions.Sharygin.Page14.Problem22.Solution
