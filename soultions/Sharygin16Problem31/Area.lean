import Sharygin16Problem31.Scalar
import Sharygin16Problem31.TriangleArea

/-!
# Interior-altitude area calculation for Sharygin, PDF page 16, problem 31

The base-times-height identity used below is derived by cutting at the perpendicular foot and
applying the problem-local right-triangle area theorem to the two pieces.
-/

namespace Soultions.Sharygin.Page16.Problem31.Area

open Euclid Plane
open Soultions.Sharygin.Page16.Problem31.Tarski
open Soultions.Sharygin.Page16.Problem31.Scalar
open Soultions.Sharygin.Page16.Problem31.TriangleArea

variable (G : Plane) [G.Axioms]

/-- A perpendicular from `c` whose foot lies between the endpoints of the base `ab`. -/
structure InteriorAltitude
    (M : AngleMeasurement G)
    (a b c : G.Point) where
  foot : G.Point
  sense : RotationSense
  between : G.Bet a foot b
  left_nondegenerate : ¬G.Collinear c foot a
  right_nondegenerate : ¬G.Collinear c foot b
  left_right :
    M.twice (M.measure ⟨c, foot, a, sense⟩) = M.halfTurn
  right_right :
    M.twice (M.measure ⟨c, foot, b, sense⟩) = M.halfTurn

/-- Twice a triangle's area is its base times the corresponding interior altitude. -/
theorem triangle_double_area_from_interior_altitude
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    {a b c : G.Point}
    (altitude : InteriorAltitude G M a b c) :
    L.scalar.add
        (A.triangleArea a b c)
        (A.triangleArea a b c) =
      L.scalar.mul
        (L.length a b)
        (L.length altitude.foot c) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  have hcut := AreaMeasurement.Axioms.cut_additive
    (A := A) M c a b altitude.foot altitude.between
  have hareaCyclic :
      A.triangleArea c a b = A.triangleArea a b c :=
    AreaMeasurement.Axioms.cyclic M c a b
  have hleft := right_triangle_double_area
    G M L A altitude.left_nondegenerate altitude.sense altitude.left_right
  have hright := right_triangle_double_area
    G M L A altitude.right_nondegenerate altitude.sense altitude.right_right
  have hbase :
      L.length a b =
        L.scalar.add
          (L.length a altitude.foot)
          (L.length altitude.foot b) :=
    LengthMeasurement.Axioms.bet_additive
      a altitude.foot b altitude.between
  have hleftOrder :
      A.triangleArea c a altitude.foot =
        A.triangleArea c altitude.foot a := by
    calc
      A.triangleArea c a altitude.foot =
          A.triangleArea a c altitude.foot :=
        AreaMeasurement.Axioms.swap M _ _ _
      _ = A.triangleArea c altitude.foot a :=
        AreaMeasurement.Axioms.cyclic M _ _ _
  calc
    L.scalar.add
        (A.triangleArea a b c)
        (A.triangleArea a b c) =
      L.scalar.add
        (A.triangleArea c a b)
        (A.triangleArea c a b) := by rw [hareaCyclic]
    _ = L.scalar.add
        (L.scalar.add
          (A.triangleArea c a altitude.foot)
          (A.triangleArea c a altitude.foot))
        (L.scalar.add
          (A.triangleArea c altitude.foot b)
          (A.triangleArea c altitude.foot b)) := by
      rw [hcut]
      simp only [OrderedScalar.Axioms.add_comm,
        add_left_comm L.scalar]
    _ = L.scalar.add
        (L.scalar.mul
          (L.length c altitude.foot)
          (L.length altitude.foot a))
        (L.scalar.mul
          (L.length c altitude.foot)
          (L.length altitude.foot b)) := by
      rw [hleftOrder, hleft, hright]
    _ = L.scalar.mul
        (L.length c altitude.foot)
        (L.scalar.add
          (L.length altitude.foot a)
          (L.length altitude.foot b)) :=
      (OrderedScalar.Axioms.left_distrib _ _ _).symm
    _ = L.scalar.mul
        (L.length c altitude.foot)
        (L.length a b) := by
      rw [LengthMeasurement.Axioms.length_symm altitude.foot a,
        ← hbase]
    _ = L.scalar.mul
        (L.length a b)
        (L.length altitude.foot c) := by
      rw [LengthMeasurement.Axioms.length_symm c altitude.foot,
        OrderedScalar.Axioms.mul_comm]

end Soultions.Sharygin.Page16.Problem31.Area
