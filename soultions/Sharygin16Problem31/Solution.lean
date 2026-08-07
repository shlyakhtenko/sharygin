import Sharygin16Problem31.Area

/-!
# Sharygin, PDF page 16, problem 31

The rhombus is cut along a diagonal.  The doubled area of triangle `ABD` is computed first
from the side `AB` and the altitude from `D`, and then from diagonal `BD` and half of diagonal
`AC`.  The geometric-mean hypothesis therefore makes `AD` twice that altitude.  This is the
direct right-triangle characterization of the acute angle as 30 degrees.
-/

namespace Soultions.Sharygin.Page16.Problem31.Solution

open Euclid Plane
open Soultions.Sharygin.Page16.Problem31.Tarski
open Soultions.Sharygin.Page16.Problem31.Scalar
open Soultions.Sharygin.Page16.Problem31.Area

variable (G : Plane) [G.Axioms]

/-- The original rhombus, its two diagonal halves, and the altitude used to read its acute
angle. -/
structure Configuration
    (M : AngleMeasurement G)
    (L : LengthMeasurement G) where
  a : G.Point
  b : G.Point
  c : G.Point
  d : G.Point
  sideAltitude : InteriorAltitude G M a b d
  diagonalAltitude : InteriorAltitude G M b d a
  ac_midpoint : G.Midpoint a diagonalAltitude.foot c
  adjacent_sides_equal : G.Congruent a b a d
  side_is_geometric_mean_of_diagonals :
    L.scalar.square (L.length a d) =
      L.scalar.mul (L.length a c) (L.length b d)

/-- With no numerical real-angle model, an acute angle is 30 degrees precisely when dropping
its perpendicular produces a right triangle whose hypotenuse is twice the opposite leg. -/
def IsThirtyDegree
    (M : AngleMeasurement G)
    (L : LengthMeasurement G)
    (d a b : G.Point) : Prop :=
  ∃ altitude : InteriorAltitude G M a b d,
    L.length a d =
      L.scalar.add
        (L.length altitude.foot d)
        (L.length altitude.foot d)

private theorem mul_left_cancel
    (S : OrderedScalar) [S.Axioms]
    {x y z : S.Carrier}
    (hx : x ≠ S.zero)
    (h : S.mul x y = S.mul x z) :
    y = z := by
  have hinv := congrArg (fun w => S.mul (S.inv x) w) h
  calc
    y = S.mul S.one y := (OrderedScalar.Axioms.one_mul y).symm
    _ = S.mul (S.mul (S.inv x) x) y := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv x) x,
        OrderedScalar.Axioms.mul_inv x hx]
    _ = S.mul (S.inv x) (S.mul x y) :=
      OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul (S.inv x) (S.mul x z) := hinv
    _ = S.mul (S.mul (S.inv x) x) z :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one z := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv x) x,
        OrderedScalar.Axioms.mul_inv x hx]
    _ = z := OrderedScalar.Axioms.one_mul z

private theorem collinear_of_equal_endpoints
    {x y z : G.Point}
    (hxz : x = z) :
    G.Collinear x y z := by
  cases hxz
  exact collinear_swap_last G (collinear_refl_left G x y)

/-- Problem 31: the acute angle of the rhombus is 30 degrees. -/
theorem problem31
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    (A : AreaMeasurement G L)
    [AreaMeasurement.Axioms (G := G) A M]
    (config : Configuration G M L) :
    IsThirtyDegree G M L config.d config.a config.b := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  let side := L.length config.a config.d
  let height := L.length config.sideAltitude.foot config.d
  let halfDiagonal := L.length config.diagonalAltitude.foot config.a

  have hsideLength : L.length config.a config.b = side :=
    (LengthMeasurement.Axioms.congruent_iff _ _ _ _).mp
      config.adjacent_sides_equal
  have hsideArea := triangle_double_area_from_interior_altitude
    G M L A config.sideAltitude
  have hdiagonalArea := triangle_double_area_from_interior_altitude
    G M L A config.diagonalAltitude
  have hareaCyclic :
      A.triangleArea config.a config.b config.d =
        A.triangleArea config.b config.d config.a :=
    AreaMeasurement.Axioms.cyclic M _ _ _
  have hbaseHeight :
      L.scalar.mul side height =
        L.scalar.mul (L.length config.b config.d) halfDiagonal := by
    calc
      L.scalar.mul side height =
          L.scalar.mul
            (L.length config.a config.b)
            (L.length config.sideAltitude.foot config.d) := by
        rw [hsideLength]
      _ = L.scalar.add
          (A.triangleArea config.a config.b config.d)
          (A.triangleArea config.a config.b config.d) := hsideArea.symm
      _ = L.scalar.add
          (A.triangleArea config.b config.d config.a)
          (A.triangleArea config.b config.d config.a) := by rw [hareaCyclic]
      _ = L.scalar.mul
          (L.length config.b config.d)
          (L.length config.diagonalAltitude.foot config.a) := hdiagonalArea

  have hhalfFirst :
      L.length config.a config.diagonalAltitude.foot = halfDiagonal :=
    LengthMeasurement.Axioms.length_symm _ _
  have hhalfSecond :
      L.length config.diagonalAltitude.foot config.c = halfDiagonal := by
    have hcongruent :
        L.length config.a config.diagonalAltitude.foot =
          L.length config.diagonalAltitude.foot config.c :=
      (LengthMeasurement.Axioms.congruent_iff
        config.a config.diagonalAltitude.foot
        config.diagonalAltitude.foot config.c).mp config.ac_midpoint.2
    exact hcongruent.symm.trans hhalfFirst
  have hdiagonalDouble :
      L.length config.a config.c =
        L.scalar.add halfDiagonal halfDiagonal := by
    calc
      L.length config.a config.c =
          L.scalar.add
            (L.length config.a config.diagonalAltitude.foot)
            (L.length config.diagonalAltitude.foot config.c) :=
        LengthMeasurement.Axioms.bet_additive _ _ _ config.ac_midpoint.1
      _ = L.scalar.add halfDiagonal halfDiagonal := by
        rw [hhalfFirst, hhalfSecond]

  have hproduct :
      L.scalar.mul side
          (L.scalar.add height height) =
        L.scalar.mul
          (L.length config.a config.c)
          (L.length config.b config.d) := by
    calc
      L.scalar.mul side (L.scalar.add height height) =
          L.scalar.add
            (L.scalar.mul side height)
            (L.scalar.mul side height) :=
        OrderedScalar.Axioms.left_distrib _ _ _
      _ = L.scalar.add
          (L.scalar.mul (L.length config.b config.d) halfDiagonal)
          (L.scalar.mul (L.length config.b config.d) halfDiagonal) := by
        rw [hbaseHeight]
      _ = L.scalar.add
          (L.scalar.mul halfDiagonal (L.length config.b config.d))
          (L.scalar.mul halfDiagonal (L.length config.b config.d)) := by
        rw [OrderedScalar.Axioms.mul_comm
          (L.length config.b config.d) halfDiagonal]
      _ = L.scalar.mul
          (L.scalar.add halfDiagonal halfDiagonal)
          (L.length config.b config.d) :=
        (right_distrib L.scalar _ _ _).symm
      _ = L.scalar.mul
          (L.length config.a config.c)
          (L.length config.b config.d) := by rw [hdiagonalDouble]

  have hsideNonzero : side ≠ L.scalar.zero := by
    intro hzero
    have had : config.a = config.d :=
      (LengthMeasurement.Axioms.length_eq_zero _ _).mp hzero
    apply config.sideAltitude.left_nondegenerate
    exact collinear_of_equal_endpoints G had.symm
  have hcancel :
      L.scalar.mul side (L.scalar.add height height) =
        L.scalar.mul side side := by
    calc
      L.scalar.mul side (L.scalar.add height height) =
          L.scalar.mul
            (L.length config.a config.c)
            (L.length config.b config.d) := hproduct
      _ = L.scalar.square side :=
        config.side_is_geometric_mean_of_diagonals.symm
      _ = L.scalar.mul side side := rfl
  have htwice : L.scalar.add height height = side :=
    mul_left_cancel L.scalar hsideNonzero hcancel
  exact ⟨config.sideAltitude, htwice.symm⟩

end Soultions.Sharygin.Page16.Problem31.Solution
