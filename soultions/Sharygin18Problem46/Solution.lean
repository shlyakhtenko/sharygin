import Sharygin18Problem46.Configuration

/-!
# Sharygin, PDF page 18, problem 46

Doubling the angle sum in triangle `AOC` gives `A + 2∠AOC + C = 0`.  The angle sum in
`ABC` gives `A+B+C=180°`, so `A+(180°+B)+C=0` as well.  Cancellation yields
`2∠AOC=180°+B`, equivalently `∠AOC=90°+B/2`.
-/

namespace Soultions.Sharygin.Page18.Problem46.Solution

open Euclid Plane
open Soultions.Sharygin.Page18.Problem46.Configuration

variable {G : Plane} (M : AngleMeasurement G) [M.Axioms]

private theorem neg_add (x : M.Measure) :
    M.add (M.neg x) x = M.zero := by
  rw [AngleMeasurement.Axioms.add_comm]
  exact AngleMeasurement.Axioms.add_neg x

private theorem add_left_cancel {x y z : M.Measure}
    (h : M.add x y = M.add x z) : y = z := by
  have h' := congrArg (fun w => M.add (M.neg x) w) h
  calc
    y = M.add M.zero y := (AngleMeasurement.Axioms.zero_add y).symm
    _ = M.add (M.add (M.neg x) x) y := by rw [neg_add M]
    _ = M.add (M.neg x) (M.add x y) :=
      AngleMeasurement.Axioms.add_assoc _ _ _
    _ = M.add (M.neg x) (M.add x z) := h'
    _ = M.add (M.add (M.neg x) x) z :=
      (AngleMeasurement.Axioms.add_assoc _ _ _).symm
    _ = M.add M.zero z := by rw [neg_add M]
    _ = z := AngleMeasurement.Axioms.zero_add z

private theorem add_right_cancel {x y z : M.Measure}
    (h : M.add y x = M.add z x) : y = z := by
  apply add_left_cancel M (x := x)
  rw [AngleMeasurement.Axioms.add_comm x y,
    AngleMeasurement.Axioms.add_comm x z]
  exact h

private theorem add_left_comm (x y z : M.Measure) :
    M.add x (M.add y z) = M.add y (M.add x z) := by
  rw [← AngleMeasurement.Axioms.add_assoc,
    AngleMeasurement.Axioms.add_comm x y,
    AngleMeasurement.Axioms.add_assoc]

private theorem twice_add (x y : M.Measure) :
    M.twice (M.add x y) = M.add (M.twice x) (M.twice y) := by
  change
    M.add (M.add x y) (M.add x y) =
      M.add (M.add x x) (M.add y y)
  simp only [AngleMeasurement.Axioms.add_comm, add_left_comm M]

private theorem doubled_incenter_sum (data : Data M) :
    M.add (M.add data.angleA (M.twice data.angleAOC)) data.angleC = M.zero := by
  have h := congrArg M.twice data.incenter_triangle_sum
  rw [twice_add M, twice_add M,
    data.a_bisected, data.c_bisected,
    AngleMeasurement.Axioms.twice_halfTurn] at h
  exact h

private theorem candidate_sum (data : Data M) :
    M.add
        (M.add data.angleA (M.add M.halfTurn data.angleB))
        data.angleC = M.zero := by
  calc
    M.add
        (M.add data.angleA (M.add M.halfTurn data.angleB))
        data.angleC =
      M.add M.halfTurn
        (M.add (M.add data.angleA data.angleB) data.angleC) := by
      simp only [AngleMeasurement.Axioms.add_comm, add_left_comm M]
    _ = M.add M.halfTurn M.halfTurn := by rw [data.triangle_sum]
    _ = M.twice M.halfTurn := rfl
    _ = M.zero := AngleMeasurement.Axioms.twice_halfTurn

private theorem sandwich_cancel
    {a c x y : M.Measure}
    (h : M.add (M.add a x) c = M.add (M.add a y) c) : x = y := by
  have hleft : M.add a x = M.add a y := add_right_cancel M h
  exact add_left_cancel M hleft

/-- Problem 46: `2∠AOC=180°+α`, the division-free form of `∠AOC=90°+α/2`. -/
theorem problem46 (data : Data M) :
    M.twice data.angleAOC = M.add M.halfTurn data.angleB := by
  apply sandwich_cancel M
  exact (doubled_incenter_sum M data).trans (candidate_sum M data).symm

end Soultions.Sharygin.Page18.Problem46.Solution
