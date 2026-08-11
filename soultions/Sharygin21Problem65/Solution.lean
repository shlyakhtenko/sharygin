import Sharygin21Problem65.Configuration

/-!
# Sharygin, PDF page 21, problem 65

The first perpendicular bisector gives `4y=a`; in the scaled coordinates this is `y₄=a`.
The second gives `x₄+y₄=6a`.  Hence `x₄=5a`, so the center is
`(5a/4,a/4)` relative to vertex `A` and the two side directions.
-/

namespace Soultions.Sharygin.Page21.Problem65.Solution

open Euclid
open Soultions.Sharygin.Page21.Problem65.Scalar
open Soultions.Sharygin.Page21.Problem65.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem center_y (data : Data S) :
    data.centerY4 = data.side := by
  exact mul_left_cancel S data.four_side_ne_zero data.midpoint_squareCenter_bisector

private theorem coordinate_sum (data : Data S) :
    S.add data.centerX4 data.centerY4 = sixTimes S data.side := by
  exact mul_left_cancel S data.four_side_ne_zero data.squareCenter_vertex_bisector

/-- Problem 65: the circle center is `(5a/4,a/4)` in side coordinates based at `A`. -/
theorem problem65 (data : Data S) :
    data.centerX4 = fiveTimes S data.side ∧
      data.centerY4 = data.side := by
  have hy := center_y S data
  refine ⟨?_, hy⟩
  apply add_right_cancel S (z := data.side)
  calc
    S.add data.centerX4 data.side =
        S.add data.centerX4 data.centerY4 := by rw [hy]
    _ = sixTimes S data.side := coordinate_sum S data
    _ = S.add (fiveTimes S data.side) data.side := rfl

end Soultions.Sharygin.Page21.Problem65.Solution
