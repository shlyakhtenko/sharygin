import Sharygin19Problem53.Configuration

/-!
# Sharygin, PDF page 19, problem 53

The centres are the midpoints of `DB` and `DC`, hence their distance is
`BC/2`.  Pythagoras in the right triangle `DBC` finishes the calculation.
-/

namespace Soultions.Sharygin.Page19.Problem53.Solution

open Euclid
open Soultions.Sharygin.Page19.Problem53.Scalar
open Soultions.Sharygin.Page19.Problem53.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem square_twice (x : S.Carrier) :
    S.square (twice S x) = fourTimes S (S.square x) := by
  unfold OrderedScalar.square twice fourTimes
  rw [right_distrib S, OrderedScalar.Axioms.left_distrib]
  rfl

private theorem bc_square (data : Data S) :
    S.square data.bc =
      S.sub (S.square data.dc) (S.square data.db) := by
  apply eq_sub_of_add_eq S
  calc
    S.add (S.square data.bc) (S.square data.db) =
        S.add (S.square data.db) (S.square data.bc) :=
      OrderedScalar.Axioms.add_comm _ _
    _ = S.square data.dc := data.right_triangle_pythagoras

/-- Problem 53: `4d² = b²-a²`. -/
theorem problem53 (data : Data S) :
    fourTimes S (S.square data.centerDistance) =
      S.sub (S.square data.dc) (S.square data.db) := by
  calc
    fourTimes S (S.square data.centerDistance) =
        S.square (twice S data.centerDistance) :=
      (square_twice S data.centerDistance).symm
    _ = S.square data.bc := by rw [data.midpoint_segment]
    _ = S.sub (S.square data.dc) (S.square data.db) := bc_square S data

end Soultions.Sharygin.Page19.Problem53.Solution
