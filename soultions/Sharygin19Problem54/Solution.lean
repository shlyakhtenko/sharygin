import Sharygin19Problem54.Configuration

/-!
# Sharygin, PDF page 19, problem 54

Equal areas put both `M` and `N` one third of the way along their sides.
The proportionality from the similar triangles `AMN` and `ABD` then gives
the requested length after cancelling the nonzero segment `AM`.
-/

namespace Soultions.Sharygin.Page19.Problem54.Solution

open Euclid
open Soultions.Sharygin.Page19.Problem54.Scalar
open Soultions.Sharygin.Page19.Problem54.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem scale_product (x y : S.Carrier) :
    S.mul x (threeTimes S y) = S.mul (threeTimes S x) y := by
  unfold threeTimes twice
  rw [OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib,
    right_distrib S, right_distrib S]

/-- Problem 54: `MN=d/3`, stated as `3 MN=d`. -/
theorem problem54 (data : Data S) :
    threeTimes S data.mn = data.diagonalBD := by
  apply mul_left_cancel S data.am_ne_zero
  calc
    S.mul data.am (threeTimes S data.mn) =
        S.mul (threeTimes S data.am) data.mn :=
      scale_product S _ _
    _ = S.mul data.side data.mn := by rw [data.am_from_equal_areas]
    _ = S.mul data.am data.diagonalBD := data.similar_triangles

end Soultions.Sharygin.Page19.Problem54.Solution
