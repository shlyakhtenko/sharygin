import Sharygin22Problem71.Configuration

namespace Soultions.Sharygin.Page22.Problem71.Solution

open Euclid
open Soultions.Sharygin.Page22.Problem71.Scalar
open Soultions.Sharygin.Page22.Problem71.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem side_split (data : Data S) :
    twice S data.sideParameter = S.sub S.one data.sideParameter := by
  apply add_right_cancel S (z := data.sideParameter)
  calc
    S.add (twice S data.sideParameter) data.sideParameter = S.one := by
      simpa only [data.c_coefficient] using data.b_coefficient
    _ = S.add (S.sub S.one data.sideParameter) data.sideParameter := by
      unfold OrderedScalar.sub
      rw [OrderedScalar.Axioms.add_assoc, neg_add S,
        OrderedScalar.Axioms.add_zero]

/-- Problem 71: the line divides `BC` in the ratio `BF:FC=1:2`. -/
theorem problem71 (data : Data S) :
    twice S data.bf = data.fc := by
  rw [data.bf_value, data.fc_value]
  calc
    twice S (S.mul data.sideParameter data.bc) =
      S.mul (twice S data.sideParameter) data.bc := by
        unfold twice
        rw [right_distrib S]
    _ = S.mul (S.sub S.one data.sideParameter) data.bc := by
      rw [side_split S data]

end Soultions.Sharygin.Page22.Problem71.Solution
