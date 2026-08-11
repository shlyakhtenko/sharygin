import Sharygin23Problem77.Configuration

namespace Soultions.Sharygin.Page23.Problem77.Solution

open Euclid
open Soultions.Sharygin.Page23.Problem77.Scalar
open Soultions.Sharygin.Page23.Problem77.Configuration

variable (S : OrderedScalar) [S.Axioms]

/-- Problem 77: `(4√3-6)R=a`. -/
theorem problem77 (data : Data S) :
    S.mul
        (S.sub (fourTimes S data.rootThree) (sixTimes S S.one))
        data.radius =
      data.givenDifference := by
  rw [← data.perimeter_difference, data.inscribed_value,
    data.circumscribed_value]
  unfold OrderedScalar.sub
  rw [right_distrib S, neg_mul S]

end Soultions.Sharygin.Page23.Problem77.Solution
