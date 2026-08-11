import Sharygin23Problem82.Configuration

namespace Soultions.Sharygin.Page23.Problem82.Solution

open Euclid
open Soultions.Sharygin.Page23.Problem82.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem twice_mul (x y : S.Carrier) :
    twice S (S.mul x y) = S.mul x (twice S y) := by
  unfold twice
  rw [OrderedScalar.Axioms.left_distrib]

/--
Problem 82: `[BDK] = (a-b) * sqrt(4d^2-(a-b)^2) / 4`, stated without division.
-/
theorem problem82 (data : Data S) :
    fourTimes S data.areaBDK =
      S.mul (S.sub data.lowerBase data.upperBase) data.root := by
  unfold fourTimes
  rw [data.triangle_area, twice_mul S, data.altitude_value,
    data.midpoint_line_location]

end Soultions.Sharygin.Page23.Problem82.Solution
