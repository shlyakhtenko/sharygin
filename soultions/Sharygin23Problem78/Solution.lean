import Sharygin23Problem78.Configuration

namespace Soultions.Sharygin.Page23.Problem78.Solution

open Euclid
open Soultions.Sharygin.Page23.Problem78.Configuration

variable (S : OrderedScalar)

/-- Problem 78: the cut-off area is `√3 a²/12`. -/
theorem problem78 (data : Data S) :
    twelveTimes S data.cutArea =
      S.mul data.rootThree (S.square data.side) := by
  unfold twelveTimes
  rw [data.cut_area_third, data.equilateral_area]

end Soultions.Sharygin.Page23.Problem78.Solution
