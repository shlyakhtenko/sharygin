import Sharygin25Problem91.Configuration

namespace Soultions.Sharygin.Page25.Problem91.Solution

open Euclid
open Soultions.Sharygin.Page25.Problem91.Configuration

variable (S : OrderedScalar)

/--
Problem 91: `K` is right, `E = alpha + beta/2`, and
`F = 90° - alpha - beta/2`, all stated without division.
-/
theorem problem91 (data : Data S) :
    twice S data.angleK = data.halfTurn ∧
      twice S data.angleE = S.add (twice S data.alpha) data.beta ∧
      S.add (twice S data.angleF) (S.add (twice S data.alpha) data.beta) =
        data.halfTurn := by
  refine ⟨data.diameter_inscribed_angle, ?_, ?_⟩
  · rw [data.inscribed_at_E, data.isosceles_central_arc]
  · rw [data.inscribed_at_F]
    exact (congrArg (S.add data.centralKE)
      data.isosceles_central_arc).symm.trans data.diameter_arcs

end Soultions.Sharygin.Page25.Problem91.Solution
