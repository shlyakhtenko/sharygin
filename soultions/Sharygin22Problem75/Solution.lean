import Sharygin22Problem75.Configuration

namespace Soultions.Sharygin.Page22.Problem75.Solution

open Euclid
open Soultions.Sharygin.Page22.Problem75.Scalar
open Soultions.Sharygin.Page22.Problem75.Configuration

variable (S : OrderedScalar) [S.Axioms]

/-- Problem 75: `2Rρ=R²-a²`. -/
theorem problem75 (data : Data S) :
    twice S (S.mul data.givenRadius data.soughtRadius) =
      S.sub (S.square data.givenRadius) (S.square data.centerToA) := by
  apply Eq.symm
  apply sub_eq_of_eq_add S
  exact data.tangent_pythagorean.symm

end Soultions.Sharygin.Page22.Problem75.Solution
