import Sharygin22Problem73.Configuration

/-!
# Sharygin, PDF page 22, problem 73

Eliminate the circumradius between `a=2R sin(α)` and
`OH=R(1-2 cos(α))`.
-/

namespace Soultions.Sharygin.Page22.Problem73.Solution

open Euclid
open Soultions.Sharygin.Page22.Problem73.Configuration

variable (S : OrderedScalar) [S.Axioms]

/-- Problem 73: `2 sin(α)·OH=a(1-2 cos(α))`. -/
theorem problem73 (data : Data S) :
    S.mul (twice S data.sinAlpha) data.centerDistance =
      S.mul data.base (S.sub S.one (twice S data.cosAlpha)) := by
  rw [data.axis_center_distance]
  calc
    S.mul (twice S data.sinAlpha)
        (S.mul data.circumradius
          (S.sub S.one (twice S data.cosAlpha))) =
      S.mul
        (S.mul (twice S data.sinAlpha) data.circumradius)
        (S.sub S.one (twice S data.cosAlpha)) :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul data.base (S.sub S.one (twice S data.cosAlpha)) := by
      rw [data.base_circumradius]

end Soultions.Sharygin.Page22.Problem73.Solution
