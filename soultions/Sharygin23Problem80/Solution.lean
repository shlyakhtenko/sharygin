import Sharygin23Problem80.Configuration

namespace Soultions.Sharygin.Page23.Problem80.Solution

open Euclid
open Soultions.Sharygin.Page23.Problem80.Configuration

variable (S : OrderedScalar) [S.Axioms]

/-- Problem 80: if `AB=a`, `BK=b`, `AK=c`, and `CD=d`, then `a * AC = a*c + b*d`. -/
theorem problem80 (data : Data S) :
    S.mul data.ab data.ac =
      S.add (S.mul data.ab data.ak) (S.mul data.bk data.cd) := by
  rw [data.diagonal_additive, OrderedScalar.Axioms.left_distrib,
    data.opposite_triangle_proportion]

end Soultions.Sharygin.Page23.Problem80.Solution
