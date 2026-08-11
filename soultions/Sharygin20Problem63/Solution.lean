import Sharygin20Problem63.Configuration

/-!
# Sharygin, PDF page 20, problem 63

The completed square has two algebraic roots.  Nonnegativity of geometric
lengths excludes the negative root, leaving `2s+R=√5 R`.
-/

namespace Soultions.Sharygin.Page20.Problem63.Solution

open Euclid
open Soultions.Sharygin.Page20.Problem63.Scalar
open Soultions.Sharygin.Page20.Problem63.Configuration

variable (S : OrderedScalar) [S.Axioms]

/-- Problem 63: `2s+R=√5 R`, equivalently `s=(√5-1)R/2`. -/
theorem problem63 (data : Data S) :
    S.add (twice S data.side) data.radius =
      S.mul data.rootFive data.radius := by
  apply eq_of_sub_eq_zero S
  apply mul_right_cancel S data.geometric_root
  calc
    S.mul
        (S.sub (S.add (twice S data.side) data.radius)
          (S.mul data.rootFive data.radius))
        (S.add (S.add (twice S data.side) data.radius)
          (S.mul data.rootFive data.radius)) = S.zero :=
      data.completed_square_factor
    _ = S.mul S.zero
        (S.add (S.add (twice S data.side) data.radius)
          (S.mul data.rootFive data.radius)) :=
      (OrderedScalar.Axioms.zero_mul _).symm

end Soultions.Sharygin.Page20.Problem63.Solution
