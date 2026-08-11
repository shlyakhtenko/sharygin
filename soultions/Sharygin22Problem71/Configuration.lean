import Sharygin22Problem71.Scalar

/-!
# Median-bisector coordinates for Sharygin, PDF page 22, problem 71

Use `A` as affine origin.  Four times the midpoint of median `BD` has coefficients `2B+C`.
Equating the coefficients of its line from `A` with a point `(1-s)B+sC` on `BC` gives the two
relations below.  The lengths on `BC` are then `s·BC` and `(1-s)·BC`.
-/

namespace Soultions.Sharygin.Page22.Problem71.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x

structure Data where
  bc : S.Carrier
  lineParameter : S.Carrier
  sideParameter : S.Carrier
  bf : S.Carrier
  fc : S.Carrier
  c_coefficient : lineParameter = sideParameter
  b_coefficient :
    S.add (twice S lineParameter) sideParameter = S.one
  bf_value : bf = S.mul sideParameter bc
  fc_value : fc = S.mul (S.sub S.one sideParameter) bc

end Soultions.Sharygin.Page22.Problem71.Configuration
