import Euclid

/-! Problem-local subtraction algebra for Sharygin, PDF page 22, problem 75. -/

namespace Soultions.Sharygin.Page22.Problem75.Scalar

open Euclid

variable (S : OrderedScalar) [S.Axioms]

theorem sub_eq_of_eq_add {d r x : S.Carrier} (h : d = S.add r x) :
    S.sub d r = x := by
  change S.add d (S.neg r) = x
  rw [h, OrderedScalar.Axioms.add_comm r x,
    OrderedScalar.Axioms.add_assoc, OrderedScalar.Axioms.add_neg,
    OrderedScalar.Axioms.add_zero]

end Soultions.Sharygin.Page22.Problem75.Scalar
