import Euclid

/-! Problem-local scalar cancellation for Sharygin, PDF page 21, problem 69. -/

namespace Soultions.Sharygin.Page21.Problem69.Scalar

open Euclid

variable (S : OrderedScalar) [S.Axioms]

theorem mul_left_cancel {x y z : S.Carrier} (hx : x ≠ S.zero)
    (h : S.mul x y = S.mul x z) : y = z := by
  have h' := congrArg (fun w => S.mul (S.inv x) w) h
  calc
    y = S.mul S.one y := (OrderedScalar.Axioms.one_mul y).symm
    _ = S.mul (S.mul (S.inv x) x) y := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv x) x, OrderedScalar.Axioms.mul_inv x hx]
    _ = S.mul (S.inv x) (S.mul x y) := OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul (S.inv x) (S.mul x z) := h'
    _ = S.mul (S.mul (S.inv x) x) z := (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one z := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv x) x, OrderedScalar.Axioms.mul_inv x hx]
    _ = z := OrderedScalar.Axioms.one_mul z

end Soultions.Sharygin.Page21.Problem69.Scalar
