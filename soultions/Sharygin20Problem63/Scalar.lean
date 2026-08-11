import Euclid

namespace Soultions.Sharygin.Page20.Problem63.Scalar

open Euclid

variable (S : OrderedScalar) [S.Axioms]

theorem neg_add (x : S.Carrier) : S.add (S.neg x) x = S.zero := by
  rw [OrderedScalar.Axioms.add_comm]
  exact OrderedScalar.Axioms.add_neg x

theorem add_left_cancel {x y z : S.Carrier}
    (h : S.add x y = S.add x z) : y = z := by
  have h' := congrArg (fun w => S.add (S.neg x) w) h
  calc
    y = S.add S.zero y := (OrderedScalar.Axioms.zero_add y).symm
    _ = S.add (S.add (S.neg x) x) y := by rw [neg_add S]
    _ = S.add (S.neg x) (S.add x y) := OrderedScalar.Axioms.add_assoc _ _ _
    _ = S.add (S.neg x) (S.add x z) := h'
    _ = S.add (S.add (S.neg x) x) z :=
      (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = S.add S.zero z := by rw [neg_add S]
    _ = z := OrderedScalar.Axioms.zero_add z

theorem mul_left_cancel {x y z : S.Carrier} (hx : x ≠ S.zero)
    (h : S.mul x y = S.mul x z) : y = z := by
  have h' := congrArg (fun w => S.mul (S.inv x) w) h
  calc
    y = S.mul S.one y := (OrderedScalar.Axioms.one_mul y).symm
    _ = S.mul (S.mul (S.inv x) x) y := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv x) x,
        OrderedScalar.Axioms.mul_inv x hx]
    _ = S.mul (S.inv x) (S.mul x y) := OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul (S.inv x) (S.mul x z) := h'
    _ = S.mul (S.mul (S.inv x) x) z :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one z := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv x) x,
        OrderedScalar.Axioms.mul_inv x hx]
    _ = z := OrderedScalar.Axioms.one_mul z

theorem mul_right_cancel {x y z : S.Carrier} (hz : z ≠ S.zero)
    (h : S.mul x z = S.mul y z) : x = y := by
  rw [OrderedScalar.Axioms.mul_comm x z,
    OrderedScalar.Axioms.mul_comm y z] at h
  exact mul_left_cancel S hz h

theorem eq_of_sub_eq_zero {x y : S.Carrier}
    (h : S.sub x y = S.zero) : x = y := by
  change S.add x (S.neg y) = S.zero at h
  have h' := congrArg (fun w => S.add w y) h
  calc
    x = S.add x S.zero := (OrderedScalar.Axioms.add_zero x).symm
    _ = S.add x (S.add (S.neg y) y) := by rw [neg_add S]
    _ = S.add (S.add x (S.neg y)) y :=
      (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = S.add S.zero y := h'
    _ = y := OrderedScalar.Axioms.zero_add y

end Soultions.Sharygin.Page20.Problem63.Scalar
