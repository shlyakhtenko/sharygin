import Sharygin25Problem89.Configuration

namespace Soultions.Sharygin.Page25.Problem89.Solution

open Euclid
open Soultions.Sharygin.Page25.Problem89.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem neg_add (x : S.Carrier) : S.add (S.neg x) x = S.zero := by
  rw [OrderedScalar.Axioms.add_comm]
  exact OrderedScalar.Axioms.add_neg x

private theorem eq_of_sub_eq_zero {x y : S.Carrier} (h : S.sub x y = S.zero) : x = y := by
  change S.add x (S.neg y) = S.zero at h
  have h' := congrArg (fun w => S.add w y) h
  calc
    x = S.add x S.zero := (OrderedScalar.Axioms.add_zero x).symm
    _ = S.add x (S.add (S.neg y) y) := by rw [neg_add S]
    _ = S.add (S.add x (S.neg y)) y := (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = S.add S.zero y := h'
    _ = y := OrderedScalar.Axioms.zero_add y

private theorem mul_right_cancel {x y z : S.Carrier} (hz : z ≠ S.zero)
    (h : S.mul x z = S.mul y z) : x = y := by
  have h' : S.mul z x = S.mul z y := by
    rw [OrderedScalar.Axioms.mul_comm z x, OrderedScalar.Axioms.mul_comm z y]
    exact h
  have hi := congrArg (S.mul (S.inv z)) h'
  calc
    x = S.mul S.one x := (OrderedScalar.Axioms.one_mul x).symm
    _ = S.mul (S.mul (S.inv z) z) x := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv z) z, OrderedScalar.Axioms.mul_inv z hz]
    _ = S.mul (S.inv z) (S.mul z x) := OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul (S.inv z) (S.mul z y) := hi
    _ = S.mul (S.mul (S.inv z) z) y := (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one y := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv z) z, OrderedScalar.Axioms.mul_inv z hz]
    _ = y := OrderedScalar.Axioms.one_mul y

/-- Problem 89: the cosine of either base angle is `2/3`, stated without division. -/
theorem problem89 (data : Data S) :
    threeTimes S data.cosBaseAngle = twice S S.one := by
  apply eq_of_sub_eq_zero S
  apply mul_right_cancel S data.positive_branch
  rw [data.orthocenter_incidence, OrderedScalar.Axioms.zero_mul]

end Soultions.Sharygin.Page25.Problem89.Solution
