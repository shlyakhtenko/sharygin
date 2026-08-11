import Euclid

/-! Problem-local scalar algebra for Sharygin, PDF page 21, problem 68. -/

namespace Soultions.Sharygin.Page21.Problem68.Scalar

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
    _ = S.add (S.add (S.neg x) x) z := (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = S.add S.zero z := by rw [neg_add S]
    _ = z := OrderedScalar.Axioms.zero_add z

theorem neg_unique {x y : S.Carrier}
    (h : S.add x y = S.zero) : y = S.neg x := by
  apply add_left_cancel S (x := x)
  rw [h]
  exact (OrderedScalar.Axioms.add_neg x).symm

theorem neg_sum (x y : S.Carrier) :
    S.neg (S.add x y) = S.add (S.neg x) (S.neg y) := by
  apply Eq.symm
  apply neg_unique S
  rw [OrderedScalar.Axioms.add_assoc]
  rw [← OrderedScalar.Axioms.add_assoc y (S.neg x) (S.neg y)]
  rw [OrderedScalar.Axioms.add_comm y (S.neg x)]
  rw [OrderedScalar.Axioms.add_assoc (S.neg x) y (S.neg y)]
  rw [OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.add_zero,
    OrderedScalar.Axioms.add_neg]

theorem neg_neg (x : S.Carrier) : S.neg (S.neg x) = x := by
  apply Eq.symm
  apply neg_unique S
  exact neg_add S x

theorem cancel_pair (x z : S.Carrier) :
    S.add (S.neg x) (S.add x z) = z := by
  rw [← OrderedScalar.Axioms.add_assoc, neg_add S,
    OrderedScalar.Axioms.zero_add]

theorem mul_zero (x : S.Carrier) : S.mul x S.zero = S.zero := by
  rw [OrderedScalar.Axioms.mul_comm]
  exact OrderedScalar.Axioms.zero_mul x

theorem right_distrib (x y z : S.Carrier) :
    S.mul (S.add x y) z = S.add (S.mul x z) (S.mul y z) := by
  rw [OrderedScalar.Axioms.mul_comm (S.add x y) z, OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.mul_comm z x, OrderedScalar.Axioms.mul_comm z y]

theorem mul_neg (x y : S.Carrier) : S.mul x (S.neg y) = S.neg (S.mul x y) := by
  apply add_left_cancel S (x := S.mul x y)
  calc
    S.add (S.mul x y) (S.mul x (S.neg y)) = S.mul x (S.add y (S.neg y)) :=
      (OrderedScalar.Axioms.left_distrib _ _ _).symm
    _ = S.mul x S.zero := by rw [OrderedScalar.Axioms.add_neg]
    _ = S.zero := mul_zero S x
    _ = S.add (S.mul x y) (S.neg (S.mul x y)) :=
      (OrderedScalar.Axioms.add_neg _).symm

theorem neg_mul (x y : S.Carrier) : S.mul (S.neg x) y = S.neg (S.mul x y) := by
  rw [OrderedScalar.Axioms.mul_comm (S.neg x) y, mul_neg S,
    OrderedScalar.Axioms.mul_comm y x]

end Soultions.Sharygin.Page21.Problem68.Scalar
