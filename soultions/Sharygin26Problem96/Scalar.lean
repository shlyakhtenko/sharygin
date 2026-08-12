import Euclid

/-! Problem-local scalar algebra for Sharygin, PDF page 26, problem 96. -/

namespace Soultions.Sharygin.Page26.Problem96.Scalar

open Euclid
variable (S : OrderedScalar) [S.Axioms]

theorem neg_add (x : S.Carrier) : S.add (S.neg x) x = S.zero := by
  rw [OrderedScalar.Axioms.add_comm]
  exact OrderedScalar.Axioms.add_neg x

theorem add_left_cancel {x y z : S.Carrier} (h : S.add x y = S.add x z) : y = z := by
  have h' := congrArg (fun w => S.add (S.neg x) w) h
  calc
    y = S.add S.zero y := (OrderedScalar.Axioms.zero_add y).symm
    _ = S.add (S.add (S.neg x) x) y := by rw [neg_add S]
    _ = S.add (S.neg x) (S.add x y) := OrderedScalar.Axioms.add_assoc _ _ _
    _ = S.add (S.neg x) (S.add x z) := h'
    _ = S.add (S.add (S.neg x) x) z := (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = S.add S.zero z := by rw [neg_add S]
    _ = z := OrderedScalar.Axioms.zero_add z

theorem sub_eq_of_eq_add {d r x : S.Carrier} (h : d = S.add r x) : S.sub d r = x := by
  change S.add d (S.neg r) = x
  rw [h, OrderedScalar.Axioms.add_comm r x, OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.add_zero]

theorem right_distrib (x y z : S.Carrier) :
    S.mul (S.add x y) z = S.add (S.mul x z) (S.mul y z) := by
  rw [OrderedScalar.Axioms.mul_comm (S.add x y) z,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.mul_comm z x,
    OrderedScalar.Axioms.mul_comm z y]

theorem mul_zero (x : S.Carrier) : S.mul x S.zero = S.zero := by
  rw [OrderedScalar.Axioms.mul_comm]
  exact OrderedScalar.Axioms.zero_mul x

theorem neg_unique {x y : S.Carrier} (h : S.add x y = S.zero) : y = S.neg x := by
  apply add_left_cancel S (x := x)
  rw [h]
  exact (OrderedScalar.Axioms.add_neg x).symm

theorem neg_mul (x y : S.Carrier) : S.mul (S.neg x) y = S.neg (S.mul x y) := by
  apply neg_unique S
  calc
    S.add (S.mul x y) (S.mul (S.neg x) y) =
        S.mul (S.add x (S.neg x)) y := (right_distrib S _ _ _).symm
    _ = S.mul S.zero y := by rw [OrderedScalar.Axioms.add_neg]
    _ = S.zero := OrderedScalar.Axioms.zero_mul y

theorem sub_mul (x y z : S.Carrier) :
    S.mul (S.sub x y) z = S.sub (S.mul x z) (S.mul y z) := by
  unfold OrderedScalar.sub
  rw [right_distrib S, neg_mul S]

end Soultions.Sharygin.Page26.Problem96.Scalar
