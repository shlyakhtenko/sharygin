import Euclid

/-! Problem-local scalar algebra for Sharygin, PDF page 24, problem 83. -/

namespace Soultions.Sharygin.Page24.Problem83.Scalar

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

theorem neg_unique {x y : S.Carrier} (h : S.add x y = S.zero) : y = S.neg x := by
  apply add_left_cancel S (x := x)
  rw [h]
  exact (OrderedScalar.Axioms.add_neg x).symm

theorem mul_zero (x : S.Carrier) : S.mul x S.zero = S.zero := by
  rw [OrderedScalar.Axioms.mul_comm]
  exact OrderedScalar.Axioms.zero_mul x

theorem right_distrib (x y z : S.Carrier) :
    S.mul (S.add x y) z = S.add (S.mul x z) (S.mul y z) := by
  rw [OrderedScalar.Axioms.mul_comm (S.add x y) z,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.mul_comm z x,
    OrderedScalar.Axioms.mul_comm z y]

theorem mul_neg (x y : S.Carrier) : S.mul x (S.neg y) = S.neg (S.mul x y) := by
  apply neg_unique S
  calc
    S.add (S.mul x y) (S.mul x (S.neg y)) = S.mul x (S.add y (S.neg y)) :=
      (OrderedScalar.Axioms.left_distrib _ _ _).symm
    _ = S.mul x S.zero := by rw [OrderedScalar.Axioms.add_neg]
    _ = S.zero := mul_zero S x

theorem neg_mul (x y : S.Carrier) : S.mul (S.neg x) y = S.neg (S.mul x y) := by
  rw [OrderedScalar.Axioms.mul_comm (S.neg x) y, mul_neg S,
    OrderedScalar.Axioms.mul_comm y x]

theorem neg_neg (x : S.Carrier) : S.neg (S.neg x) = x := by
  apply add_left_cancel S (x := S.neg x)
  rw [OrderedScalar.Axioms.add_neg, neg_add S]

theorem add_left_comm (x y z : S.Carrier) :
    S.add x (S.add y z) = S.add y (S.add x z) := by
  rw [← OrderedScalar.Axioms.add_assoc, OrderedScalar.Axioms.add_comm x y,
    OrderedScalar.Axioms.add_assoc]

/-- The sum of the squares of `x+y` and `x-y`. -/
theorem square_add_add_square_sub (x y : S.Carrier) :
    S.add (S.square (S.add x y)) (S.square (S.sub x y)) =
      S.add (S.add (S.square x) (S.square y))
        (S.add (S.square x) (S.square y)) := by
  change
    S.add
        (S.mul (S.add x y) (S.add x y))
        (S.mul (S.add x (S.neg y)) (S.add x (S.neg y))) =
      S.add (S.add (S.mul x x) (S.mul y y))
        (S.add (S.mul x x) (S.mul y y))
  rw [right_distrib S, right_distrib S,
    OrderedScalar.Axioms.left_distrib, OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib, OrderedScalar.Axioms.left_distrib,
    mul_neg S, neg_mul S, mul_neg S, neg_mul S,
    OrderedScalar.Axioms.mul_comm y x, neg_neg S]
  calc
    S.add
          (S.add (S.add (S.mul x x) (S.mul x y))
            (S.add (S.mul x y) (S.mul y y)))
          (S.add (S.add (S.mul x x) (S.neg (S.mul x y)))
            (S.add (S.neg (S.mul x y)) (S.mul y y))) =
        S.add
          (S.add (S.add (S.mul x x) (S.mul y y))
            (S.add (S.mul x x) (S.mul y y)))
          (S.add (S.add (S.mul x y) (S.neg (S.mul x y)))
            (S.add (S.mul x y) (S.neg (S.mul x y)))) := by
      simp only [OrderedScalar.Axioms.add_assoc, OrderedScalar.Axioms.add_comm,
        add_left_comm S]
    _ = S.add (S.add (S.mul x x) (S.mul y y))
          (S.add (S.mul x x) (S.mul y y)) := by
      rw [OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.zero_add,
        OrderedScalar.Axioms.add_zero]

end Soultions.Sharygin.Page24.Problem83.Scalar
