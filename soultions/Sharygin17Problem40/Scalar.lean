import Euclid

/-!
# Scalar identities for Sharygin, PDF page 17, problem 40

Only the ring identities used in this problem's direction calculation are
derived here.
-/

namespace Soultions.Sharygin.Page17.Problem40.Scalar

open Euclid

variable (S : OrderedScalar) [S.Axioms]

theorem neg_add (x : S.Carrier) :
    S.add (S.neg x) x = S.zero := by
  rw [OrderedScalar.Axioms.add_comm]
  exact OrderedScalar.Axioms.add_neg x

theorem add_left_cancel {x y z : S.Carrier}
    (h : S.add x y = S.add x z) :
    y = z := by
  have h' := congrArg (fun w => S.add (S.neg x) w) h
  calc
    y = S.add S.zero y := (OrderedScalar.Axioms.zero_add y).symm
    _ = S.add (S.add (S.neg x) x) y := by rw [neg_add S]
    _ = S.add (S.neg x) (S.add x y) :=
      OrderedScalar.Axioms.add_assoc _ _ _
    _ = S.add (S.neg x) (S.add x z) := h'
    _ = S.add (S.add (S.neg x) x) z :=
      (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = S.add S.zero z := by rw [neg_add S]
    _ = z := OrderedScalar.Axioms.zero_add z

theorem neg_unique {x y : S.Carrier}
    (h : S.add x y = S.zero) :
    y = S.neg x := by
  apply add_left_cancel S (x := x)
  rw [h]
  exact (OrderedScalar.Axioms.add_neg x).symm

theorem mul_zero (x : S.Carrier) :
    S.mul x S.zero = S.zero := by
  rw [OrderedScalar.Axioms.mul_comm]
  exact OrderedScalar.Axioms.zero_mul x

theorem right_distrib (x y z : S.Carrier) :
    S.mul (S.add x y) z =
      S.add (S.mul x z) (S.mul y z) := by
  rw [OrderedScalar.Axioms.mul_comm (S.add x y) z,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.mul_comm z x,
    OrderedScalar.Axioms.mul_comm z y]

theorem mul_neg (x y : S.Carrier) :
    S.mul x (S.neg y) = S.neg (S.mul x y) := by
  apply neg_unique S
  calc
    S.add (S.mul x y) (S.mul x (S.neg y)) =
        S.mul x (S.add y (S.neg y)) :=
      (OrderedScalar.Axioms.left_distrib _ _ _).symm
    _ = S.mul x S.zero := by rw [OrderedScalar.Axioms.add_neg]
    _ = S.zero := mul_zero S x

theorem neg_mul (x y : S.Carrier) :
    S.mul (S.neg x) y = S.neg (S.mul x y) := by
  rw [OrderedScalar.Axioms.mul_comm (S.neg x) y,
    mul_neg S, OrderedScalar.Axioms.mul_comm y x]

theorem neg_neg (x : S.Carrier) :
    S.neg (S.neg x) = x := by
  apply add_left_cancel S (x := S.neg x)
  rw [OrderedScalar.Axioms.add_neg, neg_add S]

theorem neg_zero :
    S.neg S.zero = S.zero := by
  apply add_left_cancel S (x := S.zero)
  rw [OrderedScalar.Axioms.add_neg,
    OrderedScalar.Axioms.zero_add]

theorem neg_sum (x y : S.Carrier) :
    S.neg (S.add x y) =
      S.add (S.neg x) (S.neg y) := by
  apply Eq.symm
  apply neg_unique S
  rw [OrderedScalar.Axioms.add_assoc]
  rw [← OrderedScalar.Axioms.add_assoc y (S.neg x) (S.neg y)]
  rw [OrderedScalar.Axioms.add_comm y (S.neg x)]
  rw [OrderedScalar.Axioms.add_assoc (S.neg x) y (S.neg y)]
  rw [OrderedScalar.Axioms.add_neg,
    OrderedScalar.Axioms.add_zero,
    OrderedScalar.Axioms.add_neg]

theorem add_left_comm (x y z : S.Carrier) :
    S.add x (S.add y z) =
      S.add y (S.add x z) := by
  rw [← OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm x y,
    OrderedScalar.Axioms.add_assoc]

theorem mul_left_comm (x y z : S.Carrier) :
    S.mul x (S.mul y z) =
      S.mul y (S.mul x z) := by
  rw [← OrderedScalar.Axioms.mul_assoc,
    OrderedScalar.Axioms.mul_comm x y,
    OrderedScalar.Axioms.mul_assoc]

/-- Cancel an additive inverse with one intervening summand. -/
theorem cancel_ac (x y z : S.Carrier) :
    S.add x (S.add y (S.add (S.neg x) z)) =
      S.add y z := by
  rw [← OrderedScalar.Axioms.add_assoc y (S.neg x) z]
  rw [OrderedScalar.Axioms.add_comm y (S.neg x)]
  rw [OrderedScalar.Axioms.add_assoc (S.neg x) y z]
  rw [← OrderedScalar.Axioms.add_assoc x (S.neg x)]
  rw [OrderedScalar.Axioms.add_neg,
    OrderedScalar.Axioms.zero_add]

theorem sub_eq_of_eq_add {d r x : S.Carrier}
    (h : d = S.add r x) :
    S.sub d r = x := by
  change S.add d (S.neg r) = x
  rw [h, OrderedScalar.Axioms.add_comm r x,
    OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_neg,
    OrderedScalar.Axioms.add_zero]

theorem difference_of_squares (x y : S.Carrier) :
    S.mul (S.sub x y) (S.add x y) =
      S.sub (S.square x) (S.square y) := by
  change
    S.mul (S.add x (S.neg y)) (S.add x y) =
      S.add (S.mul x x) (S.neg (S.mul y y))
  rw [right_distrib S, OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib,
    neg_mul S, neg_mul S,
    OrderedScalar.Axioms.mul_comm x y,
    OrderedScalar.Axioms.add_assoc]
  rw [← OrderedScalar.Axioms.add_assoc
    (S.mul y x) (S.neg (S.mul y x))]
  rw [OrderedScalar.Axioms.add_neg,
    OrderedScalar.Axioms.zero_add]

end Soultions.Sharygin.Page17.Problem40.Scalar
