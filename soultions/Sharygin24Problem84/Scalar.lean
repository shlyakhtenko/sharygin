import Euclid

/-! Problem-local scalar algebra for Sharygin, PDF page 24, problem 84. -/

namespace Soultions.Sharygin.Page24.Problem84.Scalar

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

theorem add_right_cancel {x y z : S.Carrier} (h : S.add y x = S.add z x) : y = z := by
  apply add_left_cancel S (x := x)
  rw [OrderedScalar.Axioms.add_comm x y, OrderedScalar.Axioms.add_comm x z]
  exact h

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
    _ = S.add (S.mul x y) (S.neg (S.mul x y)) := (OrderedScalar.Axioms.add_neg _).symm

theorem neg_mul (x y : S.Carrier) : S.mul (S.neg x) y = S.neg (S.mul x y) := by
  rw [OrderedScalar.Axioms.mul_comm (S.neg x) y, mul_neg S,
    OrderedScalar.Axioms.mul_comm y x]

theorem difference_of_squares (x y : S.Carrier) :
    S.mul (S.sub x y) (S.add x y) = S.sub (S.square x) (S.square y) := by
  unfold OrderedScalar.sub OrderedScalar.square
  rw [right_distrib S, OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib, neg_mul S, neg_mul S,
    OrderedScalar.Axioms.mul_comm x y, OrderedScalar.Axioms.add_assoc]
  rw [← OrderedScalar.Axioms.add_assoc (S.mul y x) (S.neg (S.mul y x))]
  rw [OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.zero_add]

theorem two_ne_zero : S.add S.one S.one ≠ S.zero := by
  intro htwo
  have hle := OrderedScalar.Axioms.add_le_add_right S.zero S.one S.one
    OrderedScalar.Axioms.zero_le_one
  rw [OrderedScalar.Axioms.zero_add, htwo] at hle
  exact OrderedScalar.Axioms.zero_ne_one
    (OrderedScalar.Axioms.le_antisymm S.zero S.one
      OrderedScalar.Axioms.zero_le_one hle)

theorem twice_injective {x y : S.Carrier} (h : S.add x x = S.add y y) : x = y := by
  let two := S.add S.one S.one
  have htwo : two ≠ S.zero := two_ne_zero S
  have hinv : S.mul (S.inv two) two = S.one := by
    rw [OrderedScalar.Axioms.mul_comm]
    exact OrderedScalar.Axioms.mul_inv two htwo
  have hmul : S.mul two x = S.mul two y := by
    unfold two
    rw [right_distrib S, right_distrib S,
      OrderedScalar.Axioms.one_mul, OrderedScalar.Axioms.one_mul]
    exact h
  calc
    x = S.mul S.one x := (OrderedScalar.Axioms.one_mul x).symm
    _ = S.mul (S.mul (S.inv two) two) x := by rw [hinv]
    _ = S.mul (S.inv two) (S.mul two x) := OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul (S.inv two) (S.mul two y) := congrArg (S.mul (S.inv two)) hmul
    _ = S.mul (S.mul (S.inv two) two) y := (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one y := by rw [hinv]
    _ = y := OrderedScalar.Axioms.one_mul y

end Soultions.Sharygin.Page24.Problem84.Scalar
