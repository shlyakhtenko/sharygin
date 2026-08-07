import Sharygin12Problem8.Angle

/-!
# Problem-local scalar algebra for Sharygin, page 12, problem 8

Only identities that occur in the power calculation are derived here from
`OrderedScalar.Axioms`.
-/

namespace Soultions.Sharygin.Page12.Problem8.Scalar

open Euclid

variable (S : OrderedScalar) [S.Axioms]

theorem neg_add (x : S.Carrier) :
    S.add (S.neg x) x = S.zero := by
  rw [OrderedScalar.Axioms.add_comm]
  exact OrderedScalar.Axioms.add_neg x

theorem add_left_cancel {x y z : S.Carrier}
    (h : S.add x y = S.add x z) :
    y = z := by
  have h' :=
    congrArg (fun w => S.add (S.neg x) w) h
  calc
    y = S.add S.zero y := (OrderedScalar.Axioms.zero_add y).symm
    _ = S.add (S.add (S.neg x) x) y := by rw [neg_add S x]
    _ = S.add (S.neg x) (S.add x y) :=
      OrderedScalar.Axioms.add_assoc _ _ _
    _ = S.add (S.neg x) (S.add x z) := h'
    _ = S.add (S.add (S.neg x) x) z :=
      (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = S.add S.zero z := by rw [neg_add S x]
    _ = z := OrderedScalar.Axioms.zero_add z

theorem add_right_cancel {x y z : S.Carrier}
    (h : S.add y x = S.add z x) :
    y = z := by
  apply add_left_cancel S (x := x)
  rw [OrderedScalar.Axioms.add_comm x y,
    OrderedScalar.Axioms.add_comm x z]
  exact h

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
    mul_neg S,
    OrderedScalar.Axioms.mul_comm y x]

theorem sub_eq_of_eq_add {d r x : S.Carrier}
    (h : d = S.add r x) :
    S.sub d r = x := by
  change S.add d (S.neg r) = x
  rw [h, OrderedScalar.Axioms.add_comm r x,
    OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_neg,
    OrderedScalar.Axioms.add_zero]

/-- `(x-r)(x+r)=x²-r²`, in the repository's primitive scalar operations. -/
theorem difference_of_squares (x r : S.Carrier) :
    S.mul (S.sub x r) (S.add x r) =
      S.sub (S.square x) (S.square r) := by
  change
    S.mul (S.add x (S.neg r)) (S.add x r) =
      S.add (S.mul x x) (S.neg (S.mul r r))
  rw [right_distrib S]
  rw [OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib]
  rw [neg_mul S r x, neg_mul S r r]
  rw [OrderedScalar.Axioms.mul_comm x r]
  rw [OrderedScalar.Axioms.add_assoc]
  rw [← OrderedScalar.Axioms.add_assoc
    (S.mul r x) (S.neg (S.mul r x)) (S.neg (S.mul r r))]
  rw [OrderedScalar.Axioms.add_neg]
  rw [OrderedScalar.Axioms.zero_add]

end Soultions.Sharygin.Page12.Problem8.Scalar
