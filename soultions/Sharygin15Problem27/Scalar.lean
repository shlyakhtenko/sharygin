import Sharygin15Problem27.Tarski

/-!
# Problem-local scalar algebra for Sharygin, page 15, problem 27

Only identities that occur in the power calculation are derived here from
`OrderedScalar.Axioms`.
-/

namespace Soultions.Sharygin.Page15.Problem27.Scalar

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

theorem add_left_comm (x y z : S.Carrier) :
    S.add x (S.add y z) = S.add y (S.add x z) := by
  rw [← OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm x y,
    OrderedScalar.Axioms.add_assoc]

theorem mul_left_comm (x y z : S.Carrier) :
    S.mul x (S.mul y z) =
      S.mul y (S.mul x z) := by
  rw [← OrderedScalar.Axioms.mul_assoc,
    OrderedScalar.Axioms.mul_comm x y,
    OrderedScalar.Axioms.mul_assoc]

theorem two_ne_zero :
    S.add S.one S.one ≠ S.zero := by
  intro htwo
  have hone_le_zero :
      S.le S.one S.zero := by
    have h :=
      OrderedScalar.Axioms.add_le_add_right
        S.zero S.one S.one
        OrderedScalar.Axioms.zero_le_one
    rw [OrderedScalar.Axioms.zero_add, htwo] at h
    exact h
  have hzero_one :
      S.zero = S.one :=
    OrderedScalar.Axioms.le_antisymm
      S.zero S.one
      OrderedScalar.Axioms.zero_le_one
      hone_le_zero
  exact OrderedScalar.Axioms.zero_ne_one hzero_one

/-- Doubling is injective in the ordered scalar system. -/
theorem add_self_injective {x y : S.Carrier}
    (h : S.add x x = S.add y y) :
    x = y := by
  let two := S.add S.one S.one
  have htwo : two ≠ S.zero :=
    two_ne_zero S
  have hmul_x :
      S.mul two x = S.add x x := by
    dsimp [two]
    rw [OrderedScalar.Axioms.mul_comm
        (S.add S.one S.one) x,
      OrderedScalar.Axioms.left_distrib,
      OrderedScalar.Axioms.mul_one]
  have hmul_y :
      S.mul two y = S.add y y := by
    dsimp [two]
    rw [OrderedScalar.Axioms.mul_comm
        (S.add S.one S.one) y,
      OrderedScalar.Axioms.left_distrib,
      OrderedScalar.Axioms.mul_one]
  have hscaled :
      S.mul (S.inv two) (S.mul two x) =
        S.mul (S.inv two) (S.mul two y) :=
    congrArg (S.mul (S.inv two))
      (hmul_x.trans (h.trans hmul_y.symm))
  calc
    x = S.mul S.one x :=
      (OrderedScalar.Axioms.one_mul x).symm
    _ = S.mul (S.mul (S.inv two) two) x := by
      rw [OrderedScalar.Axioms.mul_comm
        (S.inv two) two,
        OrderedScalar.Axioms.mul_inv two htwo]
    _ = S.mul (S.inv two) (S.mul two x) :=
      OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul (S.inv two) (S.mul two y) :=
      hscaled
    _ = S.mul (S.mul (S.inv two) two) y :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one y := by
      rw [OrderedScalar.Axioms.mul_comm
        (S.inv two) two,
        OrderedScalar.Axioms.mul_inv two htwo]
    _ = y := OrderedScalar.Axioms.one_mul y

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

/-- Expanding `(x+x)²` without introducing numeral notation. -/
theorem square_double (x : S.Carrier) :
    S.square (S.add x x) =
      S.add
        (S.add (S.square x) (S.square x))
        (S.add (S.square x) (S.square x)) := by
  change
    S.mul (S.add x x) (S.add x x) =
      S.add
        (S.add (S.mul x x) (S.mul x x))
        (S.add (S.mul x x) (S.mul x x))
  rw [right_distrib S,
    OrderedScalar.Axioms.left_distrib]

theorem neg_neg (x : S.Carrier) :
    S.neg (S.neg x) = x := by
  apply add_left_cancel S (x := S.neg x)
  rw [OrderedScalar.Axioms.add_neg,
    neg_add S]

/-- The sum of the squares of `x+y` and `x-y`. -/
theorem square_add_add_square_sub (x y : S.Carrier) :
    S.add
        (S.square (S.add x y))
        (S.square (S.sub x y)) =
      S.add
        (S.add (S.square x) (S.square y))
        (S.add (S.square x) (S.square y)) := by
  change
    S.add
        (S.mul (S.add x y) (S.add x y))
        (S.mul (S.add x (S.neg y)) (S.add x (S.neg y))) =
      S.add
        (S.add (S.mul x x) (S.mul y y))
        (S.add (S.mul x x) (S.mul y y))
  rw [right_distrib S, right_distrib S]
  rw [OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib]
  rw [mul_neg S, neg_mul S, mul_neg S, neg_mul S]
  rw [OrderedScalar.Axioms.mul_comm y x]
  rw [neg_neg S]
  calc
    S.add
          (S.add
            (S.add (S.mul x x) (S.mul x y))
            (S.add (S.mul x y) (S.mul y y)))
          (S.add
            (S.add (S.mul x x) (S.neg (S.mul x y)))
            (S.add (S.neg (S.mul x y)) (S.mul y y))) =
        S.add
          (S.add
            (S.add (S.mul x x) (S.mul y y))
            (S.add (S.mul x x) (S.mul y y)))
          (S.add
            (S.add (S.mul x y) (S.neg (S.mul x y)))
            (S.add (S.mul x y) (S.neg (S.mul x y)))) := by
      simp only [OrderedScalar.Axioms.add_assoc,
        OrderedScalar.Axioms.add_comm,
        add_left_comm S]
    _ = S.add
          (S.add (S.mul x x) (S.mul y y))
          (S.add (S.mul x x) (S.mul y y)) := by
      rw [OrderedScalar.Axioms.add_neg,
        OrderedScalar.Axioms.zero_add,
        OrderedScalar.Axioms.add_zero]

end Soultions.Sharygin.Page15.Problem27.Scalar
