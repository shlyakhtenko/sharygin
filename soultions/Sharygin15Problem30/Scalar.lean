import Euclid

/-!
# Scalar identities for Sharygin, PDF page 15, problem 30

Only the ring identities used in this problem's determinant calculation are
derived here.
-/

namespace Soultions.Sharygin.Page15.Problem30.Scalar

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

theorem add_right_cancel {x y z : S.Carrier}
    (h : S.add y x = S.add z x) :
    y = z := by
  apply add_left_cancel S (x := x)
  rw [OrderedScalar.Axioms.add_comm x y,
    OrderedScalar.Axioms.add_comm x z]
  exact h

theorem two_ne_zero :
    S.add S.one S.one ≠ S.zero := by
  intro htwo
  have hone_le_zero : S.le S.one S.zero := by
    have h := OrderedScalar.Axioms.add_le_add_right
      S.zero S.one S.one OrderedScalar.Axioms.zero_le_one
    rw [OrderedScalar.Axioms.zero_add, htwo] at h
    exact h
  exact OrderedScalar.Axioms.zero_ne_one
    (OrderedScalar.Axioms.le_antisymm S.zero S.one
      OrderedScalar.Axioms.zero_le_one hone_le_zero)

theorem add_self_injective {x y : S.Carrier}
    (h : S.add x x = S.add y y) :
    x = y := by
  let two := S.add S.one S.one
  have htwo : two ≠ S.zero := two_ne_zero S
  have hmul (w : S.Carrier) : S.mul two w = S.add w w := by
    dsimp [two]
    rw [OrderedScalar.Axioms.mul_comm, OrderedScalar.Axioms.left_distrib,
      OrderedScalar.Axioms.mul_one]
  have hscaled := congrArg (S.mul (S.inv two))
    ((hmul x).trans (h.trans (hmul y).symm))
  calc
    x = S.mul S.one x := (OrderedScalar.Axioms.one_mul x).symm
    _ = S.mul (S.mul (S.inv two) two) x := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv two) two,
        OrderedScalar.Axioms.mul_inv two htwo]
    _ = S.mul (S.inv two) (S.mul two x) :=
      OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul (S.inv two) (S.mul two y) := hscaled
    _ = S.mul (S.mul (S.inv two) two) y :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul S.one y := by
      rw [OrderedScalar.Axioms.mul_comm (S.inv two) two,
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
    mul_neg S, OrderedScalar.Axioms.mul_comm y x]

theorem sub_self (x : S.Carrier) :
    S.sub x x = S.zero :=
  OrderedScalar.Axioms.add_neg x

theorem sub_eq_of_eq_add {d r x : S.Carrier}
    (h : d = S.add r x) :
    S.sub d r = x := by
  change S.add d (S.neg r) = x
  rw [h, OrderedScalar.Axioms.add_comm r x,
    OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_neg,
    OrderedScalar.Axioms.add_zero]

theorem difference_of_squares (x r : S.Carrier) :
    S.mul (S.sub x r) (S.add x r) =
      S.sub (S.square x) (S.square r) := by
  change S.mul (S.add x (S.neg r)) (S.add x r) =
    S.add (S.mul x x) (S.neg (S.mul r r))
  rw [right_distrib S, OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib, neg_mul S r x, neg_mul S r r,
    OrderedScalar.Axioms.mul_comm x r, OrderedScalar.Axioms.add_assoc,
    ← OrderedScalar.Axioms.add_assoc
      (S.mul r x) (S.neg (S.mul r x)) (S.neg (S.mul r r)),
    OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.zero_add]

theorem mul_eq_zero {x y : S.Carrier}
    (h : S.mul x y = S.zero) :
    x = S.zero ∨ y = S.zero := by
  by_cases hx : x = S.zero
  · exact Or.inl hx
  · right
    have hscaled := congrArg (S.mul (S.inv x)) h
    calc
      y = S.mul S.one y := (OrderedScalar.Axioms.one_mul y).symm
      _ = S.mul (S.mul (S.inv x) x) y := by
        rw [OrderedScalar.Axioms.mul_comm (S.inv x) x,
          OrderedScalar.Axioms.mul_inv x hx]
      _ = S.mul (S.inv x) (S.mul x y) :=
        OrderedScalar.Axioms.mul_assoc _ _ _
      _ = S.mul (S.inv x) S.zero := hscaled
      _ = S.zero := by
        rw [OrderedScalar.Axioms.mul_comm, OrderedScalar.Axioms.zero_mul]

theorem square_injective_nonnegative
    {x y : S.Carrier}
    (hx : S.le S.zero x)
    (hy : S.le S.zero y)
    (h : S.square x = S.square y) :
    x = y := by
  have hproduct :
      S.mul (S.sub x y) (S.add x y) = S.zero := by
    rw [difference_of_squares S, h, sub_self S]
  rcases mul_eq_zero S hproduct with hsub | hsum
  · apply add_right_cancel S (x := S.neg y)
    simpa only [OrderedScalar.Axioms.add_assoc,
      OrderedScalar.Axioms.add_neg,
      OrderedScalar.Axioms.add_zero] using hsub
  · have hy_le_zero : S.le y S.zero := by
      have hle := OrderedScalar.Axioms.add_le_add_right
        S.zero x y hx
      rw [OrderedScalar.Axioms.zero_add, hsum] at hle
      exact hle
    have hy_zero := OrderedScalar.Axioms.le_antisymm
      y S.zero hy_le_zero hy
    rw [hy_zero, OrderedScalar.Axioms.add_zero] at hsum
    rw [hsum, hy_zero]

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

theorem square_add_add_square_sub (x y : S.Carrier) :
    S.add (S.square (S.add x y)) (S.square (S.sub x y)) =
      S.add (S.add (S.square x) (S.square y))
        (S.add (S.square x) (S.square y)) := by
  change
    S.add
        (S.mul (S.add x y) (S.add x y))
        (S.mul (S.add x (S.neg y)) (S.add x (S.neg y))) =
      S.add
        (S.add (S.mul x x) (S.mul y y))
        (S.add (S.mul x x) (S.mul y y))
  rw [right_distrib S, right_distrib S,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib,
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
      simp only [OrderedScalar.Axioms.add_assoc,
        OrderedScalar.Axioms.add_comm, add_left_comm S]
    _ = S.add (S.add (S.mul x x) (S.mul y y))
          (S.add (S.mul x x) (S.mul y y)) := by
      rw [OrderedScalar.Axioms.add_neg,
        OrderedScalar.Axioms.zero_add,
        OrderedScalar.Axioms.add_zero]

theorem square_double (x : S.Carrier) :
    S.square (S.add x x) =
      S.add (S.add (S.square x) (S.square x))
        (S.add (S.square x) (S.square x)) := by
  change S.mul (S.add x x) (S.add x x) =
    S.add (S.add (S.mul x x) (S.mul x x))
      (S.add (S.mul x x) (S.mul x x))
  rw [right_distrib S, OrderedScalar.Axioms.left_distrib]

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

theorem sub_nonnegative_of_le {x y : S.Carrier}
    (hxy : S.le x y) :
    S.le S.zero (S.sub y x) := by
  have h := OrderedScalar.Axioms.add_le_add_right x y (S.neg x) hxy
  change S.le S.zero (S.add y (S.neg x))
  rw [← OrderedScalar.Axioms.add_neg x]
  exact h

theorem neg_le_neg_of_le {x y : S.Carrier}
    (hxy : S.le x y) :
    S.le (S.neg y) (S.neg x) := by
  have h := OrderedScalar.Axioms.add_le_add_right x y (S.neg x) hxy
  have h' := OrderedScalar.Axioms.add_le_add_right
    (S.add x (S.neg x)) (S.add y (S.neg x)) (S.neg y) h
  rw [OrderedScalar.Axioms.add_neg,
    OrderedScalar.Axioms.zero_add] at h'
  have hsimplify :
      S.add (S.add y (S.neg x)) (S.neg y) = S.neg x := by
    rw [OrderedScalar.Axioms.add_assoc,
      OrderedScalar.Axioms.add_comm (S.neg x) (S.neg y),
      ← OrderedScalar.Axioms.add_assoc,
      OrderedScalar.Axioms.add_neg,
      OrderedScalar.Axioms.zero_add]
  rw [hsimplify] at h'
  exact h'

theorem add_le_add_left {x y z : S.Carrier}
    (hxy : S.le x y) :
    S.le (S.add z x) (S.add z y) := by
  have h := OrderedScalar.Axioms.add_le_add_right x y z hxy
  simpa only [OrderedScalar.Axioms.add_comm] using h

theorem mul_le_mul_of_nonnegative_left {x y z : S.Carrier}
    (hz : S.le S.zero z)
    (hxy : S.le x y) :
    S.le (S.mul z x) (S.mul z y) := by
  have hdiff : S.le S.zero (S.mul z (S.sub y x)) :=
    OrderedScalar.Axioms.mul_nonneg z (S.sub y x) hz
      (sub_nonnegative_of_le S hxy)
  have htranslated :=
    OrderedScalar.Axioms.add_le_add_right
      S.zero (S.mul z (S.sub y x)) (S.mul z x) hdiff
  have hsum :
      S.add (S.mul z (S.sub y x)) (S.mul z x) =
        S.mul z y := by
    change
      S.add (S.mul z (S.add y (S.neg x))) (S.mul z x) =
        S.mul z y
    rw [OrderedScalar.Axioms.left_distrib, mul_neg S]
    rw [OrderedScalar.Axioms.add_comm
      (S.add (S.mul z y) (S.neg (S.mul z x)))
      (S.mul z x)]
    rw [OrderedScalar.Axioms.add_comm
      (S.mul z y) (S.neg (S.mul z x)),
      ← OrderedScalar.Axioms.add_assoc,
      OrderedScalar.Axioms.add_neg,
      OrderedScalar.Axioms.zero_add]
  rw [OrderedScalar.Axioms.zero_add, hsum] at htranslated
  exact htranslated

theorem one_le_one_add_of_nonnegative {x : S.Carrier}
    (hx : S.le S.zero x) :
    S.le S.one (S.add S.one x) := by
  have h := OrderedScalar.Axioms.add_le_add_right S.zero x S.one hx
  simpa only [OrderedScalar.Axioms.zero_add,
    OrderedScalar.Axioms.add_comm] using h

theorem one_not_le_zero : ¬ S.le S.one S.zero := by
  intro hone
  exact OrderedScalar.Axioms.zero_ne_one
    (OrderedScalar.Axioms.le_antisymm S.zero S.one
      OrderedScalar.Axioms.zero_le_one hone)

theorem nonzero_of_one_le {x : S.Carrier}
    (hx : S.le S.one x) :
    x ≠ S.zero := by
  intro hzero
  rw [hzero] at hx
  exact one_not_le_zero S hx

theorem inverse_nonnegative {x : S.Carrier}
    (hx : S.le S.zero x)
    (hx0 : x ≠ S.zero) :
    S.le S.zero (S.inv x) := by
  rcases OrderedScalar.Axioms.le_total S.zero (S.inv x) with hinv | hinv
  · exact hinv
  · have hprod := mul_le_mul_of_nonnegative_left S hx hinv
    rw [mul_zero S, OrderedScalar.Axioms.mul_inv x hx0] at hprod
    exact False.elim (one_not_le_zero S hprod)

theorem mul_le_cancel_of_nonnegative_left {x y z : S.Carrier}
    (hz : S.le S.zero z)
    (hz0 : z ≠ S.zero)
    (hxy : S.le (S.mul z x) (S.mul z y)) :
    S.le x y := by
  have hinv := inverse_nonnegative S hz hz0
  have h := mul_le_mul_of_nonnegative_left S hinv hxy
  have hcancel (w : S.Carrier) :
      S.mul (S.inv z) (S.mul z w) = w := by
    rw [← OrderedScalar.Axioms.mul_assoc,
      OrderedScalar.Axioms.mul_comm (S.inv z) z,
      OrderedScalar.Axioms.mul_inv z hz0,
      OrderedScalar.Axioms.one_mul]
  rw [hcancel x, hcancel y] at h
  exact h

end Soultions.Sharygin.Page15.Problem30.Scalar
