import Sharygin16Problem36.Coordinates

/-!
# Sharygin, PDF page 16, problem 36

The three tangent intersections are computed directly.  Their base and height factors are
`(1 + sqrt 3)r` and `(3 + sqrt 3)r`; expanding their product and using
`(sqrt 3)^2 = 3` gives doubled area `2(3 + 2 sqrt 3)r^2`.
-/

namespace Soultions.Sharygin.Page16.Problem36.Solution

open Euclid
open Soultions.Sharygin.Page16.Problem36.Scalar
open Soultions.Sharygin.Page16.Problem36.Coordinates

variable (S : OrderedScalar) [S.Axioms]

private theorem three_mul (x : S.Carrier) :
    S.mul (three S) x = S.add (S.add x x) x := by
  change S.mul (S.add (S.add S.one S.one) S.one) x = _
  rw [right_distrib S, right_distrib S, OrderedScalar.Axioms.one_mul]

private theorem two_mul (x : S.Carrier) :
    S.mul (two S) x = S.add x x := by
  change S.mul (S.add S.one S.one) x = _
  rw [right_distrib S, OrderedScalar.Axioms.one_mul]

private theorem neg_three_add_one (x : S.Carrier) :
    S.add (S.neg (S.add (S.add x x) x)) x =
      S.neg (S.add x x) := by
  rw [neg_sum S, neg_sum S]
  simp only [OrderedScalar.Axioms.add_assoc,
    neg_add S, OrderedScalar.Axioms.add_zero]

private theorem cancel_last_of_three (x y : S.Carrier) :
    S.add x (S.neg (S.add (S.add y y) x)) =
      S.neg (S.add y y) := by
  rw [neg_sum S, neg_sum S]
  calc
    S.add x
        (S.add (S.add (S.neg y) (S.neg y)) (S.neg x)) =
      S.add (S.add (S.neg y) (S.neg y))
        (S.add x (S.neg x)) := by
      simp only [OrderedScalar.Axioms.add_assoc,
        OrderedScalar.Axioms.add_comm]
    _ = S.add (S.neg y) (S.neg y) := by
      rw [OrderedScalar.Axioms.add_neg,
        OrderedScalar.Axioms.add_zero]

private theorem third_incidence_second (data : Data S) :
    OnThirdTangent S data data.secondThirdVertex := by
  change
    S.add
        (S.mul data.sqrtThree
          (S.mul (S.neg data.sqrtThree) data.radius))
        data.radius =
      S.neg (S.mul (two S) data.radius)
  rw [← OrderedScalar.Axioms.mul_assoc,
    mul_neg S, neg_mul S]
  change
    S.add
        (S.neg (S.mul (S.square data.sqrtThree) data.radius))
        data.radius =
      S.neg (S.mul (two S) data.radius)
  rw [data.sqrtThree_square, three_mul S, two_mul S]
  exact neg_three_add_one S data.radius

private theorem third_incidence_first (data : Data S) :
    OnThirdTangent S data data.thirdFirstVertex := by
  change
    S.add
        (S.mul data.sqrtThree data.radius)
        (S.mul (S.neg (S.add (two S) data.sqrtThree)) data.radius) =
      S.neg (S.mul (two S) data.radius)
  rw [neg_mul S, right_distrib S, two_mul S]
  exact cancel_last_of_three S
    (S.mul data.sqrtThree data.radius) data.radius

private theorem coefficient_product (data : Data S) :
    S.mul
        (S.add S.one data.sqrtThree)
        (S.add (three S) data.sqrtThree) =
      S.mul (two S) data.areaCoefficient := by
  rw [OrderedScalar.Axioms.left_distrib, right_distrib S,
    right_distrib S, OrderedScalar.Axioms.one_mul,
    OrderedScalar.Axioms.mul_comm data.sqrtThree (three S),
    three_mul S]
  simp only [OrderedScalar.Axioms.one_mul]
  change
    S.add
        (S.add (three S)
          (S.add
            (S.add data.sqrtThree data.sqrtThree)
            data.sqrtThree))
        (S.add data.sqrtThree (S.square data.sqrtThree)) =
      S.mul (two S) data.areaCoefficient
  rw [data.sqrtThree_square]
  simp only [Data.areaCoefficient]
  rw [two_mul S, two_mul S]
  simp only [OrderedScalar.Axioms.add_comm, add_left_comm S]

private theorem double_area_value (data : Data S) :
    data.triangleDoubleArea =
      S.mul
        (S.mul (two S) data.areaCoefficient)
        (S.square data.radius) := by
  change
    determinant S
      (subPoint S data.secondThirdVertex data.firstSecondVertex)
      (subPoint S data.thirdFirstVertex data.firstSecondVertex) = _
  simp only [determinant, subPoint, Data.secondThirdVertex,
    Data.firstSecondVertex, Data.thirdFirstVertex]
  unfold OrderedScalar.sub
  rw [OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.zero_mul,
    neg_zero S, OrderedScalar.Axioms.add_zero]
  have hx :
      S.add
          (S.mul (S.neg data.sqrtThree) data.radius)
          (S.neg data.radius) =
        S.mul (S.neg (S.add S.one data.sqrtThree)) data.radius := by
    rw [neg_mul S, neg_mul S, ← neg_sum S,
      right_distrib S, OrderedScalar.Axioms.one_mul]
    congr 1
    exact OrderedScalar.Axioms.add_comm _ _
  have hy :
      S.add
          (S.mul (S.neg (S.add (two S) data.sqrtThree)) data.radius)
          (S.neg data.radius) =
        S.mul (S.neg (S.add (three S) data.sqrtThree)) data.radius := by
    rw [neg_mul S, neg_mul S, ← neg_sum S]
    apply congrArg S.neg
    rw [right_distrib S, right_distrib S]
    change
      S.add
          (S.add
            (S.mul (two S) data.radius)
            (S.mul data.sqrtThree data.radius))
          data.radius =
        S.add
          (S.mul (three S) data.radius)
          (S.mul data.sqrtThree data.radius)
    rw [three_mul S, two_mul S]
    simp only [OrderedScalar.Axioms.add_assoc,
      OrderedScalar.Axioms.add_comm]
  rw [hx, hy]
  have hnegativeProduct :
      S.mul
          (S.mul (S.neg (S.add S.one data.sqrtThree)) data.radius)
          (S.mul (S.neg (S.add (three S) data.sqrtThree)) data.radius) =
        S.mul
          (S.mul
            (S.add S.one data.sqrtThree)
            (S.add (three S) data.sqrtThree))
          (S.square data.radius) := by
    let a := S.add S.one data.sqrtThree
    let b := S.add (three S) data.sqrtThree
    calc
      S.mul
          (S.mul (S.neg a) data.radius)
          (S.mul (S.neg b) data.radius) =
        S.mul
          (S.neg (S.mul a data.radius))
          (S.neg (S.mul b data.radius)) := by
        rw [neg_mul S a data.radius, neg_mul S b data.radius]
      _ = S.mul
          (S.mul a data.radius)
          (S.mul b data.radius) := by
        rw [neg_mul S, mul_neg S, neg_neg S]
      _ = S.mul (S.mul a b) (S.square data.radius) := by
        calc
          S.mul (S.mul a data.radius) (S.mul b data.radius) =
              S.mul a
                (S.mul data.radius (S.mul b data.radius)) :=
            OrderedScalar.Axioms.mul_assoc _ _ _
          _ = S.mul a
              (S.mul b (S.mul data.radius data.radius)) := by
            rw [mul_left_comm S data.radius b data.radius]
          _ = S.mul (S.mul a b) (S.square data.radius) :=
            (OrderedScalar.Axioms.mul_assoc _ _ _).symm
  rw [hnegativeProduct]
  calc
    S.mul
        (S.mul
          (S.add S.one data.sqrtThree)
          (S.add (three S) data.sqrtThree))
        (S.square data.radius) = S.mul
        (S.mul (two S) data.areaCoefficient)
        (S.square data.radius) := by rw [coefficient_product S data]

/-- Problem 36.  The first three pairs certify the tangent intersections, and the final equation
is the exact answer `area = (3 + 2 sqrt 3) r^2`, stated without division by giving doubled area. -/
theorem problem36 (data : Data S) :
    (OnFirstTangent S data data.firstSecondVertex ∧
      OnSecondTangent S data data.firstSecondVertex) ∧
    (OnSecondTangent S data data.secondThirdVertex ∧
      OnThirdTangent S data data.secondThirdVertex) ∧
    (OnThirdTangent S data data.thirdFirstVertex ∧
      OnFirstTangent S data data.thirdFirstVertex) ∧
    data.triangleDoubleArea =
      S.mul
        (S.mul (two S) data.areaCoefficient)
        (S.square data.radius) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, third_incidence_second S data⟩,
    ⟨third_incidence_first S data, rfl⟩, double_area_value S data⟩

end Soultions.Sharygin.Page16.Problem36.Solution
