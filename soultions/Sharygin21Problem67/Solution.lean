import Sharygin21Problem67.Configuration

/-!
# Sharygin, PDF page 21, problem 67

Substitution in `4S=√3 s²`, followed by `(√3)²=3`, gives
`S=(6+4√3)r²`.
-/

namespace Soultions.Sharygin.Page21.Problem67.Solution

open Euclid
open Soultions.Sharygin.Page21.Problem67.Scalar
open Soultions.Sharygin.Page21.Problem67.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem four_as_product (x : S.Carrier) :
    fourTimes S x = S.mul (fourTimes S S.one) x := by
  unfold fourTimes twice
  simp only [right_distrib S, OrderedScalar.Axioms.one_mul]

private theorem square_product (x y : S.Carrier) :
    S.square (S.mul x y) = S.mul (S.square x) (S.square y) := by
  unfold OrderedScalar.square
  letI : Std.Associative S.mul :=
    ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
  letI : Std.Commutative S.mul :=
    ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
  ac_rfl

private theorem square_sum (x y : S.Carrier) :
    S.square (S.add x y) =
      S.add (S.square x)
        (S.add (S.mul x y) (S.add (S.mul y x) (S.square y))) := by
  unfold OrderedScalar.square
  rw [right_distrib S, OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib, OrderedScalar.Axioms.add_assoc]

private theorem square_twice (x : S.Carrier) :
    S.square (twice S x) = S.mul (fourTimes S S.one) (S.square x) := by
  unfold twice
  rw [square_sum S]
  unfold fourTimes twice
  rw [right_distrib S, right_distrib S]
  simp only [OrderedScalar.Axioms.one_mul]
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  ac_rfl

private theorem root_coefficient (data : Data S) :
    S.mul data.rootThree (S.square (S.add data.rootThree S.one)) =
      S.add (sixTimes S S.one) (fourTimes S data.rootThree) := by
  have hroot := data.root_three_square
  unfold OrderedScalar.square at hroot
  rw [square_sum S, data.root_three_square,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.left_distrib, OrderedScalar.Axioms.left_distrib]
  simp only [OrderedScalar.Axioms.mul_one, OrderedScalar.Axioms.one_mul]
  rw [hroot]
  unfold OrderedScalar.square sixTimes threeTimes fourTimes twice
  simp only [OrderedScalar.Axioms.mul_one, OrderedScalar.Axioms.left_distrib]
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  letI : Std.Associative S.mul :=
    ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
  letI : Std.Commutative S.mul :=
    ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
  ac_rfl

/-- Problem 67: the tangent triangle has area `(6+4√3)r²`. -/
theorem problem67 (data : Data S) :
    data.triangleArea =
      S.mul
        (S.add (sixTimes S S.one) (fourTimes S data.rootThree))
        (S.square data.radius) := by
  apply mul_left_cancel S data.four_ne_zero
  calc
    S.mul (fourTimes S S.one) data.triangleArea =
      fourTimes S data.triangleArea := (four_as_product S data.triangleArea).symm
    _ = S.mul data.rootThree (S.square data.triangleSide) := data.equilateral_area
    _ = S.mul data.rootThree
        (S.square
          (S.mul (twice S data.radius) (S.add data.rootThree S.one))) := by
      rw [data.tangent_triangle_side]
    _ = S.mul (fourTimes S S.one)
        (S.mul
          (S.mul data.rootThree (S.square (S.add data.rootThree S.one)))
          (S.square data.radius)) := by
      rw [square_product S, square_twice S]
      letI : Std.Associative S.mul :=
        ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
      letI : Std.Commutative S.mul :=
        ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
      ac_rfl
    _ = S.mul (fourTimes S S.one)
        (S.mul
          (S.add (sixTimes S S.one) (fourTimes S data.rootThree))
          (S.square data.radius)) := by
      rw [root_coefficient S data]

end Soultions.Sharygin.Page21.Problem67.Solution
