import Sharygin25Problem92.Configuration

namespace Soultions.Sharygin.Page25.Problem92.Solution

open Euclid
open Soultions.Sharygin.Page25.Problem92.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem right_distrib (x y z : S.Carrier) :
    S.mul (S.add x y) z = S.add (S.mul x z) (S.mul y z) := by
  rw [OrderedScalar.Axioms.mul_comm (S.add x y) z,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.mul_comm z x,
    OrderedScalar.Axioms.mul_comm z y]

private theorem scaled_square (root side : S.Carrier) :
    fourTimes S (S.mul root (S.square side)) =
      S.mul root (S.square (twice S side)) := by
  unfold fourTimes twice OrderedScalar.square
  simp only [OrderedScalar.Axioms.left_distrib, right_distrib S]

/--
Problem 92: `16S = √3(√3-1)²a²`, equivalently `S=(2√3-3)a²/8`.
-/
theorem problem92 (data : Data S) :
    sixteenTimes S data.triangleArea =
      S.mul data.rootThree
        (S.mul
          (S.square (S.sub data.rootThree S.one))
          (S.square data.squareSide)) := by
  calc
    sixteenTimes S data.triangleArea =
        fourTimes S (fourTimes S data.triangleArea) := rfl
    _ = fourTimes S (S.mul data.rootThree (S.square data.triangleSide)) := by
      rw [data.equilateral_area]
    _ = S.mul data.rootThree (S.square (twice S data.triangleSide)) :=
      scaled_square S data.rootThree data.triangleSide
    _ = S.mul data.rootThree
          (S.square (S.mul (S.sub data.rootThree S.one) data.squareSide)) := by
      rw [data.diagonal_intersection]
    _ = S.mul data.rootThree
          (S.mul (S.square (S.sub data.rootThree S.one))
            (S.square data.squareSide)) := by
      unfold OrderedScalar.square
      letI : Std.Associative S.mul :=
        ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
      letI : Std.Commutative S.mul :=
        ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
      ac_rfl

end Soultions.Sharygin.Page25.Problem92.Solution
