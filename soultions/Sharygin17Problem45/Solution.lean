import Sharygin17Problem45.Configuration

/-!
# Sharygin, PDF page 17, problem 45

The two cross triangles have common area `X=abq`, while the base triangles have areas
`S₁=a²q` and `S₂=b²q`.  Hence `X²=S₁S₂`, and finite additivity gives
`S=S₁+S₂+2X`.
-/

namespace Soultions.Sharygin.Page17.Problem45.Solution

open Euclid
open Soultions.Sharygin.Page17.Problem45.Scalar
open Soultions.Sharygin.Page17.Problem45.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem square_product (x y : S.Carrier) :
    S.square (S.mul x y) =
      S.mul (S.square x) (S.square y) := by
  change
    S.mul (S.mul x y) (S.mul x y) =
      S.mul (S.mul x x) (S.mul y y)
  simp only [OrderedScalar.Axioms.mul_comm, mul_left_comm S]

private theorem cross_square (data : Data S) :
    S.square data.crossArea =
      S.mul data.firstArea data.secondArea := by
  simp only [Data.crossArea, Data.firstArea, Data.secondArea]
  rw [square_product S, square_product S]
  change
    S.mul
        (S.mul (S.mul data.firstBase data.firstBase)
          (S.mul data.secondBase data.secondBase))
        (S.mul data.commonAreaScale data.commonAreaScale) =
      S.mul
        (S.mul (S.mul data.firstBase data.firstBase) data.commonAreaScale)
        (S.mul (S.mul data.secondBase data.secondBase) data.commonAreaScale)
  simp only [OrderedScalar.Axioms.mul_comm, mul_left_comm S]

private theorem square_twice (x : S.Carrier) :
    S.square (twice S x) = fourTimes S (S.square x) := by
  change
    S.mul (S.add x x) (S.add x x) =
      S.add (S.add (S.mul x x) (S.mul x x))
        (S.add (S.mul x x) (S.mul x x))
  rw [right_distrib S, OrderedScalar.Axioms.left_distrib]

private theorem excess_is_twice_cross (data : Data S) :
    S.sub data.totalArea (S.add data.firstArea data.secondArea) =
      twice S data.crossArea := by
  apply sub_eq_of_eq_add S
  rfl

/-- Problem 45.  The first two equations give the usual answer
`S=(sqrt S₁ + sqrt S₂)²`; the last eliminates the auxiliary cross-triangle area. -/
theorem problem45 (data : Data S) :
    data.totalArea =
        S.add (S.add data.firstArea data.secondArea)
          (twice S data.crossArea) ∧
      S.square data.crossArea =
        S.mul data.firstArea data.secondArea ∧
      S.square
          (S.sub data.totalArea
            (S.add data.firstArea data.secondArea)) =
        fourTimes S (S.mul data.firstArea data.secondArea) := by
  refine ⟨rfl, cross_square S data, ?_⟩
  rw [excess_is_twice_cross S data,
    square_twice S, cross_square S data]

end Soultions.Sharygin.Page17.Problem45.Solution
