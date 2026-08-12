import Sharygin26Problem98.Configuration

namespace Soultions.Sharygin.Page26.Problem98.Solution

open Euclid
open Soultions.Sharygin.Page26.Problem98.Scalar
open Soultions.Sharygin.Page26.Problem98.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem positive_square_root_relation (data : Data S) :
    S.mul data.rootTwo data.nearSegment =
      S.mul data.cosAlpha data.hypotenuse := by
  apply eq_of_sub_eq_zero S
  apply mul_right_cancel S data.positive_branch
  rw [difference_of_squares S, data.equal_area_square_relation]
  unfold OrderedScalar.sub
  rw [OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.zero_mul]

/--
Problem 98: the perpendicular bisecting the area divides the hypotenuse in the ratio
`cos α : (√2 - cos α)`, stated without division.
-/
theorem problem98 (data : Data S) :
    S.mul (S.sub data.rootTwo data.cosAlpha) data.nearSegment =
      S.mul data.cosAlpha data.farSegment := by
  have hlinear := positive_square_root_relation S data
  have hsplit :
      S.mul data.rootTwo data.nearSegment =
        S.add
          (S.mul data.cosAlpha data.nearSegment)
          (S.mul data.cosAlpha data.farSegment) := by
    calc
      S.mul data.rootTwo data.nearSegment =
          S.mul data.cosAlpha data.hypotenuse := hlinear
      _ = S.mul data.cosAlpha
          (S.add data.nearSegment data.farSegment) := by
        rw [← data.hypotenuse_additive]
      _ = S.add
          (S.mul data.cosAlpha data.nearSegment)
          (S.mul data.cosAlpha data.farSegment) :=
        OrderedScalar.Axioms.left_distrib _ _ _
  calc
    S.mul (S.sub data.rootTwo data.cosAlpha) data.nearSegment =
        S.sub
          (S.mul data.rootTwo data.nearSegment)
          (S.mul data.cosAlpha data.nearSegment) :=
      sub_mul S data.rootTwo data.cosAlpha data.nearSegment
    _ = S.mul data.cosAlpha data.farSegment :=
      sub_eq_of_eq_add S hsplit

end Soultions.Sharygin.Page26.Problem98.Solution
