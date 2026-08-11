import Sharygin20Problem61.Configuration

/-!
# Sharygin, PDF page 20, problem 61

The nonzero geometric factor selects `5y=3h`.  Squaring this equality and
using width `4y` gives the requested scaled area formula.
-/

namespace Soultions.Sharygin.Page20.Problem61.Solution

open Euclid
open Soultions.Sharygin.Page20.Problem61.Scalar
open Soultions.Sharygin.Page20.Problem61.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem height_relation (data : Data S) :
    fiveTimes S data.rectangleHeight =
      threeTimes S data.segmentHeight := by
  apply eq_of_sub_eq_zero S
  apply mul_right_cancel S data.positive_root
  calc
    S.mul
        (S.sub (fiveTimes S data.rectangleHeight)
          (threeTimes S data.segmentHeight))
        (S.add data.rectangleHeight data.segmentHeight) = S.zero :=
      data.factored_circle_equation
    _ = S.mul S.zero
        (S.add data.rectangleHeight data.segmentHeight) :=
      (OrderedScalar.Axioms.zero_mul _).symm

private theorem square_five (x : S.Carrier) :
    S.square (fiveTimes S x) = twentyFiveTimes S (S.square x) := by
  unfold OrderedScalar.square twentyFiveTimes fiveTimes fourTimes twice
  simp only [right_distrib S, OrderedScalar.Axioms.left_distrib]

private theorem square_three (x : S.Carrier) :
    S.square (threeTimes S x) = nineTimes S (S.square x) := by
  unfold OrderedScalar.square nineTimes threeTimes twice
  simp only [right_distrib S, OrderedScalar.Axioms.left_distrib]

private theorem squared_height_relation (data : Data S) :
    twentyFiveTimes S (S.square data.rectangleHeight) =
      nineTimes S (S.square data.segmentHeight) := by
  calc
    twentyFiveTimes S (S.square data.rectangleHeight) =
        S.square (fiveTimes S data.rectangleHeight) :=
      (square_five S _).symm
    _ = S.square (threeTimes S data.segmentHeight) := by
      rw [height_relation S data]
    _ = nineTimes S (S.square data.segmentHeight) := square_three S _

private theorem area_is_four_squares (data : Data S) :
    data.rectangleArea = fourTimes S (S.square data.rectangleHeight) := by
  rw [data.area_product, data.width_ratio]
  unfold fourTimes twice OrderedScalar.square
  simp only [right_distrib S]

/-- Problem 61: `25 area = 36h²`. -/
theorem problem61 (data : Data S) :
    twentyFiveTimes S data.rectangleArea =
      thirtySixTimes S (S.square data.segmentHeight) := by
  rw [area_is_four_squares S data]
  calc
    twentyFiveTimes S
        (fourTimes S (S.square data.rectangleHeight)) =
      fourTimes S
        (twentyFiveTimes S (S.square data.rectangleHeight)) := by
      letI : Std.Associative S.add :=
        ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
      letI : Std.Commutative S.add :=
        ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
      unfold twentyFiveTimes fiveTimes fourTimes twice
      ac_rfl
    _ = fourTimes S (nineTimes S (S.square data.segmentHeight)) := by
      rw [squared_height_relation S data]
    _ = thirtySixTimes S (S.square data.segmentHeight) := rfl

end Soultions.Sharygin.Page20.Problem61.Solution
