import Sharygin17Problem42.Configuration

/-!
# Sharygin, PDF page 17, problem 42

The diagonal bisectors force both legs to have length `b`.  Dropping the two altitudes leaves
horizontal projection `(a-b)/2`.  Pythagoras then gives
`(2h)^2 = (a+b)(3b-a)`, while twice the area is `(a+b)h`.
-/

namespace Soultions.Sharygin.Page17.Problem42.Solution

open Euclid
open Soultions.Sharygin.Page17.Problem42.Scalar
open Soultions.Sharygin.Page17.Problem42.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem square_twice (x : S.Carrier) :
    S.square (twice S x) =
      twice S (twice S (S.square x)) := by
  change
    S.mul (S.add x x) (S.add x x) =
      S.add (S.add (S.mul x x) (S.mul x x))
        (S.add (S.mul x x) (S.mul x x))
  rw [right_distrib S, OrderedScalar.Axioms.left_distrib]

private theorem scaled_pythagorean (data : Data S) :
    S.add
        (S.square (twice S data.horizontalProjection))
        (S.square (twice S data.height)) =
      S.square (twice S data.upperBase) := by
  rw [square_twice S, square_twice S, square_twice S,
    data.side_pythagorean]
  simp only [twice, OrderedScalar.Axioms.add_comm, add_left_comm S]

private theorem doubled_height_difference (data : Data S) :
    S.square (twice S data.height) =
      S.sub
        (S.square (twice S data.upperBase))
        (S.square (twice S data.horizontalProjection)) := by
  exact (sub_eq_of_eq_add S (scaled_pythagorean S data).symm).symm

private theorem first_factor (data : Data S) :
    S.sub (twice S data.upperBase)
        (S.sub data.lowerBase data.upperBase) =
      S.sub (threeTimes S data.upperBase) data.lowerBase := by
  unfold twice threeTimes OrderedScalar.sub
  rw [neg_sum S, neg_neg S]
  simp only [OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm, add_left_comm S]

private theorem second_factor (data : Data S) :
    S.add (twice S data.upperBase)
        (S.sub data.lowerBase data.upperBase) =
      S.add data.lowerBase data.upperBase := by
  unfold twice OrderedScalar.sub
  simp only [OrderedScalar.Axioms.add_assoc,
    OrderedScalar.Axioms.add_comm, add_left_comm S,
    OrderedScalar.Axioms.add_neg,
    OrderedScalar.Axioms.zero_add]

private theorem height_formula (data : Data S) :
    S.square (twice S data.height) =
      S.mul
        (S.sub (threeTimes S data.upperBase) data.lowerBase)
        (S.add data.lowerBase data.upperBase) := by
  calc
    S.square (twice S data.height) =
        S.sub
          (S.square (twice S data.upperBase))
          (S.square (twice S data.horizontalProjection)) :=
      doubled_height_difference S data
    _ = S.mul
        (S.sub (twice S data.upperBase)
          (twice S data.horizontalProjection))
        (S.add (twice S data.upperBase)
          (twice S data.horizontalProjection)) :=
      (difference_of_squares S
        (twice S data.upperBase)
        (twice S data.horizontalProjection)).symm
    _ = S.mul
        (S.sub (twice S data.upperBase)
          (S.sub data.lowerBase data.upperBase))
        (S.add (twice S data.upperBase)
          (S.sub data.lowerBase data.upperBase)) := by
      rw [data.projection_double]
    _ = _ := by rw [first_factor S data, second_factor S data]

/-- Problem 42.  These two equations determine the area from the given bases:
`2 Area=(a+b)h` and `(2h)^2=(3b-a)(a+b)`. -/
theorem problem42 (data : Data S) :
    data.doubleArea =
        S.mul (S.add data.lowerBase data.upperBase) data.height ∧
      S.square (twice S data.height) =
        S.mul
          (S.sub (threeTimes S data.upperBase) data.lowerBase)
          (S.add data.lowerBase data.upperBase) := by
  exact ⟨rfl, height_formula S data⟩

end Soultions.Sharygin.Page17.Problem42.Solution
