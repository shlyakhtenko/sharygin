import Sharygin22Problem76.Configuration

namespace Soultions.Sharygin.Page22.Problem76.Solution

open Euclid
open Soultions.Sharygin.Page22.Problem76.Scalar
open Soultions.Sharygin.Page22.Problem76.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem target_square (data : Data S) :
    S.square (S.mul data.rootTwentyOne data.chord) =
      twentyOneTimes S (S.square data.chord) := by
  unfold OrderedScalar.square
  letI : Std.Associative S.mul := ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
  letI : Std.Commutative S.mul := ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
  calc
    S.mul (S.mul data.rootTwentyOne data.chord)
        (S.mul data.rootTwentyOne data.chord) =
      S.mul (S.square data.rootTwentyOne) (S.square data.chord) := by
        unfold OrderedScalar.square
        ac_rfl
    _ = S.mul (twentyOneTimes S S.one) (S.square data.chord) := by
      rw [data.root_square]
    _ = twentyOneTimes S (S.square data.chord) := by
      unfold twentyOneTimes sevenTimes threeTimes twice
      simp only [right_distrib S, OrderedScalar.Axioms.one_mul]

/-- Problem 76: `9R=√21 a`. -/
theorem problem76 (data : Data S) :
    nineTimes S data.radius = S.mul data.rootTwentyOne data.chord := by
  apply eq_of_sub_eq_zero S
  apply mul_right_cancel S data.geometric_root
  rw [difference_of_squares S, data.radius_square, target_square S data]
  unfold OrderedScalar.sub
  rw [OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.zero_mul]

end Soultions.Sharygin.Page22.Problem76.Solution
