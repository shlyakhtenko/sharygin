import Sharygin22Problem70.Configuration

namespace Soultions.Sharygin.Page22.Problem70.Solution

open Euclid
open Soultions.Sharygin.Page22.Problem70.Scalar
open Soultions.Sharygin.Page22.Problem70.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem target_square (data : Data S) :
    S.square (S.mul data.rootTen data.side) = tenTimes S (S.square data.side) := by
  unfold OrderedScalar.square
  letI : Std.Associative S.mul := ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
  letI : Std.Commutative S.mul := ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
  calc
    S.mul (S.mul data.rootTen data.side) (S.mul data.rootTen data.side) =
      S.mul (S.square data.rootTen) (S.square data.side) := by
        unfold OrderedScalar.square
        ac_rfl
    _ = S.mul (tenTimes S S.one) (S.square data.side) := by rw [data.root_ten_square]
    _ = tenTimes S (S.square data.side) := by
      unfold tenTimes fiveTimes fourTimes twice
      simp only [right_distrib S, OrderedScalar.Axioms.one_mul]

/-- Problem 70: `4d=√10 a`. -/
theorem problem70 (data : Data S) :
    fourTimes S data.distance = S.mul data.rootTen data.side := by
  apply eq_of_sub_eq_zero S
  apply mul_right_cancel S data.geometric_root
  rw [difference_of_squares S, data.distance_square, target_square S data]
  unfold OrderedScalar.sub
  rw [OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.zero_mul]

end Soultions.Sharygin.Page22.Problem70.Solution
