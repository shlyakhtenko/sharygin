import Sharygin24Problem87.Configuration

namespace Soultions.Sharygin.Page24.Problem87.Solution

open Euclid
open Soultions.Sharygin.Page24.Problem87.Scalar
open Soultions.Sharygin.Page24.Problem87.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem altitude_square (data : Data S) :
    S.square data.altitude = twelveTimes S S.one := by
  have h := data.ab_pythagorean
  rw [data.side_ab_value, data.bisector_trisection] at h
  apply add_left_cancel S (x := S.square (twice S S.one))
  rw [← h]
  unfold OrderedScalar.square fourTimes twice twelveTimes
  simp only [OrderedScalar.nsmul, OrderedScalar.Axioms.left_distrib, right_distrib S,
    OrderedScalar.Axioms.one_mul]
  rw [OrderedScalar.Axioms.zero_add]
  letI : Std.Associative S.add := ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add := ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  ac_rfl

private theorem side_ac_square (data : Data S) :
    S.square data.sideAC = thirteenTimes S S.one := by
  rw [data.ac_pythagorean, data.bisector_trisection,
    data.median_trisection, altitude_square S data]
  have hsub : S.sub (twice S S.one) S.one = S.one := by
    apply sub_eq_of_eq_add S
    rfl
  rw [hsub]
  unfold OrderedScalar.square thirteenTimes
  rw [OrderedScalar.Axioms.mul_one]
  exact OrderedScalar.Axioms.add_comm _ _

/-- Problem 87: `AC = √13`. -/
theorem problem87 (data : Data S) : data.sideAC = data.rootThirteen := by
  apply eq_of_sub_eq_zero S
  apply mul_right_cancel S data.positive_sum
  rw [difference_of_squares S, side_ac_square S data,
    data.root_thirteen_square]
  unfold OrderedScalar.sub
  rw [OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.zero_mul]

end Soultions.Sharygin.Page24.Problem87.Solution
