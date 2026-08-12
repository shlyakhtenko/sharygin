import Sharygin26Problem97.Configuration

namespace Soultions.Sharygin.Page26.Problem97.Solution

open Euclid
open Soultions.Sharygin.Page26.Problem97.Scalar
open Soultions.Sharygin.Page26.Problem97.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem two_square :
    S.square (twice S S.one) = fourTimes S S.one := by
  unfold OrderedScalar.square fourTimes twice
  simp only [OrderedScalar.Axioms.left_distrib, OrderedScalar.Axioms.mul_one]

private theorem secant_eq_four (data : Data S) :
    data.secantCE = fourTimes S S.one := by
  calc
    data.secantCE = S.mul S.one data.secantCE :=
      (OrderedScalar.Axioms.one_mul _).symm
    _ = S.mul data.sideBC data.secantCE := by rw [data.side_bc_value]
    _ = S.square data.tangentCK := data.tangent_secant_power.symm
    _ = S.square (twice S S.one) := by rw [data.tangent_value]
    _ = fourTimes S S.one := two_square S

private theorem segment_be_eq_three (data : Data S) :
    data.segmentBE = threeTimes S S.one := by
  apply add_left_cancel S (x := S.one)
  calc
    S.add S.one data.segmentBE = S.add data.sideBC data.segmentBE := by
      rw [data.side_bc_value]
    _ = data.secantCE := data.secant_additive.symm
    _ = fourTimes S S.one := secant_eq_four S data
    _ = S.add S.one (threeTimes S S.one) := by
      unfold fourTimes threeTimes twice
      letI : Std.Associative S.add :=
        ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
      letI : Std.Commutative S.add :=
        ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
      ac_rfl

private theorem diameter_square (data : Data S) :
    S.square data.diameterAE = tenTimes S S.one := by
  rw [data.diameter_pythagorean, data.side_ab_value,
    segment_be_eq_three S data]
  unfold OrderedScalar.square tenTimes nineTimes fourTimes threeTimes twice
  simp only [OrderedScalar.Axioms.left_distrib, OrderedScalar.Axioms.mul_one]
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  ac_rfl

/-- Problem 97: the diameter of the circle is `√10`. -/
theorem problem97 (data : Data S) : data.diameterAE = data.rootTen := by
  apply eq_of_sub_eq_zero S
  apply mul_right_cancel S data.positive_sum
  rw [difference_of_squares S, diameter_square S data,
    data.root_ten_square]
  unfold OrderedScalar.sub
  rw [OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.zero_mul]

end Soultions.Sharygin.Page26.Problem97.Solution
