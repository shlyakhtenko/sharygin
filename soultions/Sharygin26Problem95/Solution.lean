import Sharygin26Problem95.Configuration

namespace Soultions.Sharygin.Page26.Problem95.Solution

open Euclid
open Soultions.Sharygin.Page26.Problem95.Scalar
open Soultions.Sharygin.Page26.Problem95.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem ad_sub_db (data : Data S) :
    S.sub data.ad data.db = S.one := by
  have hsquares :
      S.sub (S.square data.ad) (S.square data.db) =
        S.square data.altitude := by
    apply sub_eq_of_eq_add S
    rw [data.ad_eq_bc]
    exact data.bcd_pythagorean
  apply mul_right_cancel S data.side_ab_ne_zero
  calc
    S.mul (S.sub data.ad data.db) data.sideAB =
        S.mul (S.sub data.ad data.db) (S.add data.ad data.db) := by
      rw [← data.foot_between]
    _ = S.sub (S.square data.ad) (S.square data.db) :=
      difference_of_squares S data.ad data.db
    _ = S.square data.altitude := hsquares
    _ = data.sideAB := by
      rw [data.altitude_square, data.side_ab_value]
    _ = S.mul S.one data.sideAB := (OrderedScalar.Axioms.one_mul _).symm

private theorem db_eq_one (data : Data S) : data.db = S.one := by
  have had : data.ad = S.add data.db S.one :=
    eq_add_of_sub_eq S (ad_sub_db S data)
  have htwice : twice S data.db = twice S S.one := by
    apply add_right_cancel S (z := S.one)
    calc
      S.add (twice S data.db) S.one = S.add (S.add data.db S.one) data.db := by
        unfold twice
        letI : Std.Associative S.add :=
          ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
        letI : Std.Commutative S.add :=
          ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
        ac_rfl
      _ = S.add data.ad data.db := by rw [had]
      _ = data.sideAB := data.foot_between.symm
      _ = threeTimes S S.one := data.side_ab_value
      _ = S.add (twice S S.one) S.one := rfl
  apply mul_right_cancel S data.twice_one_ne_zero
  calc
    S.mul data.db (twice S S.one) = twice S data.db := by
      unfold twice
      rw [OrderedScalar.Axioms.left_distrib, OrderedScalar.Axioms.mul_one]
    _ = twice S S.one := htwice
    _ = S.mul S.one (twice S S.one) := (OrderedScalar.Axioms.one_mul _).symm

private theorem ad_eq_two (data : Data S) : data.ad = twice S S.one := by
  calc
    data.ad = S.add data.db S.one :=
      eq_add_of_sub_eq S (ad_sub_db S data)
    _ = twice S S.one := by
      rw [db_eq_one S data]
      rfl

private theorem side_ac_square (data : Data S) :
    S.square data.sideAC = sevenTimes S S.one := by
  rw [data.acd_pythagorean, ad_eq_two S data, data.altitude_square]
  unfold OrderedScalar.square sevenTimes fourTimes threeTimes twice
  simp only [OrderedScalar.Axioms.left_distrib, OrderedScalar.Axioms.mul_one]
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  ac_rfl

/-- Problem 95: `AC = √7`. -/
theorem problem95 (data : Data S) : data.sideAC = data.rootSeven := by
  apply eq_of_sub_eq_zero S
  apply mul_right_cancel S data.positive_sum
  rw [difference_of_squares S, side_ac_square S data,
    data.root_seven_square]
  unfold OrderedScalar.sub
  rw [OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.zero_mul]

end Soultions.Sharygin.Page26.Problem95.Solution
