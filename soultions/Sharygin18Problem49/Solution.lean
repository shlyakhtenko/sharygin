import Sharygin18Problem49.Configuration

/-!
# Sharygin, PDF page 18, problem 49

For either outer third, twice its area is twice a quarter-disc, minus the
central right triangle's doubled area `R²`, plus the doubled area `Rx` of
the triangle over the corresponding end segment `x`.  Combining this with
the quarter-disc and equal-third partitions gives `6x = (6-π)R`.
-/

namespace Soultions.Sharygin.Page18.Problem49.Solution

open Euclid
open Soultions.Sharygin.Page18.Problem49.Scalar
open Soultions.Sharygin.Page18.Problem49.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem three_add_neg_cancel (a z : S.Carrier) :
    S.add (threeTimes S (S.add a (S.neg z))) (threeTimes S z) =
      threeTimes S a := by
  letI : Std.Associative S.add :=
    ⟨fun x y w => OrderedScalar.Axioms.add_assoc x y w⟩
  letI : Std.Commutative S.add :=
    ⟨fun x y => OrderedScalar.Axioms.add_comm x y⟩
  unfold threeTimes twice
  calc
    S.add
        (S.add
          (S.add (S.add a (S.neg z)) (S.add a (S.neg z)))
          (S.add a (S.neg z)))
        (S.add (S.add z z) z) =
      S.add (S.add z (S.neg z))
        (S.add (S.add z (S.neg z))
          (S.add (S.add z (S.neg z)) (S.add (S.add a a) a))) := by
      ac_rfl
    _ = S.add (S.add a a) a := by
      simp only [OrderedScalar.Axioms.add_neg,
        OrderedScalar.Axioms.zero_add]

private theorem three_twice_split (q y : S.Carrier) :
    threeTimes S (S.add (twice S q) y) =
      S.add (fourTimes S q) (S.add (twice S q) (threeTimes S y)) := by
  letI : Std.Associative S.add :=
    ⟨fun x y z => OrderedScalar.Axioms.add_assoc x y z⟩
  letI : Std.Commutative S.add :=
    ⟨fun x y => OrderedScalar.Axioms.add_comm x y⟩
  unfold threeTimes fourTimes twice
  ac_rfl

private theorem outer_part_balance
    (q area part disk radiusSquare : S.Carrier)
    (hquarter : fourTimes S q = disk)
    (hdecomposition :
      S.add (twice S area) radiusSquare =
        S.add (twice S q) part)
    (hthird : threeTimes S (twice S area) = disk) :
    S.add (fourTimes S q) (sixTimes S part) =
      sixTimes S radiusSquare := by
  have hdoubled :
      twice S area =
        S.add (S.add (twice S q) part) (S.neg radiusSquare) :=
    eq_sub_of_add_eq S hdecomposition
  have hraw :
      fourTimes S q =
        threeTimes S
          (S.add (S.add (twice S q) part) (S.neg radiusSquare)) := by
    calc
      fourTimes S q = disk := hquarter
      _ = threeTimes S (twice S area) := hthird.symm
      _ = threeTimes S
          (S.add (S.add (twice S q) part) (S.neg radiusSquare)) := by
        rw [hdoubled]
  have hshift := congrArg
    (fun w => S.add w (threeTimes S radiusSquare)) hraw
  have hclean :
      S.add (fourTimes S q) (threeTimes S radiusSquare) =
        threeTimes S (S.add (twice S q) part) := by
    calc
      S.add (fourTimes S q) (threeTimes S radiusSquare) =
          S.add
            (threeTimes S
              (S.add (S.add (twice S q) part) (S.neg radiusSquare)))
            (threeTimes S radiusSquare) := hshift
      _ = threeTimes S (S.add (twice S q) part) :=
        three_add_neg_cancel S _ _
  have hsmall :
      S.add (twice S q) (threeTimes S part) =
        threeTimes S radiusSquare := by
    apply add_left_cancel S (x := fourTimes S q)
    calc
      S.add (fourTimes S q)
          (S.add (twice S q) (threeTimes S part)) =
        threeTimes S (S.add (twice S q) part) :=
          (three_twice_split S q part).symm
      _ = S.add (fourTimes S q) (threeTimes S radiusSquare) :=
        hclean.symm
  calc
    S.add (fourTimes S q) (sixTimes S part) =
        twice S (S.add (twice S q) (threeTimes S part)) := by
      letI : Std.Associative S.add :=
        ⟨fun x y z => OrderedScalar.Axioms.add_assoc x y z⟩
      letI : Std.Commutative S.add :=
        ⟨fun x y => OrderedScalar.Axioms.add_comm x y⟩
      unfold sixTimes fourTimes twice
      ac_rfl
    _ = twice S (threeTimes S radiusSquare) := by rw [hsmall]
    _ = sixTimes S radiusSquare := rfl

private theorem scaled_end_part
    (data : Data S) (part area : S.Carrier)
    (hdecomposition :
      S.add (twice S area) (S.square data.radius) =
        S.add (twice S data.quarterArea) (S.mul data.radius part))
    (hthird :
      threeTimes S (twice S area) =
        S.mul data.pi (S.square data.radius)) :
    sixTimes S part =
      S.mul (S.sub (sixTimes S S.one) data.pi) data.radius := by
  have hbalance := outer_part_balance S
    data.quarterArea area (S.mul data.radius part)
    (S.mul data.pi (S.square data.radius)) (S.square data.radius)
    data.quarter_partition hdecomposition hthird
  rw [data.quarter_partition] at hbalance
  have hsum :
      S.add (sixTimes S (S.mul data.radius part))
          (S.mul data.pi (S.square data.radius)) =
        sixTimes S (S.square data.radius) := by
    rw [OrderedScalar.Axioms.add_comm]
    exact hbalance
  have hisolated := eq_sub_of_add_eq S hsum
  apply mul_left_cancel S data.radius_ne_zero
  calc
    S.mul data.radius (sixTimes S part) =
        sixTimes S (S.mul data.radius part) := by
      unfold sixTimes threeTimes twice
      simp only [OrderedScalar.Axioms.left_distrib]
    _ = S.add (sixTimes S (S.square data.radius))
          (S.neg (S.mul data.pi (S.square data.radius))) := hisolated
    _ = S.mul data.radius
          (S.mul (S.sub (sixTimes S S.one) data.pi) data.radius) := by
      unfold OrderedScalar.sub sixTimes threeTimes twice OrderedScalar.square
      rw [right_distrib S, OrderedScalar.Axioms.left_distrib]
      congr 1
      · simp only [right_distrib S, OrderedScalar.Axioms.left_distrib,
          OrderedScalar.Axioms.one_mul]
      · rw [neg_mul S, mul_neg S]
        congr 1
        calc
          S.mul data.pi (S.mul data.radius data.radius) =
              S.mul (S.mul data.pi data.radius) data.radius :=
            (OrderedScalar.Axioms.mul_assoc _ _ _).symm
          _ = S.mul (S.mul data.radius data.pi) data.radius := by
            rw [OrderedScalar.Axioms.mul_comm data.pi data.radius]
          _ = S.mul data.radius (S.mul data.pi data.radius) :=
            OrderedScalar.Axioms.mul_assoc _ _ _

private theorem complement_plus_pi (pi radius : S.Carrier) :
    S.add
        (S.mul (S.sub (sixTimes S S.one) pi) radius)
        (S.mul pi radius) =
      sixTimes S radius := by
  letI : Std.Associative S.add :=
    ⟨fun x y z => OrderedScalar.Axioms.add_assoc x y z⟩
  letI : Std.Commutative S.add :=
    ⟨fun x y => OrderedScalar.Axioms.add_comm x y⟩
  unfold OrderedScalar.sub sixTimes threeTimes twice
  rw [right_distrib S, neg_mul S]
  calc
    S.add
        (S.add
          (S.mul
            (S.add (S.add (S.add S.one S.one) S.one)
              (S.add (S.add S.one S.one) S.one)) radius)
          (S.neg (S.mul pi radius)))
        (S.mul pi radius) =
      S.mul
        (S.add (S.add (S.add S.one S.one) S.one)
          (S.add (S.add S.one S.one) S.one)) radius := by
      rw [OrderedScalar.Axioms.add_assoc,
        neg_add S,
        OrderedScalar.Axioms.add_zero]
    _ = S.add
        (S.add (S.add radius radius) radius)
        (S.add (S.add radius radius) radius) := by
      simp only [right_distrib S, OrderedScalar.Axioms.one_mul]

/-- The two outer pieces of the diameter have the same required scale. -/
theorem outer_parts (data : Data S) :
    sixTimes S data.leftPart =
        S.mul (S.sub (sixTimes S S.one) data.pi) data.radius ∧
      sixTimes S data.rightPart =
        S.mul (S.sub (sixTimes S S.one) data.pi) data.radius := by
  exact ⟨
    scaled_end_part S data data.leftPart data.leftArea
      data.left_decomposition data.left_is_third,
    scaled_end_part S data data.rightPart data.rightArea
      data.right_decomposition data.right_is_third⟩

/--
Problem 49: the diameter is divided in the ratio
`(6-π) : 2π : (6-π)`, expressed without division.
-/
theorem problem49 (data : Data S) :
    sixTimes S data.leftPart =
        S.mul (S.sub (sixTimes S S.one) data.pi) data.radius ∧
      threeTimes S data.middlePart = S.mul data.pi data.radius ∧
      sixTimes S data.rightPart =
        S.mul (S.sub (sixTimes S S.one) data.pi) data.radius := by
  obtain ⟨hleft, hright⟩ := outer_parts S data
  refine ⟨hleft, ?_, hright⟩
  have hpartition := congrArg (sixTimes S) data.diameter_partition
  have hpartition' :
      S.add (sixTimes S data.leftPart)
          (S.add (sixTimes S data.middlePart)
            (sixTimes S data.rightPart)) =
        twice S (sixTimes S data.radius) := by
    letI : Std.Associative S.add :=
      ⟨fun x y z => OrderedScalar.Axioms.add_assoc x y z⟩
    letI : Std.Commutative S.add :=
      ⟨fun x y => OrderedScalar.Axioms.add_comm x y⟩
    calc
      S.add (sixTimes S data.leftPart)
          (S.add (sixTimes S data.middlePart)
            (sixTimes S data.rightPart)) =
        sixTimes S
          (S.add data.leftPart
            (S.add data.middlePart data.rightPart)) := by
          unfold sixTimes threeTimes twice
          ac_rfl
      _ = sixTimes S (twice S data.radius) := hpartition
      _ = twice S (sixTimes S data.radius) := by
        unfold sixTimes threeTimes twice
        ac_rfl
  let complement :=
    S.mul (S.sub (sixTimes S S.one) data.pi) data.radius
  let piRadius := S.mul data.pi data.radius
  have hcomplement : S.add complement piRadius = sixTimes S data.radius :=
    complement_plus_pi S data.pi data.radius
  have hmiddle_scaled :
      sixTimes S data.middlePart = twice S piRadius := by
    apply add_right_cancel S (z := complement)
    apply add_left_cancel S (x := complement)
    calc
      S.add complement
          (S.add (sixTimes S data.middlePart) complement) =
        S.add (sixTimes S data.leftPart)
          (S.add (sixTimes S data.middlePart)
            (sixTimes S data.rightPart)) := by
          rw [hleft, hright]
      _ = twice S (sixTimes S data.radius) := hpartition'
      _ = twice S (S.add complement piRadius) := by rw [hcomplement]
      _ = S.add complement (S.add (twice S piRadius) complement) := by
        letI : Std.Associative S.add :=
          ⟨fun x y z => OrderedScalar.Axioms.add_assoc x y z⟩
        letI : Std.Commutative S.add :=
          ⟨fun x y => OrderedScalar.Axioms.add_comm x y⟩
        unfold twice
        ac_rfl
  apply mul_left_cancel S (x := twice S S.one)
    (by
      intro htwo
      change S.add S.one S.one = S.zero at htwo
      have hone_le_zero : S.le S.one S.zero := by
        have h := OrderedScalar.Axioms.add_le_add_right
          S.zero S.one S.one OrderedScalar.Axioms.zero_le_one
        rw [OrderedScalar.Axioms.zero_add, htwo] at h
        exact h
      have hzero_one := OrderedScalar.Axioms.le_antisymm
        S.zero S.one OrderedScalar.Axioms.zero_le_one hone_le_zero
      exact OrderedScalar.Axioms.zero_ne_one hzero_one)
  calc
    S.mul (twice S S.one) (threeTimes S data.middlePart) =
        sixTimes S data.middlePart := by
      unfold sixTimes twice
      rw [right_distrib S, OrderedScalar.Axioms.one_mul]
    _ = twice S piRadius := hmiddle_scaled
    _ = S.mul (twice S S.one) piRadius := by
      unfold twice
      rw [right_distrib S, OrderedScalar.Axioms.one_mul]

end Soultions.Sharygin.Page18.Problem49.Solution
