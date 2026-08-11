import Sharygin24Problem86.Configuration

namespace Soultions.Sharygin.Page24.Problem86.Solution

open Euclid
open Soultions.Sharygin.Page24.Problem86.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem neg_add (x : S.Carrier) : S.add (S.neg x) x = S.zero := by
  rw [OrderedScalar.Axioms.add_comm]
  exact OrderedScalar.Axioms.add_neg x

private theorem add_left_cancel {x y z : S.Carrier}
    (h : S.add x y = S.add x z) : y = z := by
  have h' := congrArg (fun w => S.add (S.neg x) w) h
  calc
    y = S.add S.zero y := (OrderedScalar.Axioms.zero_add y).symm
    _ = S.add (S.add (S.neg x) x) y := by rw [neg_add S]
    _ = S.add (S.neg x) (S.add x y) := OrderedScalar.Axioms.add_assoc _ _ _
    _ = S.add (S.neg x) (S.add x z) := h'
    _ = S.add (S.add (S.neg x) x) z := (OrderedScalar.Axioms.add_assoc _ _ _).symm
    _ = S.add S.zero z := by rw [neg_add S]
    _ = z := OrderedScalar.Axioms.zero_add z

private theorem sub_eq_of_eq_add {d r x : S.Carrier} (h : d = S.add r x) :
    S.sub d r = x := by
  change S.add d (S.neg r) = x
  rw [h, OrderedScalar.Axioms.add_comm r x,
    OrderedScalar.Axioms.add_assoc, OrderedScalar.Axioms.add_neg,
    OrderedScalar.Axioms.add_zero]

private theorem right_distrib (x y z : S.Carrier) :
    S.mul (S.add x y) z = S.add (S.mul x z) (S.mul y z) := by
  rw [OrderedScalar.Axioms.mul_comm (S.add x y) z,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.mul_comm z x,
    OrderedScalar.Axioms.mul_comm z y]

private theorem mul_zero (x : S.Carrier) : S.mul x S.zero = S.zero := by
  rw [OrderedScalar.Axioms.mul_comm]
  exact OrderedScalar.Axioms.zero_mul x

private theorem neg_unique {x y : S.Carrier} (h : S.add x y = S.zero) : y = S.neg x := by
  apply add_left_cancel S (x := x)
  rw [h]
  exact (OrderedScalar.Axioms.add_neg x).symm

private theorem mul_neg (x y : S.Carrier) : S.mul x (S.neg y) = S.neg (S.mul x y) := by
  apply neg_unique S
  calc
    S.add (S.mul x y) (S.mul x (S.neg y)) = S.mul x (S.add y (S.neg y)) :=
      (OrderedScalar.Axioms.left_distrib _ _ _).symm
    _ = S.mul x S.zero := by rw [OrderedScalar.Axioms.add_neg]
    _ = S.zero := mul_zero S x

private theorem neg_mul (x y : S.Carrier) : S.mul (S.neg x) y = S.neg (S.mul x y) := by
  rw [OrderedScalar.Axioms.mul_comm (S.neg x) y, mul_neg S,
    OrderedScalar.Axioms.mul_comm y x]

private theorem outside_value (data : Data S) :
    twice S data.outside =
      S.mul (S.sub (threeTimes S S.one) data.rootSeven) data.radius := by
  have hpartition :
      fourTimes S data.radius =
        S.add data.radius
          (S.add (S.mul data.rootSeven data.radius) (twice S data.outside)) := by
    calc
      fourTimes S data.radius = twice S data.segmentLength := by
        rw [data.segment_value]
        rfl
      _ = S.add (twice S data.insideSmall)
            (S.add (twice S data.insideLarge) (twice S data.outside)) := by
        rw [data.segment_partition]
        unfold twice
        letI : Std.Associative S.add :=
          ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
        letI : Std.Commutative S.add :=
          ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
        ac_rfl
      _ = S.add data.radius
            (S.add (S.mul data.rootSeven data.radius) (twice S data.outside)) := by
        rw [data.small_intersection, data.large_intersection]
  have hpartition' :
      fourTimes S data.radius =
        S.add (S.add data.radius (S.mul data.rootSeven data.radius))
          (twice S data.outside) := by
    rw [hpartition]
    exact (OrderedScalar.Axioms.add_assoc _ _ _).symm
  apply add_left_cancel S
    (x := S.add data.radius (S.mul data.rootSeven data.radius))
  rw [← hpartition']
  unfold OrderedScalar.sub threeTimes fourTimes twice
  rw [right_distrib S, neg_mul S]
  simp only [right_distrib S, OrderedScalar.Axioms.one_mul]
  letI : Std.Associative S.add :=
    ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add :=
    ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  calc
    S.add (S.add data.radius data.radius) (S.add data.radius data.radius) =
        S.add
          (S.add (S.add data.radius data.radius) (S.add data.radius data.radius))
          (S.add (S.mul data.rootSeven data.radius)
            (S.neg (S.mul data.rootSeven data.radius))) := by
      rw [OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.add_zero]
    _ = S.add (S.add data.radius (S.mul data.rootSeven data.radius))
          (S.add (S.add (S.add data.radius data.radius) data.radius)
            (S.neg (S.mul data.rootSeven data.radius))) := by
      ac_rfl

/-- Problem 86: the fraction outside both circles is `(3-√7)/4`. -/
theorem problem86 (data : Data S) :
    fourTimes S data.outside =
      S.mul (S.sub (threeTimes S S.one) data.rootSeven) data.segmentLength := by
  rw [data.segment_value]
  unfold fourTimes
  rw [outside_value S data]
  unfold twice
  rw [OrderedScalar.Axioms.left_distrib]

end Soultions.Sharygin.Page24.Problem86.Solution
