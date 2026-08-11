import Sharygin24Problem84.Configuration

namespace Soultions.Sharygin.Page24.Problem84.Solution

open Euclid
open Soultions.Sharygin.Page24.Problem84.Scalar
open Soultions.Sharygin.Page24.Problem84.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem square_root_six (data : Data S) :
    S.square data.rootSix = S.mul (S.square data.rootTwo) (S.square data.rootThree) := by
  rw [data.root_six_value]
  unfold OrderedScalar.square
  letI : Std.Associative S.mul := ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
  letI : Std.Commutative S.mul := ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
  ac_rfl

private theorem conjugate_product (data : Data S) :
    S.mul (S.sub data.rootSix data.rootTwo) (S.add data.rootSix data.rootTwo) =
      fourTimes S S.one := by
  rw [difference_of_squares S, square_root_six S data,
    data.root_two_square, data.root_three_square]
  unfold OrderedScalar.sub fourTimes threeTimes twice
  simp only [OrderedScalar.Axioms.left_distrib, right_distrib S,
    OrderedScalar.Axioms.mul_one]
  apply add_right_cancel S (x := S.add S.one S.one)
  letI : Std.Associative S.add := ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add := ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  simp only [OrderedScalar.Axioms.add_assoc, OrderedScalar.Axioms.add_comm,
    OrderedScalar.Axioms.add_neg, OrderedScalar.Axioms.zero_add]

private theorem center_factor (data : Data S) :
    twice S data.distance =
      S.mul (S.add data.rootTwo data.rootSix) data.radius90 := by
  rw [data.center_distance, data.common_chord, data.root_six_value]
  rw [right_distrib S]
  letI : Std.Associative S.mul := ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
  letI : Std.Commutative S.mul := ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
  congr 1
  ac_rfl

private theorem second_radical_factor (data : Data S) :
    S.mul data.rootTwo (S.sub data.rootSix data.rootTwo) =
      twice S (S.sub data.rootThree S.one) := by
  rw [data.root_six_value]
  unfold OrderedScalar.sub twice
  rw [OrderedScalar.Axioms.left_distrib, mul_neg S,
    ← OrderedScalar.Axioms.mul_assoc]
  change
    S.add
        (S.mul (S.square data.rootTwo) data.rootThree)
        (S.neg (S.square data.rootTwo)) =
      S.add (S.add data.rootThree (S.neg S.one))
        (S.add data.rootThree (S.neg S.one))
  rw [data.root_two_square]
  unfold twice
  rw [right_distrib S, OrderedScalar.Axioms.one_mul]
  apply add_right_cancel S (x := twice S S.one)
  unfold twice
  letI : Std.Associative S.add := ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add := ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  calc
    S.add
          (S.add (S.add data.rootThree data.rootThree)
            (S.neg (S.add S.one S.one)))
          (S.add S.one S.one) =
        S.add (S.add data.rootThree data.rootThree)
          (S.add (S.neg (S.add S.one S.one)) (S.add S.one S.one)) := by
      ac_rfl
    _ = S.add data.rootThree data.rootThree := by
      rw [neg_add S, OrderedScalar.Axioms.add_zero]
    _ = S.add
          (S.add (S.add data.rootThree (S.neg S.one))
            (S.add data.rootThree (S.neg S.one)))
          (S.add S.one S.one) := by
      calc
        S.add data.rootThree data.rootThree =
            S.add (S.add data.rootThree data.rootThree) S.zero :=
          (OrderedScalar.Axioms.add_zero _).symm
        _ = S.add (S.add data.rootThree data.rootThree)
              (S.add (S.add (S.neg S.one) S.one)
                (S.add (S.neg S.one) S.one)) := by
          rw [neg_add S, OrderedScalar.Axioms.zero_add]
        _ = S.add
              (S.add (S.add data.rootThree (S.neg S.one))
                (S.add data.rootThree (S.neg S.one)))
              (S.add S.one S.one) := by
          ac_rfl

/-- Problem 84: the radii are `a(√6-√2)/2` and `a(√3-1)`. -/
theorem problem84 (data : Data S) :
    twice S data.radius90 =
        S.mul (S.sub data.rootSix data.rootTwo) data.distance ∧
      data.radius60 =
        S.mul (S.sub data.rootThree S.one) data.distance := by
  have hscaled :
      twice S (S.mul (S.sub data.rootSix data.rootTwo) data.distance) =
        fourTimes S data.radius90 := by
    calc
      twice S (S.mul (S.sub data.rootSix data.rootTwo) data.distance) =
          S.mul (S.sub data.rootSix data.rootTwo) (twice S data.distance) := by
        unfold twice
        rw [OrderedScalar.Axioms.left_distrib]
      _ = S.mul (S.sub data.rootSix data.rootTwo)
            (S.mul (S.add data.rootTwo data.rootSix) data.radius90) := by
        rw [center_factor S data]
      _ = S.mul
            (S.mul (S.sub data.rootSix data.rootTwo)
              (S.add data.rootSix data.rootTwo)) data.radius90 := by
        rw [OrderedScalar.Axioms.add_comm data.rootTwo data.rootSix,
          OrderedScalar.Axioms.mul_assoc]
      _ = S.mul (fourTimes S S.one) data.radius90 := by
        rw [conjugate_product S data]
      _ = fourTimes S data.radius90 := by
        unfold fourTimes twice
        simp only [right_distrib S, OrderedScalar.Axioms.one_mul]
  have hfirst :
      twice S data.radius90 =
        S.mul (S.sub data.rootSix data.rootTwo) data.distance := by
    apply twice_injective S
    change fourTimes S data.radius90 =
      twice S (S.mul (S.sub data.rootSix data.rootTwo) data.distance)
    exact hscaled.symm
  refine ⟨hfirst, ?_⟩
  apply twice_injective S
  rw [data.common_chord]
  calc
    twice S (S.mul data.rootTwo data.radius90) =
        S.mul data.rootTwo (twice S data.radius90) := by
      unfold twice
      rw [OrderedScalar.Axioms.left_distrib]
    _ = S.mul data.rootTwo
          (S.mul (S.sub data.rootSix data.rootTwo) data.distance) := by
      rw [hfirst]
    _ = S.mul
          (S.mul data.rootTwo (S.sub data.rootSix data.rootTwo)) data.distance := by
      rw [OrderedScalar.Axioms.mul_assoc]
    _ = S.mul (twice S (S.sub data.rootThree S.one)) data.distance := by
      rw [second_radical_factor S data]
    _ = twice S (S.mul (S.sub data.rootThree S.one) data.distance) := by
      unfold twice
      rw [right_distrib S]

end Soultions.Sharygin.Page24.Problem84.Solution
