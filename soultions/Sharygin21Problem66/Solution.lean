import Sharygin21Problem66.Configuration

/-!
# Sharygin, PDF page 21, problem 66

Substitute the rhombus altitude `h=a sin(α)` into `4h(2R-h)=a²`, expand, and cancel the
nonzero side.  The division-free answer is
`8R sin(α)=a(1+4 sin²(α))`.
-/

namespace Soultions.Sharygin.Page21.Problem66.Solution

open Euclid
open Soultions.Sharygin.Page21.Problem66.Scalar
open Soultions.Sharygin.Page21.Problem66.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem cancel_side_equation (data : Data S) :
    S.sub
        (S.mul (eightTimes S data.sinAlpha) data.radius)
        (S.mul (fourTimes S data.side) (S.square data.sinAlpha)) =
      data.side := by
  apply mul_left_cancel S data.side_ne_zero
  calc
    S.mul data.side
        (S.sub
          (S.mul (eightTimes S data.sinAlpha) data.radius)
          (S.mul (fourTimes S data.side) (S.square data.sinAlpha))) =
      S.mul (fourTimes S data.altitude)
        (S.sub (twice S data.radius) data.altitude) := by
      rw [data.altitude_value]
      unfold OrderedScalar.sub OrderedScalar.square eightTimes fourTimes twice
      simp only [OrderedScalar.Axioms.left_distrib, right_distrib S, mul_neg S, neg_sum S]
      letI : Std.Associative S.add :=
        ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
      letI : Std.Commutative S.add :=
        ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
      letI : Std.Associative S.mul :=
        ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
      letI : Std.Commutative S.mul :=
        ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
      ac_rfl
    _ = S.square data.side := data.tangent_chord_relation
    _ = S.mul data.side data.side := rfl

/-- Problem 66: `8R sin(α)=a(1+4 sin²(α))`. -/
theorem problem66 (data : Data S) :
    S.mul (eightTimes S data.sinAlpha) data.radius =
      S.mul data.side
        (S.add S.one (fourTimes S (S.square data.sinAlpha))) := by
  have h := add_eq_of_sub_eq S (cancel_side_equation S data)
  calc
    S.mul (eightTimes S data.sinAlpha) data.radius =
      S.add data.side
        (S.mul (fourTimes S data.side) (S.square data.sinAlpha)) := h
    _ = S.mul data.side
        (S.add S.one (fourTimes S (S.square data.sinAlpha))) := by
      unfold fourTimes twice
      simp only [OrderedScalar.Axioms.left_distrib, right_distrib S,
        OrderedScalar.Axioms.mul_one]

end Soultions.Sharygin.Page21.Problem66.Solution
