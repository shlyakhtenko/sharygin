import Sharygin20Problem58.Configuration

/-!
# Sharygin, PDF page 20, problem 58

The two given angles complement `B` and `A`.  Adding the two complementary
relations and comparing with the triangle angle sum leaves `C=α+β`.
-/

namespace Soultions.Sharygin.Page20.Problem58.Solution

open Euclid
open Soultions.Sharygin.Page20.Problem58.Scalar
open Soultions.Sharygin.Page20.Problem58.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem angle_c (data : Data S) :
    data.angleC = S.add data.alpha data.beta := by
  apply add_left_cancel S (x := S.add data.angleA data.angleB)
  calc
    S.add (S.add data.angleA data.angleB) data.angleC =
        data.straightAngle := by
      rw [OrderedScalar.Axioms.add_assoc]
      exact data.triangle_angle_sum
    _ = S.add data.rightAngle data.rightAngle :=
      data.two_right_angles.symm
    _ = S.add (S.add data.beta data.angleA) data.rightAngle :=
      congrArg (fun x => S.add x data.rightAngle)
        data.altitude_at_b.symm
    _ = S.add (S.add data.beta data.angleA)
        (S.add data.alpha data.angleB) :=
      congrArg (fun x => S.add (S.add data.beta data.angleA) x)
        data.altitude_at_a.symm
    _ = S.add
        (S.add data.angleA data.angleB)
        (S.add data.alpha data.beta) := by
      letI : Std.Associative S.add :=
        ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
      letI : Std.Commutative S.add :=
        ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
      ac_rfl

/-- Problem 58: `A=90°-β`, `B=90°-α`, and `C=α+β`. -/
theorem problem58 (data : Data S) :
    data.angleA = S.sub data.rightAngle data.beta ∧
      data.angleB = S.sub data.rightAngle data.alpha ∧
      data.angleC = S.add data.alpha data.beta := by
  refine ⟨?_, ?_, angle_c S data⟩
  · apply eq_sub_of_add_eq S
    calc
      S.add data.angleA data.beta = S.add data.beta data.angleA :=
        OrderedScalar.Axioms.add_comm _ _
      _ = data.rightAngle := data.altitude_at_b
  · apply eq_sub_of_add_eq S
    calc
      S.add data.angleB data.alpha = S.add data.alpha data.angleB :=
        OrderedScalar.Axioms.add_comm _ _
      _ = data.rightAngle := data.altitude_at_a

end Soultions.Sharygin.Page20.Problem58.Solution
