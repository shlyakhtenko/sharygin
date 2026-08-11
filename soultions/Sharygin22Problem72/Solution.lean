import Sharygin22Problem72.Configuration

/-!
# Sharygin, PDF page 22, problem 72

Multiplying `4[BMH]=a·xH` by `a²+b²` and substituting the projection equation gives
`4(a²+b²)[BMH]=a³b`.
-/

namespace Soultions.Sharygin.Page22.Problem72.Solution

open Euclid
open Soultions.Sharygin.Page22.Problem72.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem right_distrib (x y z : S.Carrier) :
    S.mul (S.add x y) z = S.add (S.mul x z) (S.mul y z) := by
  rw [OrderedScalar.Axioms.mul_comm (S.add x y) z,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.mul_comm z x, OrderedScalar.Axioms.mul_comm z y]

private theorem four_product (x y : S.Carrier) :
    S.mul (fourTimes S x) y = S.mul x (fourTimes S y) := by
  unfold fourTimes twice
  simp only [right_distrib S, OrderedScalar.Axioms.left_distrib]

/-- Problem 72: `4(a²+b²)[BMH]=a³b`. -/
theorem problem72 (data : Data S) :
    S.mul
        (fourTimes S
          (S.add (S.square data.legCB) (S.square data.legCA)))
        data.bmhArea =
      S.mul
        (S.mul (S.square data.legCB) data.legCB)
        data.legCA := by
  letI : Std.Associative S.mul :=
    ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
  letI : Std.Commutative S.mul :=
    ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
  rw [← data.square_sum]
  calc
    S.mul (fourTimes S data.legSquareSum) data.bmhArea =
      S.mul data.legSquareSum (fourTimes S data.bmhArea) :=
        four_product S data.legSquareSum data.bmhArea
    _ = S.mul data.legSquareSum
        (S.mul data.legCB data.altitudeFootX) := by
      rw [data.area_base_height]
    _ = S.mul data.legCB
        (S.mul data.legSquareSum data.altitudeFootX) := by
      ac_rfl
    _ = S.mul data.legCB
        (S.mul (S.square data.legCB) data.legCA) := by
      rw [data.projection_x]
    _ = S.mul
        (S.mul (S.square data.legCB) data.legCB)
        data.legCA := by
      ac_rfl

end Soultions.Sharygin.Page22.Problem72.Solution
