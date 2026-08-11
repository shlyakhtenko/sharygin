import Sharygin25Problem90.Configuration

namespace Soultions.Sharygin.Page25.Problem90.Solution

open Euclid
open Soultions.Sharygin.Page25.Problem90.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem twentyFour_add (x y : S.Carrier) :
    twentyFourTimes S (S.add x y) =
      S.add (twentyFourTimes S x) (twentyFourTimes S y) := by
  unfold twentyFourTimes threeTimes eightTimes fourTimes twice
  letI : Std.Associative S.add := ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add := ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  ac_rfl

/-- Problem 90: the pentagon has area `3a²/8`, stated as `24S=9a²`. -/
theorem problem90 (data : Data S) :
    twentyFourTimes S data.pentagonArea = nineTimes S (S.square data.side) := by
  rw [data.area_partition, twentyFour_add S, twentyFour_add S,
    data.first_triangle, data.middle_triangle, data.third_triangle]
  unfold nineTimes eightTimes fiveTimes fourTimes twice
  letI : Std.Associative S.add := ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
  letI : Std.Commutative S.add := ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
  ac_rfl

end Soultions.Sharygin.Page25.Problem90.Solution
