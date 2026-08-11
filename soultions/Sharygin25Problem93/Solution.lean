import Sharygin25Problem93.Configuration

namespace Soultions.Sharygin.Page25.Problem93.Solution

open Euclid
open Soultions.Sharygin.Page25.Problem93.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem right_distrib (x y z : S.Carrier) :
    S.mul (S.add x y) z = S.add (S.mul x z) (S.mul y z) := by
  rw [OrderedScalar.Axioms.mul_comm (S.add x y) z,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.mul_comm z x,
    OrderedScalar.Axioms.mul_comm z y]

/-- Problem 93: the sine of the angle between `MC` and `NK` is `7√2/10`. -/
theorem problem93 (data : Data S) :
    tenTimes S data.sine = sevenTimes S data.rootTwo := by
  have hfive :
      S.mul data.rootTwo (fiveTimes S data.rootTwo) = tenTimes S S.one := by
    have hsquare : S.mul data.rootTwo data.rootTwo = S.add S.one S.one := by
      exact data.root_two_square
    unfold tenTimes fiveTimes fourTimes twice
    simp only [OrderedScalar.Axioms.left_distrib, hsquare]
    letI : Std.Associative S.add :=
      ⟨fun a b c => OrderedScalar.Axioms.add_assoc a b c⟩
    letI : Std.Commutative S.add :=
      ⟨fun a b => OrderedScalar.Axioms.add_comm a b⟩
    ac_rfl
  calc
    tenTimes S data.sine = S.mul (tenTimes S S.one) data.sine := by
      unfold tenTimes fiveTimes fourTimes twice
      simp only [right_distrib S, OrderedScalar.Axioms.one_mul]
    _ = S.mul (S.mul data.rootTwo (fiveTimes S data.rootTwo)) data.sine := by
      rw [hfive]
    _ = S.mul data.rootTwo (S.mul (fiveTimes S data.rootTwo) data.sine) :=
      OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul data.rootTwo (sevenTimes S S.one) := by
      rw [data.direction_vector_sine]
    _ = sevenTimes S data.rootTwo := by
      unfold sevenTimes fiveTimes fourTimes twice
      simp only [OrderedScalar.Axioms.left_distrib, OrderedScalar.Axioms.mul_one]

end Soultions.Sharygin.Page25.Problem93.Solution
