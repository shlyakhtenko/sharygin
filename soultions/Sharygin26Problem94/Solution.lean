import Sharygin26Problem94.Configuration

namespace Soultions.Sharygin.Page26.Problem94.Solution

open Euclid
open Soultions.Sharygin.Page26.Problem94.Configuration

variable (S : OrderedScalar) [S.Axioms]

private theorem right_distrib (x y z : S.Carrier) :
    S.mul (S.add x y) z = S.add (S.mul x z) (S.mul y z) := by
  rw [OrderedScalar.Axioms.mul_comm (S.add x y) z,
    OrderedScalar.Axioms.left_distrib,
    OrderedScalar.Axioms.mul_comm z x,
    OrderedScalar.Axioms.mul_comm z y]

/--
Problem 94: if the first circle has radius `r`, then the circle through `A`, `D`, and `C`
has radius `R` characterized by `cR = br` (equivalently, `R = br/c` when `c` is nonzero).
-/
theorem problem94 (data : Data S) :
    S.mul data.sideAB data.secondRadius =
      S.mul data.sideAC data.firstRadius := by
  calc
    S.mul data.sideAB data.secondRadius =
        S.mul
          (S.mul data.commonSine (twice S data.firstRadius))
          data.secondRadius := by
      rw [data.first_chord_circumdiameter]
    _ = S.mul data.commonSine
          (S.mul (twice S data.firstRadius) data.secondRadius) :=
      OrderedScalar.Axioms.mul_assoc _ _ _
    _ = S.mul data.commonSine
          (S.mul (twice S data.secondRadius) data.firstRadius) := by
      unfold twice
      rw [right_distrib S, right_distrib S]
      rw [OrderedScalar.Axioms.mul_comm data.firstRadius data.secondRadius]
    _ = S.mul
          (S.mul data.commonSine (twice S data.secondRadius))
          data.firstRadius :=
      (OrderedScalar.Axioms.mul_assoc _ _ _).symm
    _ = S.mul data.sideAC data.firstRadius := by
      rw [data.second_chord_circumdiameter]

end Soultions.Sharygin.Page26.Problem94.Solution
