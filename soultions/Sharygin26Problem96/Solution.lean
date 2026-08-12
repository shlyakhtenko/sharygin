import Sharygin26Problem96.Configuration

namespace Soultions.Sharygin.Page26.Problem96.Solution

open Euclid
open Soultions.Sharygin.Page26.Problem96.Scalar
open Soultions.Sharygin.Page26.Problem96.Configuration

variable (S : OrderedScalar) [S.Axioms]

/-- Problem 96: the incircle radius of `ACD` is `(√3 - 1)R/2`. -/
theorem problem96 (data : Data S) :
    twice S data.inradius =
      S.mul (S.sub data.rootThree S.one) data.radius := by
  have htangent := data.tangent_length_decomposition
  rw [data.long_chord, data.short_chord, data.diameter] at htangent
  have hbalance :
      S.mul data.rootThree data.radius =
        S.add data.radius (twice S data.inradius) := by
    apply add_left_cancel S (x := data.radius)
    calc
      S.add data.radius (S.mul data.rootThree data.radius) =
          S.add (S.mul data.rootThree data.radius) data.radius :=
        OrderedScalar.Axioms.add_comm _ _
      _ = S.add (twice S data.radius) (twice S data.inradius) :=
        htangent
      _ = S.add data.radius
          (S.add data.radius (twice S data.inradius)) := by
        unfold twice
        exact OrderedScalar.Axioms.add_assoc _ _ _
  have hsub :
      S.sub (S.mul data.rootThree data.radius) data.radius =
        twice S data.inradius :=
    sub_eq_of_eq_add S hbalance
  calc
    twice S data.inradius =
        S.sub (S.mul data.rootThree data.radius) data.radius := hsub.symm
    _ = S.sub
          (S.mul data.rootThree data.radius)
          (S.mul S.one data.radius) := by
      rw [OrderedScalar.Axioms.one_mul]
    _ = S.mul (S.sub data.rootThree S.one) data.radius :=
      (sub_mul S data.rootThree S.one data.radius).symm

end Soultions.Sharygin.Page26.Problem96.Solution
