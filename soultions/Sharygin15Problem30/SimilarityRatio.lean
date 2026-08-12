import Sharygin15Problem30.Scalar
import Sharygin15Problem30.Similarity

/-!
# Scalar consequence of the problem-local AA construction

This is kept in problem 30 because the project is deliberately retaining duplicated proofs
until recurring abstractions emerge from completed examples.
-/

namespace Soultions.Sharygin.Page15.Problem30.SimilarityRatio

open Euclid Plane
open Soultions.Sharygin.Page15.Problem30.Similarity

variable (G : Plane) [G.Axioms]

/-- Two equal angle pairs give the cross-product relation between corresponding radial sides. -/
theorem product_identity_of_two_angles
    (M : AngleMeasurement G) [M.Axioms]
    (L : LengthMeasurement G) [L.Axioms]
    {o a b c d : G.Point}
    (sense : RotationSense)
    (hleft : ¬G.Collinear o a b)
    (hright : ¬G.Collinear o c d)
    (hvertex : SameAngle G a o b c o d)
    (hbaseMeasure :
      M.measure ⟨o, a, b, sense⟩ =
        M.measure ⟨o, c, d, sense.reverse⟩)
    (hbaseOrientation :
      G.Orientation o a b =
        (G.Orientation o c d).map RotationSense.reverse) :
    L.scalar.mul (L.length o a) (L.length o d) =
      L.scalar.mul (L.length o b) (L.length o c) := by
  letI : OrderedScalar.Axioms L.scalar :=
    LengthMeasurement.Axioms.scalar_axioms
  rcases aa_equal_scale_or_fourthProportional G M sense
      hleft hright hvertex hbaseMeasure hbaseOrientation with
    hequal | hconfiguration
  · have hoa_oc : L.length o a = L.length o c :=
      (LengthMeasurement.Axioms.congruent_iff o a o c).mp hequal.1
    have hob_od : L.length o b = L.length o d :=
      (LengthMeasurement.Axioms.congruent_iff o b o d).mp hequal.2
    rw [hoa_oc, hob_od]
    exact OrderedScalar.Axioms.mul_comm _ _
  · obtain ⟨e, f, hfourth, hoe_oa, hof_ob⟩ := hconfiguration
    have hproduct :
        L.scalar.mul (L.length o e) (L.length o d) =
          L.scalar.mul (L.length o f) (L.length o c) :=
      LengthMeasurement.Axioms.fourth_proportional_mul o e f c d hfourth
    have hoe : L.length o e = L.length o a :=
      (LengthMeasurement.Axioms.congruent_iff o e o a).mp hoe_oa
    have hof : L.length o f = L.length o b :=
      (LengthMeasurement.Axioms.congruent_iff o f o b).mp hof_ob
    rwa [hoe, hof] at hproduct

end Soultions.Sharygin.Page15.Problem30.SimilarityRatio
