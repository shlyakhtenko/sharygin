import Sharygin19Problem56.Configuration

/-!
# Sharygin, PDF page 19, problem 56

On the symmetry axis, the distance `OI` is the contact-chord offset plus the
incircle radius.  Multiplying by `AO` lets the two direct geometric formulas
combine, after which the nonzero factor `AO` cancels.
-/

namespace Soultions.Sharygin.Page19.Problem56.Solution

open Euclid
open Soultions.Sharygin.Page19.Problem56.Scalar
open Soultions.Sharygin.Page19.Problem56.Configuration

variable (S : OrderedScalar) [S.Axioms]

/-- Problem 56: the incenter has distance `R` from the given circle's centre. -/
theorem problem56 (data : Data S) : data.oi = data.radius := by
  apply mul_left_cancel S data.ao_ne_zero
  calc
    S.mul data.ao data.oi =
        S.mul data.ao
          (S.add data.contactOffset data.triangleInradius) := by
      rw [data.axis_addition]
    _ = S.add
        (S.mul data.ao data.contactOffset)
        (S.mul data.ao data.triangleInradius) :=
      OrderedScalar.Axioms.left_distrib _ _ _
    _ = S.add (S.square data.radius)
        (S.mul data.radius (S.sub data.ao data.radius)) := by
      rw [data.contact_similarity, data.inradius_from_area]
    _ = S.mul data.ao data.radius := by
      unfold OrderedScalar.square OrderedScalar.sub
      rw [OrderedScalar.Axioms.left_distrib, mul_neg S]
      calc
        S.add (S.mul data.radius data.radius)
            (S.add (S.mul data.radius data.ao)
              (S.neg (S.mul data.radius data.radius))) =
          S.mul data.radius data.ao := by
            rw [← OrderedScalar.Axioms.add_assoc,
              OrderedScalar.Axioms.add_comm
                (S.mul data.radius data.radius)
                (S.mul data.radius data.ao),
              OrderedScalar.Axioms.add_assoc,
              OrderedScalar.Axioms.add_neg,
              OrderedScalar.Axioms.add_zero]
        _ = S.mul data.ao data.radius :=
          OrderedScalar.Axioms.mul_comm _ _

end Soultions.Sharygin.Page19.Problem56.Solution
