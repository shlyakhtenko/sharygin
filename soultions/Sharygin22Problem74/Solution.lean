import Sharygin22Problem74.Configuration

/-!
# Sharygin, PDF page 22, problem 74

Eliminate the circumradius from the two chord formulas.
-/

namespace Soultions.Sharygin.Page22.Problem74.Solution

open Euclid
open Soultions.Sharygin.Page22.Problem74.Configuration

variable (S : OrderedScalar) [S.Axioms]

/-- Problem 74: `sin(α+β) AK = a cos((α-β)/2)`. -/
theorem problem74 (data : Data S) :
    S.mul data.sinAngleSum data.ak =
      S.mul data.sideBC data.cosHalfDifference := by
  rw [data.bisector_chord]
  calc
    S.mul data.sinAngleSum
        (S.mul (twice S data.circumradius) data.cosHalfDifference) =
      S.mul
        (S.mul (twice S data.circumradius) data.sinAngleSum)
        data.cosHalfDifference := by
      letI : Std.Associative S.mul :=
        ⟨fun a b c => OrderedScalar.Axioms.mul_assoc a b c⟩
      letI : Std.Commutative S.mul :=
        ⟨fun a b => OrderedScalar.Axioms.mul_comm a b⟩
      ac_rfl
    _ = S.mul data.sideBC data.cosHalfDifference := by
      rw [data.base_chord]

end Soultions.Sharygin.Page22.Problem74.Solution
