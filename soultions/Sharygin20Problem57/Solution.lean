import Sharygin20Problem57.Configuration

/-!
# Sharygin, PDF page 20, problem 57

The point `X` used in the direct `60°` construction splits `AM`; its two
pieces are respectively congruent to `CM` and `BM`.
-/

namespace Soultions.Sharygin.Page20.Problem57.Solution

open Euclid
open Soultions.Sharygin.Page20.Problem57.Configuration

variable (S : OrderedScalar) [S.Axioms]

/-- Problem 57: for `M` on the arc `BC`, `AM = BM + CM`. -/
theorem problem57 (data : Data S) :
    data.am = S.add data.bm data.cm := by
  calc
    data.am = S.add data.ax data.xm := data.x_between_a_m
    _ = S.add data.cm data.bm := by
      rw [data.sas_ax_cm, data.construction_xm]
    _ = S.add data.bm data.cm := OrderedScalar.Axioms.add_comm _ _

end Soultions.Sharygin.Page20.Problem57.Solution
