import Euclid

/-!
# Incenter angle data for Sharygin, PDF page 18, problem 46

The fields are precisely the two triangle angle sums and the two angle-bisector equalities.
-/

namespace Soultions.Sharygin.Page18.Problem46.Configuration

open Euclid Plane

variable {G : Plane} (M : AngleMeasurement G) [M.Axioms]

structure Data where
  angleA : M.Measure
  angleB : M.Measure
  angleC : M.Measure
  halfA : M.Measure
  halfC : M.Measure
  angleAOC : M.Measure
  triangle_sum : M.add (M.add angleA angleB) angleC = M.halfTurn
  a_bisected : M.twice halfA = angleA
  c_bisected : M.twice halfC = angleC
  incenter_triangle_sum :
    M.add (M.add halfA angleAOC) halfC = M.halfTurn

end Soultions.Sharygin.Page18.Problem46.Configuration
