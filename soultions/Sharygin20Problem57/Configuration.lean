import Euclid

/-!
# Direct construction for Sharygin, PDF page 20, problem 57

Choose `X` on `AM` with `MX = BM`.  The inscribed angle over an equilateral
side is `60°`, so `MBX` is equilateral.  Comparing the remaining triangles
by SAS gives `AX = CM`.  These are the local outputs of that construction,
kept distinct from the requested sum.
-/

namespace Soultions.Sharygin.Page20.Problem57.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

structure Data where
  am : S.Carrier
  bm : S.Carrier
  cm : S.Carrier
  ax : S.Carrier
  xm : S.Carrier
  x_between_a_m : am = S.add ax xm
  construction_xm : xm = bm
  sas_ax_cm : ax = cm

end Soultions.Sharygin.Page20.Problem57.Configuration
