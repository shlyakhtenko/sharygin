import Euclid

/-!
# Configuration for Sharygin, PDF pages 74--75, problem 32

The proof uses a coordinate on the transversal through the centroid.  The
three direction coefficients `a`, `b`, and `c` are the rates at which its
three barycentric coordinates change.  Since barycentric coordinates sum to
one, `c = a + b`.  Reaching the three sidelines gives the three displayed
intercept equations.
-/

namespace Soultions.Sharygin.Page74.Problem32.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

structure Data where
  a : S.Carrier
  b : S.Carrier
  c : S.Carrier
  centroidCoordinate : S.Carrier
  distMK : S.Carrier
  distML : S.Carrier
  distMP : S.Carrier
  directionClosure : c = S.add a b
  reachesAB :
    S.mul distMK c = centroidCoordinate
  reachesAC :
    S.mul distML b = centroidCoordinate
  reachesBC :
    S.mul distMP a = centroidCoordinate
  c_ne_zero : c ≠ S.zero

/--
The division-free form of
`1 / MK = 1 / ML + 1 / MP`.
-/
def Conclusion (d : Data S) : Prop :=
  S.mul d.distML d.distMP =
    S.add
      (S.mul d.distMK d.distMP)
      (S.mul d.distMK d.distML)

end Soultions.Sharygin.Page74.Problem32.Configuration
