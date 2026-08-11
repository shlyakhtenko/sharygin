import Sharygin19Problem53.Scalar

/-!
# Configuration for Sharygin, PDF page 19, problem 53

The two right angles make `DB` and `DC` diameters of the two circumcircles.
Their centres are therefore the corresponding midpoints, and the segment
joining them is a midline of triangle `DBC`.
-/

namespace Soultions.Sharygin.Page19.Problem53.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def fourTimes (x : S.Carrier) := twice S (twice S x)

structure Data where
  db : S.Carrier
  dc : S.Carrier
  bc : S.Carrier
  centerDistance : S.Carrier
  right_triangle_pythagoras :
    S.add (S.square db) (S.square bc) = S.square dc
  midpoint_segment : twice S centerDistance = bc

end Soultions.Sharygin.Page19.Problem53.Configuration
