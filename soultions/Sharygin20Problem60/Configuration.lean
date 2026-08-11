import Sharygin20Problem60.Scalar

/-!
# Coordinate data for Sharygin, PDF page 20, problem 60

After multiplying coordinates by two, a top vertex of the smaller square
has offsets `x` and `a+2x` from the circumcircle centre.  The original
square gives the squared diameter relation on the right.
-/

namespace Soultions.Sharygin.Page20.Problem60.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) := S.add x x
def fourTimes (x : S.Carrier) := twice S (twice S x)
def fiveTimes (x : S.Carrier) := S.add (fourTimes S x) x

structure Data where
  originalSide : S.Carrier
  smallSide : S.Carrier
  positive_root : S.add smallSide originalSide ≠ S.zero
  top_vertex_on_circle :
    S.add (S.square smallSide)
        (S.square (S.add originalSide (twice S smallSide))) =
      twice S (S.square originalSide)

end Soultions.Sharygin.Page20.Problem60.Configuration
