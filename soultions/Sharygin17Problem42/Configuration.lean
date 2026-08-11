import Sharygin17Problem42.Scalar

/-!
# Diagonal-bisector trapezoid data for Sharygin, PDF page 17, problem 42

Parallel-base angle transfer turns each diagonal-bisector condition into an isosceles triangle,
so both lateral sides equal the upper base `b`.  The remaining metric data are the altitude and
the common horizontal projection in this isosceles trapezoid.
-/

namespace Soultions.Sharygin.Page17.Problem42.Configuration

open Euclid

variable (S : OrderedScalar) [S.Axioms]

def twice (x : S.Carrier) : S.Carrier := S.add x x
def threeTimes (x : S.Carrier) : S.Carrier := S.add (S.add x x) x

structure Data where
  lowerBase : S.Carrier
  upperBase : S.Carrier
  height : S.Carrier
  horizontalProjection : S.Carrier
  projection_double :
    twice S horizontalProjection = S.sub lowerBase upperBase
  side_pythagorean :
    S.square upperBase =
      S.add (S.square horizontalProjection) (S.square height)

/-- Twice the area of the trapezoid. -/
def Data.doubleArea (data : Data S) : S.Carrier :=
  S.mul (S.add data.lowerBase data.upperBase) data.height

end Soultions.Sharygin.Page17.Problem42.Configuration
